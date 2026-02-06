#define _CRT_SECURE_NO_WARNINGS
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <cstring>
#include <array>
#include <vector>
#include <optional>
#include <memory>
#include <concepts>
#include <type_traits>
#include <iostream>
#include <utility>

#if defined(VALIDATE) && defined(NDEBUG)
#error "VALIDATE is useless if asserts are turned off by NDEBUG"
#endif

#if defined(VALIDATE) || defined(TESTGEN)
#include <set>
#endif

#ifdef LOGGING
#define LOG(fmt_, ...) \
    (fprintf(stderr, "[L] " fmt_ "\n" __VA_OPT__(,) __VA_ARGS__))
#else
#define LOG(...)
#endif

#ifndef TESTGEN

template <class T>
concept CBTreeKeyComparable =
    std::totally_ordered<T> &&
    std::strict_weak_order<std::less<>, T, T>;

#define BTREE_REQ(T_, TRef_, t_t_)             \
    (                                          \
        std::is_trivially_copyable_v<T_> &&    \
        CBTreeKeyComparable<T_> &&             \
        std::is_trivially_copyable_v<TRef_> && \
        (t_t_) >= 2                            \
    )

#define BTREE_TEMPLATE(T_, TRef_, t_t_)           \
    template <class T_, class TRef_, size_t t_t_> \
    requires BTREE_REQ(T_, TRef_, t_t_)

BTREE_TEMPLATE(T, TRef, t_t)
struct BTreeTraits {
    using elem_t = T;
    using ref_t = TRef;
    static constexpr size_t c_t = t_t;
    static constexpr size_t c_min_sz = t_t - 1;
    static constexpr size_t c_max_sz = 2 * t_t - 1;
};

template <class TPage>
struct BTreePageTraits
    : BTreeTraits<
        typename TPage::elem_t,
        typename TPage::ref_t,
        TPage::c_t>
{};

BTREE_TEMPLATE(T, TRef, t_t)
struct BTreeNodeData {
    T keys[BTreeTraits<T, TRef, t_t>::c_max_sz]{};
    TRef children[BTreeTraits<T, TRef, t_t>::c_max_sz + 1]{};
    TRef self_ref;
    uint32_t size : 31 = 0;
    uint32_t is_leaf : 1 = false;
};

#ifdef VALIDATE
template <class TPage>
class BTreeValidator;
#endif

template <class TPage>
class BTree {
    TPage m_root{};
    size_t m_size = 0;
    typename TPage::lctx_t m_lctx;

#ifndef NDEBUG
    struct {
        size_t ops = 0;
        size_t size = 0;
        size_t height = 0;
        size_t max_size = 0;
        size_t max_height = 0;
        size_t inserts = 0;
        size_t deletes = 0;
        size_t searches = 0;
        size_t splits = 0;
        size_t merges = 0;
        size_t root_pushes = 0;
        size_t root_pops = 0;
        size_t rotations = 0;
        size_t page_allocations = 0;
        size_t page_frees = 0;
        size_t page_reads = 0;
        size_t page_writes = 0;
    } mutable m_stats{};
    char const *m_tag = "";
#endif

    using lctx_t = typename TPage::lctx_t;
    using elem_t = BTreePageTraits<TPage>::elem_t;
    using ref_t = BTreePageTraits<TPage>::ref_t;
    static constexpr size_t c_t = BTreePageTraits<TPage>::c_t;
    static constexpr size_t c_min_sz = BTreePageTraits<TPage>::c_min_sz;
    static constexpr size_t c_max_sz = BTreePageTraits<TPage>::c_max_sz;

public:
#ifdef VALIDATE
    friend class BTreeValidator<TPage>;
    using page_t = TPage;
#endif

    explicit BTree(lctx_t &&lctx) : m_lctx{std::move(lctx)} { Init(); }
#ifndef NDEBUG
    BTree(lctx_t &&lctx, char const *tag) : m_lctx{std::move(lctx)}, m_tag{tag}
        { Init(); }
#endif

    BTree(BTree &&) = default;
    BTree &operator=(BTree &&) = default;
    BTree(BTree const &) = delete;
    BTree &operator=(BTree const &) = delete;
    ~BTree() {
        if (TPage::IsValid(m_root))
            WritePageBack(m_root);
        TPage::Close(m_lctx);
    }

    bool Search(elem_t const &k) const {
        auto *data = &m_root.Data();
        TPage loaded_page{};
        for (;;) {
            auto &node = *data;
            size_t chid = 0;
            while (chid < node.size && k > node.keys[chid]) {
                ++chid;
            }
            if (chid < node.size && node.keys[chid] == k) {
                return true;
            } else if (node.is_leaf) {
                return false;
            } else {
                loaded_page = ReadPageIn(node.children[chid]);
                data = &loaded_page.Data();
            }
        }
    }

    void Insert(elem_t const &k) {
        if (m_root.Data().size == c_max_sz) {
            TPage new_root = AllocatePage();
            new_root.Data().size = 0;
            new_root.Data().is_leaf = false;
            new_root.Data().children[0] = m_root.Data().self_ref;
            SplitChild(new_root, m_root, 0);
            m_root = std::move(new_root);
            ReportRootPush();
        }
        auto *cur_page = &m_root;
        auto *data = &cur_page->Data();
        TPage loaded_page{};
        for (;;) {
            auto &page = *cur_page;
            auto &node = *data;
            ssize_t chid = node.size - 1;
            if (node.is_leaf) {
                while (chid >= 0 && k < node.keys[chid]) {
                    node.keys[chid + 1] = node.keys[chid];
                    --chid;
                }
                node.keys[chid + 1] = k;
                ++node.size;
                WritePageBack(page);
                ReportInsert();
                break;
            } else {
                while (chid >= 0 && k < node.keys[chid]) {
                    --chid;
                }
                ++chid;
                TPage child_page = ReadPageIn(node.children[chid]);
                if (child_page.Data().size == c_max_sz) {
                    TPage next = SplitChild(page, child_page, chid);
                    if (k > node.keys[chid]) {
                        ++chid;
                        child_page = std::move(next);
                    }
                }
                loaded_page = std::move(child_page);
                cur_page = &loaded_page;
                data = &loaded_page.Data();
            }
        }
        ++m_size;
    }

    bool Delete(elem_t const &k) {
        if (m_size == 0) {
            return false;
        } else if (m_root.Data().size == 0) {
            TPage new_root = ReadPageIn(m_root.Data().children[0]);
            FreePage(std::move(m_root));
            m_root = std::move(new_root);
            ReportRootPop();
        }
        enum search_method_t {
            e_sm_search,
            e_sm_bottommost,
            e_sm_topmost,
            e_sm_middle
        } sm = e_sm_search;
        struct search_res_t {
            uint32_t index : 31;
            uint32_t found : 1;
        };
        auto search = [&k](auto const &node, search_method_t cur_sm) {
            switch (cur_sm) {
            case e_sm_search: {
                uint32_t chid = 0;
                while (chid < node.size && k > node.keys[chid]) {
                    ++chid;
                }
                return search_res_t{
                    .index = chid,
                    .found = chid < node.size && k == node.keys[chid]
                };
            }
            case e_sm_bottommost: {
                return search_res_t{.index = 0, .found = node.is_leaf};
            }
            case e_sm_topmost: {
                return node.is_leaf
                    ? search_res_t{.index = node.size - 1u, .found = true }
                    : search_res_t{.index = node.size,      .found = false};
            }
            case e_sm_middle: {
                return search_res_t{.index = c_min_sz, .found = true};
            }
            default: {
                assert(0);
                return search_res_t{};
            }
            }
        };
        auto *cur_page = &m_root;
        decltype(cur_page) found_page = nullptr;
        auto *data = &cur_page->Data();
        TPage loaded_page{};
        TPage loaded_found_page{};
        elem_t *replacement_slot = nullptr;
        for (;;) {
            auto &page = *cur_page;
            auto &node = *data;
            search_res_t sr = search(node, sm);
            if (node.is_leaf) {
                if (!sr.found && !replacement_slot) {
                    return false;
                }
                if (replacement_slot) {
                    *replacement_slot = node.keys[sr.index];
                    assert(found_page);
                    WritePageBack(*found_page);
                }
                for (size_t i = sr.index + 1; i < node.size; ++i) {
                    node.keys[i - 1] = node.keys[i];
                }
                --node.size;
                --m_size;
                WritePageBack(page);
                ReportDelete();
                return true;
            } else {
                if (sr.found) {
                    TPage lpage = ReadPageIn(node.children[sr.index]);
                    if (lpage.Data().size > c_min_sz) {
                        replacement_slot = &node.keys[sr.index];
                        if (cur_page == &loaded_page) {
                            loaded_found_page = std::move(loaded_page);
                            found_page = &loaded_found_page;
                        } else {
                            found_page = cur_page;
                        }
                        loaded_page = std::move(lpage);
                        sm = e_sm_topmost;
                    } else {
                        TPage rpage = ReadPageIn(node.children[sr.index + 1]);
                        if (rpage.Data().size > c_min_sz) {
                            replacement_slot = &node.keys[sr.index];
                            if (cur_page == &loaded_page) {
                                loaded_found_page = std::move(loaded_page);
                                found_page = &loaded_found_page;
                            } else {
                                found_page = cur_page;
                            }
                            loaded_page = std::move(rpage);
                            sm = e_sm_bottommost;
                        } else {
                            loaded_page = MergeChildren(
                                page, lpage, rpage, sr.index);
                            sm = e_sm_middle;
                        }
                    }
                } else {
                    TPage cpage = ReadPageIn(node.children[sr.index]);
                    if (cpage.Data().size > c_min_sz) {
                        loaded_page = std::move(cpage);
                    } else {
                        TPage lpage{};
                        TPage rpage{};
                        if (sr.index > 0) {
                            lpage = ReadPageIn(node.children[sr.index - 1]);
                            if (lpage.Data().size > c_min_sz) {
                                for (
                                    size_t i = cpage.Data().size;
                                    i > 0; --i)
                                {
                                    cpage.Data().keys[i] =
                                        cpage.Data().keys[i - 1];
                                }
                                for (
                                    size_t i = cpage.Data().size + 1;
                                    i > 0; --i)
                                {
                                    cpage.Data().children[i] =
                                        cpage.Data().children[i - 1];
                                }
                                cpage.Data().keys[0] =
                                    node.keys[sr.index - 1];
                                cpage.Data().children[0] =
                                    lpage.Data().children[lpage.Data().size];
                                node.keys[sr.index - 1] =
                                    lpage.Data().keys[lpage.Data().size - 1];
                                --lpage.Data().size;
                                ++cpage.Data().size;
                                WritePageBack(page);
                                WritePageBack(cpage);
                                WritePageBack(lpage);
                                loaded_page = std::move(cpage);
                                ReportRotation();
                                goto descend;
                            }
                        }
                        if (sr.index < node.size) {
                            lpage = {};
                            rpage = ReadPageIn(node.children[sr.index + 1]);
                            if (rpage.Data().size > c_min_sz) {
                                cpage.Data().keys[cpage.Data().size] =
                                    node.keys[sr.index];
                                cpage.Data().children[cpage.Data().size + 1] =
                                    rpage.Data().children[0];
                                node.keys[sr.index] =
                                    rpage.Data().keys[0];
                                for (
                                    size_t i = 0;
                                    i < rpage.Data().size; ++i)
                                {
                                    rpage.Data().keys[i] =
                                        rpage.Data().keys[i + 1];
                                }
                                for (
                                    size_t i = 0;
                                    i < rpage.Data().size + 1; ++i)
                                {
                                    rpage.Data().children[i] =
                                        rpage.Data().children[i + 1];
                                }
                                --rpage.Data().size;
                                ++cpage.Data().size;
                                WritePageBack(page);
                                WritePageBack(cpage);
                                WritePageBack(rpage);
                                loaded_page = std::move(cpage);
                                ReportRotation();
                                goto descend;
                            }
                        }
                        if (lpage) {
                            loaded_page = MergeChildren(
                                page, lpage, cpage, sr.index - 1);
                        } else if (rpage) {
                            loaded_page = MergeChildren(
                                page, cpage, rpage, sr.index);
                        }
                    }
                }
            descend:
                cur_page = &loaded_page;
                data = &loaded_page.Data();
            }
        }
    }

    size_t Size() const { return m_size; }
    size_t Empty() const { return m_size == 0; }

#ifndef NDEBUG
    void DumpStats() const {
        fprintf(stderr, "=== BTree \"%s\" perf dump ===\n", m_tag);
        fprintf(stderr, "  Total:       %-7lu\n", m_stats.ops);
        fprintf(stderr, "  Inserts:     %-7lu (%-5.2f%% of ops)\n",
            m_stats.inserts,
            (float(m_stats.inserts) / m_stats.ops) * 100.f);
        fprintf(stderr, "  Deletes:     %-7lu (%-5.2f%% of ops)\n",
            m_stats.deletes,
            (float(m_stats.deletes) / m_stats.ops) * 100.f);
        fprintf(stderr, "  Max size:    %-7lu (%-5.2f%% of ops)\n",
            m_stats.max_size,
            (float(m_stats.max_size) / m_stats.ops) * 100.f);
        fprintf(stderr, "  Max height:  %-7lu (%-5.2f%% of ops)\n",
            m_stats.max_height,
            (float(m_stats.max_height) / m_stats.ops) * 100.f);
        fprintf(stderr, "  Root pushes: %-7lu (%-5.2f%% of inserts)\n",
            m_stats.root_pushes,
            (float(m_stats.root_pushes) / m_stats.inserts) * 100.f);
        fprintf(stderr, "  Root pops:   %-7lu (%-5.2f%% of deletes)\n",
            m_stats.root_pops,
            (float(m_stats.root_pops) / m_stats.deletes) * 100.f);
        fprintf(stderr, "  Splits:      %-7lu\n", m_stats.splits);
        fprintf(stderr, "  Merges:      %-7lu\n", m_stats.merges);
        fprintf(stderr, "  Rotations:   %-7lu\n", m_stats.rotations);
        fprintf(stderr, "  Page allocs: %-7lu\n", m_stats.page_allocations);
        fprintf(stderr, "  Page frees:  %-7lu\n", m_stats.page_frees);
        fprintf(stderr, "  Page reads:  %-7lu\n", m_stats.page_reads);
        fprintf(stderr, "  Page writes: %-7lu\n", m_stats.page_writes);
        fprintf(stderr, "=== end dump ===\n");
    }
#else
    void DumpStats() const {}
#endif

private:
    void Init() {
        m_root = AllocatePage();
        m_root.Data().size = 0;
        m_root.Data().is_leaf = true;
        WritePageBack(m_root);
    }

    TPage SplitChild(TPage &parent, TPage &child, size_t chid) {
        TPage r = AllocatePage();
        auto &rnode = r.Data();
        auto &cnode = child.Data();
        auto &pnode = parent.Data();
        rnode.is_leaf = cnode.is_leaf;
        rnode.size = c_t - 1;
        for (size_t i = 0; i < rnode.size; ++i) {
            rnode.keys[i] = cnode.keys[i + c_t];
        }
        if (!rnode.is_leaf) {
            for (size_t i = 0; i <= rnode.size; ++i) {
                rnode.children[i] = cnode.children[i + c_t];
            }
        }
        for (size_t i = pnode.size + 1; i > chid + 1; --i) {
            pnode.children[i] = pnode.children[i - 1];
        }
        pnode.children[chid + 1] = rnode.self_ref;
        for (size_t i = pnode.size; i > chid; --i) {
            pnode.keys[i] = pnode.keys[i - 1];
        }
        pnode.keys[chid] = cnode.keys[c_t - 1];
        cnode.size = c_t - 1;
        ++pnode.size;
        WritePageBack(r);
        WritePageBack(child);
        WritePageBack(parent);
        ReportSplit();
        return r;
    }

    TPage MergeChildren(TPage &parent, TPage &l, TPage &r, size_t chid) {
        auto &pnode = parent.Data();
        auto &lnode = l.Data();
        auto &rnode = r.Data();
        for (size_t i = 0; i < rnode.size; ++i) {
            lnode.keys[i + c_t] = rnode.keys[i];
        }
        lnode.keys[c_t - 1] = pnode.keys[chid];
        if (!rnode.is_leaf) {
            for (size_t i = 0; i <= rnode.size; ++i) {
                lnode.children[i + c_t] = rnode.children[i];
            }
        }
        for (size_t i = chid + 1; i < pnode.size; ++i) {
            pnode.children[i] = pnode.children[i + 1];
        }
        for (size_t i = chid; i < pnode.size; ++i) {
            pnode.keys[i] = pnode.keys[i + 1];
        }
        --pnode.size;
        lnode.size = 2 * c_t - 1;
        FreePage(std::move(r));
        WritePageBack(l);
        WritePageBack(parent);
        ReportMerge();
        return std::move(l);
    }

    void WritePageBack(TPage const &page) {
        TPage::Write(m_lctx, page, page.Data().self_ref);
        ReportPageWrite();
    }
    TPage ReadPageIn(ref_t const &ref) const {
        ReportPageRead();
        return TPage::Read(m_lctx, ref);
    }
    TPage AllocatePage() {
        ReportPageAlloc();
        return TPage::Allocate(m_lctx);
    }
    void FreePage(TPage &&page) {
        ReportPageFree();
        TPage pg{std::move(page)};
        return TPage::Free(m_lctx, pg.Data().self_ref);
    }

#ifndef NDEBUG
    void ReportInsert() const {
        ++m_stats.ops;
        ++m_stats.inserts;
        ++m_stats.size;
        m_stats.max_size = std::max(m_stats.max_size, m_stats.size);
    }
    void ReportDelete() const {
        ++m_stats.ops;
        ++m_stats.deletes;
        --m_stats.size;
    }
    void ReportSearch() const {
        ++m_stats.ops;
        ++m_stats.searches;
    }
    void ReportRootPush() const {
        ++m_stats.root_pushes;
        ++m_stats.height;
        m_stats.max_height = std::max(m_stats.max_height, m_stats.height);
    }
    void ReportRootPop() const {
        ++m_stats.root_pops;
        --m_stats.height;
    }
    void ReportSplit()     const { ++m_stats.splits; }
    void ReportMerge()     const { ++m_stats.merges; }
    void ReportRotation()  const { ++m_stats.rotations; }
    void ReportPageAlloc() const { ++m_stats.page_allocations; }
    void ReportPageFree()  const { ++m_stats.page_frees; }
    void ReportPageRead()  const { ++m_stats.page_reads; }
    void ReportPageWrite() const { ++m_stats.page_writes; }
#else
    void ReportInsert()    const {}
    void ReportDelete()    const {}
    void ReportSearch()    const {}
    void ReportRootPush()  const {}
    void ReportRootPop()   const {}
    void ReportSplit()     const {}
    void ReportMerge()     const {}
    void ReportRotation()  const {}
    void ReportPageAlloc() const {}
    void ReportPageFree()  const {}
    void ReportPageRead()  const {}
    void ReportPageWrite() const {}
#endif
};

#ifdef VALIDATE
template <class TPage>
class BTreeValidator {
    BTree<TPage> const *m_bt = nullptr;
    std::multiset<typename BTreePageTraits<TPage>::elem_t> m_mirror{};

    using elem_t = BTreePageTraits<TPage>::elem_t;
    using ref_t = BTreePageTraits<TPage>::ref_t;
    static constexpr size_t c_t = BTreePageTraits<TPage>::c_t;
    static constexpr size_t c_min_sz = BTreePageTraits<TPage>::c_min_sz;
    static constexpr size_t c_max_sz = BTreePageTraits<TPage>::c_max_sz;

public:
    explicit BTreeValidator(BTree<TPage> const &bt) : m_bt{&bt} {}

#define VASSERT(cond_) Assert((cond_), #cond_)

    void Validate() {
        VASSERT(m_bt);
        ssize_t discovered_height = -1;
        size_t discovered_size = 0;
        ValidateNode(
            m_bt->m_root, 0, std::nullopt, std::nullopt,
            discovered_height, discovered_size);
        VASSERT(discovered_size == m_bt->m_size); 
        VASSERT(m_bt->m_size == m_mirror.size()); 
        LOG("Validation: passed sz=%lu h=%lu",
            discovered_size, discovered_height);
    }

    void Assert(bool cond, char const *msg) const {
        if (!cond) {
            fprintf(stderr, "Assertion failed: %s\n", msg);
            fprintf(stderr, "Current tree state:\n");
            Dump();
            fflush(stderr);
            assert(0);
        }
    }

    void Dump() const {
        size_t h = 0;
        while (DumpAtHeight(h++))
            std::cerr << '\n';
    }

    void CheckInsert(elem_t const &e)
        { m_mirror.insert(e); }
    void CheckSearch(elem_t const &e, bool res) const
        { VASSERT(m_mirror.contains(e) == res); }

    void CheckDelete(elem_t const &e, bool res) {
        auto it = m_mirror.find(e);
        VASSERT((it != m_mirror.end()) == res);
        if (it != m_mirror.end())
            m_mirror.erase(it);
    }

private:
    void ValidateNode(
        TPage const &pg, size_t h,
        std::optional<elem_t> const &min_val,
        std::optional<elem_t> const &max_val,
        ssize_t &dh, size_t &ds) const
    {
        auto &node = pg.Data();
        VASSERT(node.size <= c_max_sz);
        if (h > 0) {
            VASSERT(node.size >= c_min_sz);
        }
        ds += node.size;
        if (node.is_leaf) {
            if (dh < 0) {
                dh = h;
            } else {
                VASSERT(h == dh);
            }
        }
        std::optional<elem_t> base = min_val;
        for (size_t i = 0; i < node.size; ++i) {
            elem_t k = node.keys[i];
            if (min_val) {
                VASSERT(k >= *min_val);
            }
            if (max_val) {
                VASSERT(k <= *max_val);
            }
            if (base) {
                VASSERT(k >= base);
            }
            if (!node.is_leaf) {
                auto page = m_bt->ReadPageIn(node.children[i]);
                VASSERT(page.Data().self_ref == node.children[i]);
                ValidateNode(page, h + 1, base, k, dh, ds);
            }
            base = k;
        }
        if (!node.is_leaf) {
            auto page = m_bt->ReadPageIn(node.children[node.size]);
            VASSERT(page.Data().self_ref == node.children[node.size]);
            ValidateNode(page, h + 1, base, max_val, dh, ds);
        }
    }

    bool DumpAtHeight(size_t h) const {
        bool first = true;
        return DumpNodeAtHeight(m_bt->m_root, h, 0, first);
    }
    bool DumpNodeAtHeight(
        TPage const &pg, size_t req_h, size_t cur_h, bool &first) const
    {
        if (cur_h == req_h) {
            DumpNode(pg, first);
            return true;
        }

        auto &node = pg.Data();
        if (node.is_leaf) {
            return false;
        }

        bool res = false;
        for (size_t i = 0; i <= node.size; ++i) {
            res |= DumpNodeAtHeight(
                m_bt->ReadPageIn(node.children[i]), req_h, cur_h + 1, first);
        }

        return res;
    }
    void DumpNode(TPage const &pg, bool &first) const {
        if (first) {
            first = false;
        } else {
            std::cerr << ' ';
        }

        auto &node = pg.Data();
        std::cerr << '[';
        for (size_t i = 0; i < node.size; ++i) {
            if (i != 0)
                std::cerr << ' ';
            std::cerr << node.keys[i];
        }
        std::cerr << ']';
    }

#undef VASSERT
};

template <class TTree>
auto btree_validator_for(TTree const &bt)
{
    return BTreeValidator<typename TTree::page_t>{bt};
}
#endif

#define BRTEE_FILE_TEMPLATE(T_, t_t_) \
    template <class T_, size_t t_t_>  \
    requires BTREE_REQ(T_, size_t, t_t_)

BRTEE_FILE_TEMPLATE(T, t_t)
class BTreeBackingFile {
    FILE *m_f = nullptr;
    size_t m_page_cnt = 0;
    std::vector<size_t> m_free_list{};

public:
    BTreeBackingFile() = default;
    explicit BTreeBackingFile(FILE *f) : m_f{f} {
        if (m_f) {
            fseek(m_f, 0, SEEK_END);
            m_page_cnt = ftell(m_f);
            assert(m_page_cnt % c_page_size_bytes == 0);
            m_page_cnt /= c_page_size_bytes;
            fseek(m_f, 0, SEEK_SET);
        }
    }

    BTreeBackingFile(BTreeBackingFile &&other)
        : m_f{std::exchange(other.m_f, nullptr)}
        , m_page_cnt{std::exchange(other.m_page_cnt, 0)} {}
    BTreeBackingFile &operator=(BTreeBackingFile &&other) {
        BTreeBackingFile tmp{std::move(*this)};
        m_f = std::exchange(other.m_f, nullptr);
        m_page_cnt = std::exchange(other.m_page_cnt, 0);
    }

    BTreeBackingFile(BTreeBackingFile const &) = delete;
    BTreeBackingFile &operator=(BTreeBackingFile const &) = delete;

    struct Page {
        std::unique_ptr<BTreeNodeData<T, size_t, t_t>> data;

        using lctx_t = BTreeBackingFile<T, t_t>;
        using elem_t = T;
        using ref_t = size_t;
        static constexpr size_t c_t = t_t;
        static constexpr size_t c_page_size =
            BTreeTraits<T, size_t, t_t>::c_max_sz;
        static constexpr size_t c_page_size_bytes =
            sizeof(BTreeNodeData<T, size_t, t_t>);

        explicit operator bool() const { return data != nullptr; }

        auto &Data()             { return *data; }
        auto const &Data() const { return *data; }

        static void Write(lctx_t &lctx, Page const &pg, size_t pid)
            { lctx.Write(std::move(pg), pid); }
        static Page Read(lctx_t const &lctx, size_t pid)
            { return lctx.Read(pid); }
        static Page Allocate(lctx_t &lctx)
            { return lctx.Allocate(); }
        static void Free(lctx_t &lctx, size_t pid)
            { lctx.Free(pid); }
        static void Close(lctx_t &lctx)
            { lctx.Close(); }
        static bool IsValid(Page const &page)
            { return bool(page.data); }
    };

    static constexpr size_t c_page_size_bytes = Page::c_page_size_bytes;

    explicit operator bool() const { return m_f; }

    void Write(Page const &pg, size_t pid) {
        assert(m_f);
        assert(pid + 1 <= m_page_cnt);
        size_t start_pos = pid * c_page_size_bytes;
        fseek(m_f, start_pos, SEEK_SET);
        size_t res = fwrite(pg.data.get(), c_page_size_bytes, 1, m_f);
        assert(res == 1);
    }

    Page Read(size_t pid) const {
        assert(m_f);
        Page pg{};
        pg.data = std::make_unique<BTreeNodeData<T, size_t, t_t>>();
        assert(pid + 1 <= m_page_cnt);
        size_t start_pos = pid * c_page_size_bytes;
        fseek(m_f, start_pos, SEEK_SET);
        size_t res = fread(pg.data.get(), c_page_size_bytes, 1, m_f);
        assert(res == 1);
        return pg;
    }

    Page Allocate() {
        size_t pid;
        if (m_free_list.empty()) {
            pid = m_page_cnt++;
        } else {
            pid = m_free_list.back();
            m_free_list.pop_back();
        }
        Page pg{};
        pg.data = std::make_unique<BTreeNodeData<T, size_t, t_t>>();
        pg.data->self_ref = pid;
        return pg;
    }

    void Free(size_t pid) { m_free_list.push_back(pid); }

    void Close() {
        if (m_f) {
            fclose(std::exchange(m_f, nullptr));
        }
    }
};

// For simplicity, not persistent
BRTEE_FILE_TEMPLATE(T, t_t)
static auto create_file_pod_btree(char const *path)
{
    using file_t = BTreeBackingFile<T, t_t>;
    using tree_t = BTree<typename file_t::Page>;
    auto lf = file_t{fopen(path, "wb+")};
    if (!lf) {
        return std::optional<tree_t>{std::nullopt};
    }
#ifdef NDEBUG
    return std::optional<tree_t>{tree_t{std::move(lf)}};
#else
    return std::optional<tree_t>{tree_t{std::move(lf), path}};
#endif
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "Usage: prog fname.\n");
        return 1;
    }

    using test_type_t = int;
    constexpr size_t c_test_t = 4;

    auto btree_maybe = create_file_pod_btree<test_type_t, c_test_t>(argv[1]);
    if (!btree_maybe) {
        fprintf(stderr, "Failed to open %s.\n", argv[1]);
        return 1;
    }

    auto &bt = *btree_maybe;

#ifdef VALIDATE
    auto validator = btree_validator_for(bt);
#define VASSERT(cond_) validator.Assert((cond_), #cond_)
#endif

    [[maybe_unused]] size_t cmd_id = 0;
    while (std::cin.good()) {
        char cmd;
        std::cin >> cmd;
        switch (cmd) {
        case '+': {
            test_type_t item;
            std::cin >> item;
            LOG("%lu: inserting %d", cmd_id, item);
            bt.Insert(item);
#ifdef VALIDATE
            validator.CheckInsert(item);
#endif
            break;
        }
        case '-': {
            test_type_t item;
            std::cin >> item;
            LOG("%lu: deleting %d", cmd_id, item);
            bool removed = bt.Delete(item);
            printf("%s %d\n", removed ? "Removed" : "Not present", item);
#ifdef VALIDATE
            validator.CheckDelete(item, removed);
#endif
            break;
        }
        case '?': {
            test_type_t item;
            std::cin >> item;
            LOG("%lu: searching %d", cmd_id, item);
            bool found = bt.Search(item);
            printf("%s %d\n", found ? "Found" : "Not found", item);
#ifdef VALIDATE
            validator.CheckSearch(item, found);
#endif
            break;
        }
        default:
            assert(0);
        }
#ifdef VALIDATE
        validator.Validate();
#undef VASSERT
#endif
        ++cmd_id;
    }

    bt.DumpStats();
}

#else

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "Usage: prog cmd_count.\n");
        return 1;
    }

    size_t const cmd_count = atol(argv[1]);

    constexpr double c_insert_probability = 0.4f;
    constexpr double c_delete_probability = 0.4f;
    constexpr double c_choose_existing_probability = 0.7f;

    srand(time(nullptr));

    std::set<int> tracker{};

    auto cast = [] { return double(rand()) / RAND_MAX; };

    for (size_t i = 0; i < cmd_count; ++i) {
        double type_cast = cast();
        if (type_cast <= c_insert_probability) {
            int elem = rand();
            printf("+ %d\n", elem);
            tracker.insert(elem);
        } else {
            type_cast -= c_insert_probability;
            bool is_delete = type_cast <= c_delete_probability;
            char glyph = is_delete ? '-' : '?';
            if (tracker.size() && cast() < c_choose_existing_probability) {
                int id = rand() % tracker.size();
                auto it = tracker.begin();
                while (id--) {
                    ++it;
                }
                printf("%c %d\n", glyph, *it);
                if (is_delete) {
                    tracker.erase(it);
                }
            } else {
                int elem;
                do {
                    elem = rand();
                } while (tracker.contains(elem));
                printf("%c %d\n", glyph, elem);
            }
        }
    }
}

#endif
