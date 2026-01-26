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

#define ARRCNT(a_) (sizeof(a_) / sizeof((a_)[0]))

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

    explicit BTree(lctx_t &&lctx) : m_lctx{std::move(lctx)} {
        m_root = TPage::Allocate(m_lctx);
        m_root.Data().size = 0;
        m_root.Data().is_leaf = true;
        WritePageBack(m_root);
    }
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
            // @TODO: configurable search function
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
            TPage new_root = TPage::Allocate(m_lctx);
            new_root.Data().size = 0;
            new_root.Data().is_leaf = false;
            new_root.Data().children[0] = m_root.Data().self_ref;
            SplitChild(new_root, m_root, 0);
            m_root = std::move(new_root);
        }
        auto *cur_page = &m_root;
        auto *data = &cur_page->Data();
        TPage loaded_page{};
        for (;;) {
            auto &page = *cur_page;
            auto &node = *data;
            ssize_t chid = node.size - 1;
            if (node.is_leaf) {
                // @TODO: configurable search function
                while (chid >= 0 && k < node.keys[chid]) {
                    node.keys[chid + 1] = node.keys[chid];
                    --chid;
                }
                node.keys[chid + 1] = k;
                ++node.size;
                WritePageBack(page);
                break;
            } else {
                // @TODO: configurable search function
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

    size_t Size() const { return m_size; }
    size_t Empty() const { return m_size == 0; }

private:
    TPage SplitChild(TPage &parent, TPage &child, size_t chid) {
        TPage r = TPage::Allocate(m_lctx);
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
        return r;
    }

    void WritePageBack(TPage const &page)
        { TPage::Write(m_lctx, page, page.Data().self_ref); }
    TPage ReadPageIn(ref_t const &ref) const
        { return TPage::Read(m_lctx, ref); }
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

        auto &Data() { return *data; }
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
    return std::optional<tree_t>{tree_t{std::move(lf)}};
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

    size_t cmd_id = 0;
    while (std::cin.good()) {
        char cmd;
        std::cin >> cmd;
        switch (cmd) {
        case '<': {
            test_type_t item;
            std::cin >> item;
            LOG("%lu: inserting %d", cmd_id, item);
            bt.Insert(item);
#ifdef VALIDATE
            validator.CheckInsert(item);
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
    constexpr double c_lookup_existing_probability = 0.7f;

    srand(time(nullptr));

    std::set<int> tracker{};

    auto cast = [] { return double(rand()) / RAND_MAX; };

    for (size_t i = 0; i < cmd_count; ++i) {
        double type_cast = cast();
        if (type_cast <= c_insert_probability) {
            int elem = rand();
            printf("< %d\n", elem);
            tracker.insert(elem);
        } else {
            if (tracker.size() && cast() < c_lookup_existing_probability) {
                int id = rand() % tracker.size();
                auto it = tracker.begin();
                while (id--) {
                    ++it;
                }
                printf("? %d\n", *it);
            } else {
                int elem;
                do {
                    elem = rand();
                } while (tracker.contains(elem));
                printf("? %d\n", elem);
            }
        }
    }
}

#endif

// @TODO: BTree: delete
// @TODO: test/validation
// @TODO: stats
