#define _CRT_SECURE_NO_WARNINGS
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <cstring>
#include <span>
#include <optional>
#include <array>
#include <concepts>
#include <algorithm>
#include <memory>
#include <type_traits>
#include <iostream>
#include <utility>

#ifdef VALIDATE
#include <stack>
#endif

#ifndef TESTGEN

template <class TPage, size_t t_page_cache_size>
class ExternalStack {
    std::array<std::optional<TPage>, t_page_cache_size> m_page_cache{};
    std::array<ssize_t, t_page_cache_size> m_page_cache_ids{};
    std::array<size_t, t_page_cache_size> m_page_cache_gens{};
    typename TPage::loader_context_t m_loader_context;
    size_t m_cur_page = 0, m_cur_page_in_cache = 0, m_in_page = 0;
    size_t m_cur_gen = 0;

    using lctx_t = typename TPage::loader_context_t;
    using elem_t = typename TPage::element_type_t;
    static constexpr size_t c_page_size = TPage::c_page_size;

#ifndef NDEBUG
    struct Stats {
        size_t pushes = 0;
        size_t pops = 0;
        size_t ops = 0;
        size_t size = 0;
        size_t max_size = 0;
        size_t page_flips = 0;
        size_t page_hits = 0;
        size_t page_misses = 0;
        size_t page_reads = 0;
        size_t page_writes = 0;
    } mutable m_stats{};
    char const *m_tag = "";
#endif

public:
    explicit ExternalStack(lctx_t &&lctx) : m_loader_context{std::move(lctx)} {
        std::fill(m_page_cache_ids.begin(), m_page_cache_ids.end(), -1);
        std::fill(m_page_cache_gens.begin(), m_page_cache_gens.end(), 0);
    }
#ifndef NDEBUG
    ExternalStack(lctx_t &&lctx, char const *tag)
        : m_loader_context{std::move(lctx)}
        , m_tag{tag}
    {
        std::fill(m_page_cache_ids.begin(), m_page_cache_ids.end(), -1);
        std::fill(m_page_cache_gens.begin(), m_page_cache_gens.end(), 0);
    }
#endif
    ExternalStack(ExternalStack &&) = default;
    ExternalStack &operator=(ExternalStack &&) = default;
    ExternalStack(ExternalStack const &) = delete;
    ExternalStack &operator=(ExternalStack const &) = delete;
    ~ExternalStack() {
        for (size_t i = 0; i < t_page_cache_size; ++i) {
            if (m_page_cache[i]) {
                WritePageBack(i, m_page_cache_ids[i]);
            }
        }
        TPage::Close(m_loader_context);
    }

#ifndef NDEBUG
    void DumpStats() const {
        fprintf(stderr, "=== ExternalStack \"%s\" perf dump ===\n", m_tag);
        fprintf(stderr, "  Total:       %-7lu\n", m_stats.ops);
        fprintf(stderr, "  Pushes:      %-7lu (%-5.2f%%)\n",
            m_stats.pushes,
            (float(m_stats.pushes) / m_stats.ops) * 100.f);
        fprintf(stderr, "  Pops:        %-7lu (%-5.2f%%)\n",
            m_stats.pops,
            (float(m_stats.pops) / m_stats.ops) * 100.f);
        fprintf(stderr, "  Max size:    %-7lu (%-5.2f%%)\n",
            m_stats.max_size,
            (float(m_stats.max_size) / m_stats.ops) * 100.f);
        fprintf(stderr, "  Page flips:  %-7lu\n", m_stats.page_flips);
        fprintf(stderr, "  Page hits:   %-7lu (%-5.2f%%)\n",
            m_stats.page_hits,
            (float(m_stats.page_hits) / m_stats.page_flips) * 100.f);
        fprintf(stderr, "  Page misses: %-7lu (%-5.2f%%)\n",
            m_stats.page_misses,
            (float(m_stats.page_misses) / m_stats.page_flips) * 100.f);
        fprintf(stderr, "  Page reads:  %-7lu\n", m_stats.page_reads);
        fprintf(stderr, "  Page writes: %-7lu\n", m_stats.page_writes);
        fprintf(stderr, "=== end dump ===\n");
    }
#else
    void DumpStats() const {}
#endif

    void Push(elem_t const &elem) { PushImpl(elem); }
    void Push(elem_t &&elem) { PushImpl(std::move(elem)); }

    std::optional<elem_t> Pop() {
        if (m_cur_page == 0 && m_in_page == 0) {
            return std::nullopt;
        } else if (m_in_page == 0) {
            --m_cur_page;
            m_in_page = c_page_size;
            LoadCurPage();
        }

        ReportPop();
        return std::move((*m_page_cache[m_cur_page_in_cache])[--m_in_page]);
    }

private:
    template <class T>
        requires std::same_as<std::remove_cvref_t<T>, elem_t>
    void PushImpl(T &&e) {
        if (m_in_page == 0) {
            LoadCurPage();
        }

        (*m_page_cache[m_cur_page_in_cache])[m_in_page++] = std::forward<T>(e);
        if (m_in_page == c_page_size) {
            ++m_cur_page;
            m_in_page = 0;
        }

        ReportPush();
    }

    void LoadCurPage() {
        ReportPageFlip();

        if (
            auto it = std::find(
                m_page_cache_ids.begin(), m_page_cache_ids.end(), m_cur_page);
            it != m_page_cache_ids.end())
        {
            m_cur_page_in_cache = it - m_page_cache_ids.begin();
            m_page_cache_gens[m_cur_page_in_cache] = ++m_cur_gen;
            ReportPageHit();
            return;
        }

        size_t max_gen = SSIZE_MAX;
        for (size_t i = 0; size_t gen : m_page_cache_gens) {
            if (m_page_cache_ids[i] == -1) {
                m_cur_page_in_cache = i;
                break;
            } else if (gen < max_gen) {
                m_cur_page_in_cache = i;
                max_gen = gen;
            }
            ++i;
        }

        ssize_t evicted_page_id = m_page_cache_ids[m_cur_page_in_cache];

        if (evicted_page_id >= 0) {
            WritePageBack(m_cur_page_in_cache, evicted_page_id);
        }

        ReadPageIn(m_cur_page_in_cache, m_cur_page);

        ReportPageMiss();
    }

    void WritePageBack(size_t cache_id, size_t page_id) {
        auto &slot = m_page_cache[cache_id];
        assert(slot);
        TPage::Write(m_loader_context, *slot, page_id);
        slot.reset();
        m_page_cache_ids[cache_id] = -1;
        m_page_cache_gens[cache_id] = 0;
        ReportPageWrite();
    }

    void ReadPageIn(size_t cache_id, size_t page_id) {
        auto &slot = m_page_cache[cache_id];
        assert(!slot);
        slot.emplace(TPage::Read(m_loader_context, page_id));
        m_page_cache_ids[cache_id] = page_id;
        m_page_cache_gens[cache_id] = ++m_cur_gen;
        ReportPageRead();
    }

#ifndef NDEBUG
    void ReportPush() const {
        ++m_stats.pushes;
        ++m_stats.ops;
        ++m_stats.size;
        m_stats.max_size = std::max(m_stats.max_size, m_stats.size);
    }
    void ReportPop() const {
        ++m_stats.pops;
        ++m_stats.ops;
        --m_stats.size;
    }
    void ReportPageFlip() const { ++m_stats.page_flips; }
    void ReportPageHit() const { ++m_stats.page_hits; }
    void ReportPageMiss() const { ++m_stats.page_misses; }
    void ReportPageRead() const { ++m_stats.page_reads; }
    void ReportPageWrite() const { ++m_stats.page_writes; }
#else
    void ReportPush() const {}
    void ReportPop() const {}
    void ReportPageFlip() const {}
    void ReportPageHit() const {}
    void ReportPageMiss() const {}
    void ReportPageRead() const {}
    void ReportPageWrite() const {}
#endif
};

template <class T, size_t t_page_size>
    requires std::is_trivially_copyable_v<T>
class LoadableFile {
    FILE *m_f = nullptr;
    size_t m_size = 0;

public:
    LoadableFile() = default;
    explicit LoadableFile(FILE *f) : m_f{f} {
        if (m_f) {
            fseek(m_f, 0, SEEK_END);
            m_size = ftell(m_f);
            fseek(m_f, 0, SEEK_SET);
        }
    }

    LoadableFile(LoadableFile &&other)
        : m_f{std::exchange(other.m_f, nullptr)}
        , m_size{std::exchange(other.m_size, 0)} {}
    LoadableFile &operator=(LoadableFile &&other) {
        LoadableFile tmp{std::move(*this)};
        m_f = std::exchange(other.m_f, nullptr);
        m_size = std::exchange(other.m_size, 0);
    }

    LoadableFile(LoadableFile const &) = delete;
    LoadableFile &operator=(LoadableFile const &) = delete;

    struct Page {
        std::unique_ptr<std::array<T, t_page_size>> data;

        using loader_context_t = LoadableFile<T, t_page_size>;
        using element_type_t = T;
        static constexpr size_t c_page_size = t_page_size;

        T &operator[](size_t i) { return data->at(i); }
        T const &operator[](size_t i) const { return data->at(i); }

        static void Write(loader_context_t &lctx, Page const &pg, size_t pid)
            { lctx.Write(std::move(pg), pid); }
        static Page Read(loader_context_t &lctx, size_t pid)
            { return lctx.Read(pid); }
        static void Close(loader_context_t &lctx)
            { lctx.Close(); }
    };

    static constexpr size_t c_page_size_bytes = t_page_size * sizeof(T);

    explicit operator bool() const { return m_f; }

    void Write(Page const &pg, size_t pid) {
        assert(m_f);
        size_t start_pos = pid * c_page_size_bytes;
        fseek(m_f, start_pos, SEEK_SET);
        size_t res = fwrite(pg.data->data(), c_page_size_bytes, 1, m_f);
        assert(res == 1);
        m_size = std::max(start_pos + c_page_size_bytes, m_size);
    }

    Page Read(size_t pid) {
        assert(m_f);
        Page pg{};
        pg.data = std::make_unique<std::array<T, t_page_size>>();
        size_t start_pos = pid * c_page_size_bytes;
        size_t bytes_to_read = 0;
        if (start_pos < m_size) {
            bytes_to_read = std::min(c_page_size_bytes, m_size - start_pos);
            fseek(m_f, start_pos, SEEK_SET);
            size_t res = fread(pg.data->data(), bytes_to_read, 1, m_f);
            assert(res == 1);
        }
        if (bytes_to_read < c_page_size_bytes) {
            size_t bytes_to_clear = c_page_size_bytes - bytes_to_read;
            memset(pg.data->data() + bytes_to_read, 0, bytes_to_clear); 
        }
        return pg;
    }

    void Close() {
        if (m_f) {
            fclose(std::exchange(m_f, nullptr));
        }
    }
};

// For simplicity, not persistent
template <class T, size_t t_page_size, size_t t_page_cache_size>
    requires std::is_trivially_copyable_v<T>
static auto create_file_pod_stack(char const *path)
{
    using lf_t = LoadableFile<T, t_page_size>;
    using st_t = ExternalStack<typename lf_t::Page, t_page_cache_size>;
    lf_t lf = LoadableFile<T, t_page_size>{fopen(path, "wb+")};
    if (!lf) {
        return std::optional<st_t>{std::nullopt};
    }
#ifndef NDEBUG
    return std::optional<st_t>{st_t{std::move(lf), path}};
#else
    return std::optional<st_t>{st_t{std::move(lf)}};
#endif
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "Usage: prog fname.\n");
        return 1;
    }

    using test_type_t = int;
    constexpr size_t c_test_page_size = 1 << 10;
    constexpr size_t c_test_page_cache_size = 2;

    auto stack_maybe = create_file_pod_stack<
        test_type_t, c_test_page_size, c_test_page_cache_size>(argv[1]);
    if (!stack_maybe) {
        fprintf(stderr, "Failed to open %s.\n", argv[1]);
        return 1;
    }

    auto &stk = *stack_maybe;

#ifdef VALIDATE
    std::stack<test_type_t> checker{};
#endif

    while (std::cin.good()) {
        char cmd;
        std::cin >> cmd;
        switch (cmd) {
        case '<': {
            test_type_t item;
            std::cin >> item;
            stk.Push(item);
#ifdef VALIDATE
            checker.push(item);
#endif
            break;
        }
        case '>': {
            auto maybe = stk.Pop();
            if (maybe) {
                printf("%d\n", *maybe);
            } else {
                printf("Stack was empty!\n");
            }
#ifdef VALIDATE
            if (maybe) {
                assert(*maybe == checker.top());
                checker.pop();
            } else {
                assert(checker.empty());
            }
#endif
            break;
        }
        default:
            assert(0);
        }
    }

    stk.DumpStats();

#ifdef VALIDATE
    for (;;) {
        auto maybe = stk.Pop();
        if (maybe) {
            assert(*maybe == checker.top());
            checker.pop();
        } else {
            assert(checker.empty());
            break;
        }
    }
#endif
}

#else

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "Usage: prog cmd_count.\n");
        return 1;
    }

    size_t const cmd_count = atol(argv[1]);

    srand(time(nullptr));

    constexpr double c_probability_base = 0.5f;
    constexpr double c_probability_after_pushswitch = 0.999f;
    constexpr double c_probability_after_popswitch = 0.001f;
    constexpr double c_probability_increment = 1e-6;

    double next_probability = c_probability_after_pushswitch;
    enum move_t {
        e_mv_push,
        e_mv_pop
    } prev_move = e_mv_push;

    for (size_t i = 0; i < cmd_count; ++i) {
        double cast = double(rand()) / RAND_MAX;
        move_t next_move = cast <= next_probability ? e_mv_push : e_mv_pop;
        if (next_move == e_mv_push) {
            printf("< %d\n", rand());
            if (prev_move != next_move) {
                next_probability = c_probability_after_pushswitch;
            } else if (next_probability > c_probability_base) {
                next_probability -= c_probability_increment;
            }
        } else {
            printf(">\n");
            if (prev_move != next_move) {
                next_probability = c_probability_after_popswitch;
            } else if (next_probability < c_probability_base) {
                next_probability += c_probability_increment;
            }
        }
        prev_move = next_move;
    }
}

#endif
