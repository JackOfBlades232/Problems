#include <queue>
#include <map>
#include <span>
#include <cassert>
#include <cstdio>

using namespace std;

struct bit_encoding_t {
    uint32_t bits;
    uint32_t bit_count;
};

struct BitVector : public vector<uint8_t> {
    uint32_t bit_count;
};

template <class T>
using HuffmanEncoding = map<T, bit_encoding_t>;

template <class T>
HuffmanEncoding<T> create_encoding(
    span<T const> values, span<uint32_t> frequencies)
{
    assert(values.size());
    assert(values.size() == frequencies.size());

    struct node_t {
        uint32_t f = 0;
        T const *key = nullptr;
        node_t *l = nullptr, *r = nullptr;
    };
    struct NodeGreater {
        constexpr bool operator()(node_t const *lhs, node_t const *rhs) const {
            return lhs->f > rhs->f;
        }
    };

    priority_queue<node_t *, vector<node_t *>, NodeGreater> fq{};
    for (size_t i = 0; uint32_t f : frequencies)
        fq.push(new node_t{.f = f, .key = &values[i++]});

    while (fq.size() > 1) {
        node_t *n1 = fq.top();
        fq.pop();
        node_t *n2 = fq.top();
        fq.pop();
        node_t *n = new node_t{n1->f + n2->f, nullptr, n1, n2};
        fq.push(n);
    }

    node_t *root = fq.top();
    fq.pop();

    HuffmanEncoding<T> encoding{};

    auto build = [&](auto &&self, node_t *node, bit_encoding_t enc) -> void {
        if (node->key) {
            encoding[*node->key] = enc;
            assert(!node->l && !node->r);
        } else {
            assert(enc.bit_count < 32);
            assert(node->l && node->r);
            self(
                self, node->l,
                bit_encoding_t{enc.bits, enc.bit_count + 1}
            );
            self(
                self, node->r,
                bit_encoding_t{
                    enc.bits | (1u << enc.bit_count), enc.bit_count + 1}
            );
        }
        delete node;
    };

    build(build, root, bit_encoding_t{0, 0});

    return encoding;
}

template <class T>
BitVector encode(span<T const> values, HuffmanEncoding<T> const &enc)
{
    BitVector stream{};
    for (auto const &v : values) {
        bit_encoding_t e = enc.at(v);
        while (e.bit_count > 8 - (stream.bit_count & 7)) {
            uint32_t s = stream.bit_count & 7;
            if (s == 0)
                stream.push_back(0);
            uint32_t b = 8 - s;
            uint32_t src_mask = (1 << b) - 1;
            uint32_t src = e.bits & src_mask;
            stream.back() |= src << s;
            stream.bit_count += b;
            e.bits >>= b;
            e.bit_count -= b;
        }
        if (e.bit_count) {
            uint32_t s = stream.bit_count & 7;
            if (s == 0)
                stream.push_back(0);
            stream.back() |= e.bits << s;
            stream.bit_count += e.bit_count;
        }
    }
    return stream;
}

template <class T>
vector<T> decode(BitVector const &data, HuffmanEncoding<T> const &enc)
{
    // blah
}

void dump(BitVector const &data)
{
    uint32_t bits_left = data.bit_count;
    for (uint8_t byte : data) {
        for (uint32_t i = 0; i < min<uint32_t>(bits_left, 8); ++i)
            printf("%d", (byte >> i) & 1);
        if (bits_left <= 8)
            break;
        bits_left -= 8;
    }
    printf("\n");
}

int main()
{
    char chars[] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'};
    uint32_t freqs[] = {1, 1, 2, 3, 5, 8, 13, 21};
    char text[] = {
        'f', 'f', 'a', 'd', 'b', 'f', 'g', 'h', 'a',
        'd', 'e', 'f', 'g', 'a', 'd', 'e', 'f', 'g'};

    auto enc = create_encoding<char>(chars, freqs);
    auto encoded = encode<char>(text, enc);

    dump(encoded);
}
