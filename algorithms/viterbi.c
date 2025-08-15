#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <malloc.h>

#define SCANF_ARGCOUNT(...) (sizeof((void *[]){__VA_ARGS__})/sizeof(void *))
#define SCANF(fmt_, ...)                              \
    do {                                              \
        int read_ = scanf(fmt_, __VA_ARGS__);         \
        assert(read_ == SCANF_ARGCOUNT(__VA_ARGS__)); \
    } while (0)

#define TABLE_AT(x_, y_) ((TABLE)[(y_) * TABLE_STRIDE + (x_)])

typedef struct edge {
    int from, to;
    int label;
    float p;
} edge_t;

typedef struct table_entry {
    float p;
    int prev;
} table_entry_t;

int main()
{
    int v, e, k, v0;
    SCANF("%d %d %d %d", &v, &e, &k, &v0);

    int *labels = alloca(k * sizeof(int));
    for (int i = 0; i < k; ++i)
        SCANF("%d", &labels[i]);
   
    edge_t *edges = alloca(e * sizeof(edge_t));
    for (int i = 0; i < e; ++i) {
        SCANF("%d %d %d %f",
            &edges[i].from, &edges[i].to, &edges[i].label, &edges[i].p);
    }

    // This is only for validation
    float *vertex_outgoing_probs = alloca(v * sizeof(float));
    memset(vertex_outgoing_probs, 0, v * sizeof(*vertex_outgoing_probs));
    for (int i = 0; i < e; ++i)
        vertex_outgoing_probs[edges[i].from] += edges[i].p;
    int validation_failed = 0;
    for (int i = 0; i < v; ++i) {
        if (vertex_outgoing_probs[i] - 1.f > 0.00001f) {
            printf(
                "Invalid outgoing probability for vertex%d = %f",
                i, vertex_outgoing_probs[i]);
            validation_failed = 1;
        }
    }
    if (validation_failed)
        return 1;

    size_t const table_size = v * (k + 1);
    table_entry_t *table = alloca(table_size * sizeof(table_entry_t));
    memset(table, 0, table_size * sizeof(*table));

#define TABLE table
#define TABLE_STRIDE v

    TABLE_AT(v0, 0) = (table_entry_t){1.f, -1};

    for (int i = 1; i <= k; ++i) {
        int const desired_label = labels[i - 1];
        for (int j = 0; j < e; ++j) {
            if (edges[j].label != desired_label)
                continue;

            float p = TABLE_AT(edges[j].from, i - 1).p * edges[j].p;
            if (p > TABLE_AT(edges[j].to, i).p)
                TABLE_AT(edges[j].to, i) = (table_entry_t){p, edges[j].from};
        }
    }

    int last_v = -1;
    float best_prob = 0.f;
    for (int i = 0; i < v; ++i) {
        if (TABLE_AT(i, k).p > best_prob) {
            last_v = i;
            best_prob = TABLE_AT(i, k).p;
        }
    }

    if (best_prob == 0.f) {
        printf("Path doesn't exist\n");
        return 0;
    }

    int *solution = alloca((k + 1) * sizeof(int));
    for (int i = k; i >= 0; --i) {
        solution[i] = last_v;
        last_v = TABLE_AT(last_v, i).prev;
    }

    printf("%d", solution[0]);
    for (int i = 1; i <= k; ++i)
        printf(" -> %d", solution[i]);
    putchar('\n');

    printf("Prob: %f\n", best_prob);

#undef TABLE
#undef TABLE_STRIDE

    return 0;
}
