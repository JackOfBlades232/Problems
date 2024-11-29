#include <cstring>
#include <alloca.h>
#include <iostream>
#include <string>
#include <algorithm>

int main()
{
    std::string s1, s2;
    std::cin >> s1 >> s2;

    size_t table_size = sizeof(int) * (s1.length() + 1) * (s2.length() + 1);
    int *table = (int *)alloca(table_size);
    memset(table, 0xFFFFFFFF, table_size);

    auto helper = [&](const auto &self, int i, int j) {
        size_t table_id = j * (s1.length() + 1) + i;
        if (i == 0 || j == 0)
            return (table[table_id] = 0);

        if (table[table_id] >= 0)
            return table[table_id];
        else if (s1[i - 1] == s2[j - 1])
            return (table[table_id] = self(self, i - 1, j - 1) + 1);
        else
            return (table[table_id] = std::max(self(self, i, j - 1), self(self, i - 1, j)));
    };

    int longest_common_subword_len = helper(helper, s1.length(), s2.length());

    std::cout << longest_common_subword_len << '\n';

    auto print_helper = [&](const auto &self, int i, int j) {
        if (i == 0 || j == 0)
            return;

        size_t table_id = j * (s1.length() + 1) + i;
        size_t lower_id = (j - 1) * (s1.length() + 1) + i;
        size_t right_id = j * (s1.length() + 1) + i - 1;
        size_t diag_id = (j - 1) * (s1.length() + 1) + i - 1;
        if (s1[i - 1] == s2[j - 1] && table[table_id] == table[diag_id] + 1) {
            self(self, i - 1, j - 1);
            std::cout << s1[i - 1];
        } else if (table[table_id] == table[lower_id])
            self(self, i, j - 1);
        else
            self(self, i - 1, j);
    };

    print_helper(print_helper, s1.length(), s2.length());
    std::cout << '\n';

    return 0;
}
