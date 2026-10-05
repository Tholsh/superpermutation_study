#include <bitset>
#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <span>
#include <vector>

using Symbol = uint8_t;

constexpr const char* RED = "\033[31m";
constexpr const char* RESET = "\033[0m";

bool is_dirty(std::span<const Symbol> w, std::size_t n) {
    std::vector<bool> seen(n + 1, false);

    for (Symbol s : w) {
        std::size_t index = static_cast<std::size_t>(s);

        if (index == 0 || index > n) {
            return true;
        }

        if (seen[index]) {
            return true;
        }

        seen[index] = true;
    }

    return false;
}

uint8_t which_index(std::span<const Symbol> bigwindow, std::span<const Symbol> w, std::size_t n) {

    for (uint8_t index = (bigwindow.size() - 2); index > 0; --index) {

        if (bigwindow[index] == bigwindow.back()){    //see what index is the same as the last symbol in the window

            return ((2*n) - index); //return the index of the symbol in the window that is the same as the last symbol in the window
        }
    }

    return 0; //symbol not in window.
}

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "usage: paint-waste N\n";
        return 1;
    }

    std::size_t n = std::strtoull(argv[1], nullptr, 10);

    if (n == 0 || n > 9) {
        std::cerr << "bad N: " << argv[1] << '\n';
        return 1;
    }

    std::vector<Symbol> symbols;
    std::vector<char> raw;

    char c;
    while (std::cin.get(c)) {
        if (std::isspace(static_cast<unsigned char>(c))) {
            continue;
        }

        if (!std::isdigit(static_cast<unsigned char>(c))) {
            std::cerr << "bad character: " << c << '\n';
            return 1;
        }

        Symbol symbol = static_cast<Symbol>(c - '0');

        if (symbol == 0 || symbol > n) {
            std::cerr << "bad symbol: " << c << '\n';
            return 1;
        }

        symbols.push_back(symbol);
        raw.push_back(c);
    }

    std::vector<bool> dirty_at(symbols.size(), false);

    std::size_t dirty_count = 0;
    std::size_t current_dirty_run = 0;
    std::size_t max_dirty_run = 0;
    std::size_t current_clean_run = 0;

    std::vector<uint8_t> waste_indexes;
    std::vector<uint8_t> waste_depths;

    for (std::size_t i = 0; i < symbols.size(); ++i) {
        if (i + 1 < n) {
            continue;
        }

        std::span<const Symbol> w{symbols.data() + i + 1 - n, n};
        //make dynamic bigwindow
        std::size_t bigwindow_size = std::min<std::size_t>(2 * n, i + 1);
        std::size_t bigwindow_start = i + 1 - bigwindow_size;

        std::span<const Symbol> bigwindow{
            symbols.data() + bigwindow_start,
            bigwindow_size
        };

        if (is_dirty(w, n)) {
            dirty_at[i] = true;
            ++dirty_count;
            ++current_dirty_run;
            waste_indexes.push_back(which_index(bigwindow, w, n));  //save the relative index of append
            waste_depths.push_back(current_clean_run);  //save the clean length
            current_clean_run = 0;

            if (current_dirty_run > max_dirty_run) {
                max_dirty_run = current_dirty_run;
            }
        } else {
            current_dirty_run = 0;
            current_clean_run++;
        }
    }

    bool red_on = false;

    for (std::size_t i = 0; i < raw.size(); ++i) {
        bool dirty = dirty_at[i];

        if (dirty && !red_on) {
            std::cout << RED;
            red_on = true;
        }

        if (!dirty && red_on) {
            std::cout << RESET;
            red_on = false;
        }

        std::cout << raw[i];
    }

    if (red_on) {
        std::cout << RESET;
    }

    std::cout << '\n';

    std::size_t window_count = symbols.size() >= n ? symbols.size() - n + 1 : 0;

    std::cerr << "symbols: " << symbols.size() << '\n';
    std::cerr << "n: " << n << '\n';
    std::cerr << "windows: " << window_count << '\n';
    std::cerr << "dirty: " << dirty_count << '\n';
    std::cerr << "clean: " << window_count - dirty_count << '\n';
    std::cerr << "max_dirty_run: " << max_dirty_run << '\n';

    std::cerr << std::hex;



        std::cerr << "\nreduced_alphabet_words:\n";

        for (long long unsigned int index = 0; index < waste_indexes.size(); ++index) {
        std::cerr << '[' << static_cast<unsigned>(waste_depths[index]) << ':' << static_cast<unsigned>(waste_indexes[index]) << "] ";
    }

    std::cerr << '\n';


    return 0;
}
