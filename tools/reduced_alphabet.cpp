#include <algorithm>
#include <array>
#include <charconv>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <span>
#include <string_view>
#include <vector>

using Symbol = uint8_t;

constexpr const char* RED = "\033[31m";
constexpr const char* RESET = "\033[0m";

bool is_dirty(std::span<const Symbol> window) {
    unsigned seen = 0;
    for (Symbol symbol : window) {
        const unsigned bit = 1u << symbol;
        if (seen & bit) return true;
        seen |= bit;
    }
    return false;
}

uint8_t which_index(std::span<const Symbol> bigwindow, std::size_t n) {
    for (std::size_t index = bigwindow.size() - 2; index > 0; --index) {
        if (bigwindow[index] == bigwindow.back()) {
            return static_cast<uint8_t>(2 * n - index);
        }
    }
    return 0;
}

// Lehmer rank: only called on windows that contain every symbol exactly once.
std::size_t permutation_rank(std::span<const Symbol> window,
                             const std::array<std::size_t, 10>& factorial) {
    std::size_t rank = 0;
    for (std::size_t i = 0; i < window.size(); ++i) {
        std::size_t smaller = 0;
        for (std::size_t j = i + 1; j < window.size(); ++j) {
            smaller += window[j] < window[i];
        }
        rank += smaller * factorial[window.size() - i - 1];
    }
    return rank;
}

int main(int argc, char** argv) {
    bool short_output = false;
    std::string_view degree;
    for (int i = 1; i < argc; ++i) {
        const std::string_view argument = argv[i];
        if (argument == "-h" || argument == "--help") {
            std::cout << "usage: paint-waste [-s] N < WORD\n"
                         "  -s  statistics only (no colored word or reduced alphabet)\n";
            return 0;
        }
        if (argument == "-s" && !short_output) {
            short_output = true;
        } else if (degree.empty() && !argument.starts_with('-')) {
            degree = argument;
        } else {
            std::cerr << "usage: paint-waste [-s] N < WORD\n";
            return 1;
        }
    }
    std::size_t n = 0;
    if (degree.empty()) {
        std::cerr << "usage: paint-waste [-s] N < WORD\n";
        return 1;
    }
    const auto parsed = std::from_chars(degree.data(), degree.data() + degree.size(), n);
    if (parsed.ec != std::errc{} || parsed.ptr != degree.data() + degree.size() || n == 0 || n > 9) {
        std::cerr << "bad N: " << degree << '\n';
        return 1;
    }

    std::vector<Symbol> symbols;
    char c;
    while (std::cin.get(c)) {
        if (std::isspace(static_cast<unsigned char>(c))) continue;
        if (c < '1' || c > '9') {
            std::cerr << "bad character: " << c << '\n';
            return 1;
        }
        const Symbol symbol = static_cast<Symbol>(c - '0');
        if (symbol > n) {
            std::cerr << "bad symbol: " << c << '\n';
            return 1;
        }
        symbols.push_back(symbol);
    }
    if (std::cin.bad()) {
        std::cerr << "input read failed\n";
        return 1;
    }

    std::array<std::size_t, 10> factorial{};
    factorial[0] = 1;
    for (std::size_t i = 1; i <= n; ++i) factorial[i] = factorial[i - 1] * i;
    std::vector<bool> covered(factorial[n], false);
    std::vector<bool> dirty_at(short_output ? 0 : symbols.size(), false);
    std::vector<uint8_t> waste_indexes;
    std::vector<std::size_t> waste_depths;
    std::size_t dirty_count = 0, distinct = 0;
    std::size_t dirty_run = 0, clean_run = 0, max_dirty_run = 0, max_clean_run = 0;
    std::size_t dirty_runs = 0, clean_runs = 0;

    for (std::size_t i = n - 1; i < symbols.size(); ++i) {
        const std::span<const Symbol> window{symbols.data() + i + 1 - n, n};
        if (is_dirty(window)) {
            ++dirty_count;
            if (dirty_run == 0) ++dirty_runs;
            ++dirty_run;
            max_dirty_run = std::max(max_dirty_run, dirty_run);
            if (!short_output) {
                dirty_at[i] = true;
                const std::size_t bigwindow_size = std::min(2 * n, i + 1);
                const std::span<const Symbol> bigwindow{
                    symbols.data() + i + 1 - bigwindow_size, bigwindow_size};
                waste_indexes.push_back(which_index(bigwindow, n));
                waste_depths.push_back(clean_run);
            }
            clean_run = 0;
        } else {
            dirty_run = 0;
            if (clean_run == 0) ++clean_runs;
            ++clean_run;
            max_clean_run = std::max(max_clean_run, clean_run);
            const auto rank = permutation_rank(window, factorial);
            if (!covered[rank]) {
                covered[rank] = true;
                ++distinct;
            }
        }
    }

    if (!short_output) {
        bool red_on = false;
        for (std::size_t i = 0; i < symbols.size(); ++i) {
            if (dirty_at[i] != red_on) {
                std::cout << (dirty_at[i] ? RED : RESET);
                red_on = dirty_at[i];
            }
            std::cout << static_cast<char>('0' + symbols[i]);
        }
        if (red_on) std::cout << RESET;
        std::cout << "\n\nreduced_alphabet_words:\n" << std::hex;
        for (std::size_t i = 0; i < waste_indexes.size(); ++i) {
            std::cout << '[' << waste_depths[i] << ':' << static_cast<unsigned>(waste_indexes[i]) << "] ";
        }
        std::cout << "\n\nstatistics:\n";
    }

    const std::size_t windows = symbols.size() >= n ? symbols.size() - n + 1 : 0;
    const std::size_t clean = windows - dirty_count;
    std::cout << std::dec
              << "length: " << symbols.size() << '\n'
              << "symbols: " << symbols.size() << '\n'
              << "n: " << n << '\n'
              << "windows: " << windows << '\n'
              << "dirty: " << dirty_count << '\n'
              << "clean: " << clean << '\n'
              << "max_dirty_run: " << max_dirty_run << '\n'
              << "max_clean_run: " << max_clean_run << '\n'
              << "dirty_runs: " << dirty_runs << '\n'
              << "clean_runs: " << clean_runs << '\n'
              << "required_permutations: " << factorial[n] << '\n'
              << "distinct_permutations: " << distinct << '\n'
              << "missing_permutations: " << factorial[n] - distinct << '\n'
              << "repeated_permutation_windows: " << clean - distinct << '\n'
              << "valid_superpermutation: " << (distinct == factorial[n] ? 1 : 0) << '\n';
    return 0;
}
