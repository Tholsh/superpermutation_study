// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Theo H.
// Port-only Pantone/Halfar completion, generalized from the supplied
// n12 generate_ports_only.cpp. Produces no literal superpermutation.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using U = std::uint64_t;
struct Slice { U head, tail; std::uint32_t length; };
static void require(bool ok, const std::string& message) { if (!ok) throw std::runtime_error(message); }
static U pack(const std::array<int, 13>& a, int count, int start = 0, int width = 0) {
    U result = 0;
    for (int j = 0; j < count; ++j) result = (result << 4) | a[width ? (start + j) % width : j];
    return result;
}
int main(int argc, char** argv) {
    try {
        if (argc != 5 || std::string(argv[1]) != "--n") {
            std::cerr << "usage: rllb-ports --n 11|12|13 SELECTION PREFIX\n"; return 2;
        }
        const int n = std::stoi(argv[2]), k = n - 2, h = n - 3;
        require(n >= 11 && n <= 13, "N must be 11, 12, or 13");
        std::ifstream input(argv[3]); require(bool(input), "cannot read selection");
        U expected = 1, f3 = 0, factorial = 1;
        for (int j = 1; j <= n; ++j) {
            factorial *= j;
            if (j == k - 1) expected = factorial;
            if (j >= n - 2) f3 += factorial;
        }
        std::vector<Slice> slices;
        slices.reserve(expected * (k + 1));
        std::vector<U> classes; classes.reserve(expected);
        U charge = 0, detached = 0;
        std::string line;
        while (std::getline(input, line)) {
            std::istringstream row(line); std::string word, visible, extra;
            if (!(row >> word) || word[0] == '#') continue;
            require(bool(row >> visible) && !(row >> extra), "malformed native row");
            require(int(word.size()) == k, "native word width mismatch");
            std::array<int, 13> x{}; unsigned mask = 0;
            for (int j = 0; j < k; ++j) {
                int symbol = word[j] >= '0' && word[j] <= '9' ? word[j] - '0' : word[j] - 'A' + 10;
                require(symbol >= 0 && symbol < k && !(mask & (1u << symbol)), "invalid native alphabet");
                x[j] = symbol; mask |= 1u << symbol;
            }
            int v;
            if (visible == "F") v = k;
            else if (visible == "S") v = k - 2;
            else if (visible == "D") v = 0;
            else { std::size_t used = 0; v = std::stoi(visible, &used); require(used == visible.size(), "invalid visible length"); }
            require(v == 0 || v == k || (v >= 1 && v <= k - 2), "unsupported visible length");
            int zero = int(std::find(x.begin(), x.begin() + k, 0) - x.begin());
            classes.push_back(pack(x, k, zero, k));
            if (v) charge += k - v; else ++detached;
            auto add = [&](const std::array<int, 13>& b, int count) {
                require(slices.size() < UINT32_MAX, "too many ports");
                slices.push_back({pack(b, h), pack(b, h, (count + 1) % (k + 1), k + 1),
                                  static_cast<std::uint32_t>((n + 1) * count + 1)});
            };
            if (v) for (int j = 0; j < k; ++j) {
                std::array<int, 13> b{};
                for (int a = 0; a < j; ++a) b[a] = x[a];
                b[j] = k + 1;
                for (int a = j; a < k; ++a) b[a + 1] = x[a];
                add(b, v + (j < v));
            }
            for (int j = v; j < k; ++j) {
                std::array<int, 13> b{};
                for (int a = 0; a < k; ++a) b[a] = x[(j + a) % k];
                b[k] = k;
                add(b, k + 1);
            }
        }
        require(input.eof(), "selection read failed");
        require(classes.size() == expected && slices.size() == expected * k + charge, "incomplete native selection");
        std::sort(classes.begin(), classes.end());
        require(std::adjacent_find(classes.begin(), classes.end()) == classes.end(), "duplicate native 2-loop");
        classes.clear(); classes.shrink_to_fit();
        std::unordered_map<U, std::uint32_t> lookup;
        lookup.max_load_factor(.7f); lookup.reserve(slices.size());
        for (std::uint32_t j = 0; j < slices.size(); ++j)
            require(lookup.emplace(slices[j].head, j).second, "duplicate completion head");
        std::vector<std::uint32_t> next(slices.size());
        std::vector<unsigned char> incoming(slices.size()), seen(slices.size());
        for (std::uint32_t j = 0; j < slices.size(); ++j) {
            auto tail = lookup.find(slices[j].tail);
            require(tail != lookup.end(), "unbalanced completion tail");
            next[j] = tail->second;
            require(incoming[next[j]]++ == 0, "multiple completion predecessors");
        }
        lookup.clear(); lookup.rehash(0); incoming.clear(); incoming.shrink_to_fit();
        const std::string prefix = argv[4];
        std::ofstream heads(prefix + ".heads.bin", std::ios::binary), table(prefix + ".trails.tsv");
        require(bool(heads) && bool(table), "cannot create output graph");
        table << "trail\tfirst_port\tn_ports\tnative_length\tfirst_head\n";
        U ports = 0, length = 0, trails = 0;
        for (std::uint32_t j = 0; j < slices.size(); ++j) if (!seen[j]) {
            U first = ports, native = 0; auto at = j;
            do {
                require(!seen[at], "completion trail enters an earlier cycle"); seen[at] = 1;
                heads.write(reinterpret_cast<const char*>(&slices[at].head), 8);
                ++ports; native += slices[at].length; at = next[at];
            } while (at != j);
            table << trails++ << '\t' << first << '\t' << ports - first << '\t' << native
                  << '\t' << std::hex << slices[j].head << std::dec << '\n';
            length += native;
        }
        require(length == f3 + charge && ports == slices.size(), "completion accounting mismatch");
        heads.close(); table.close(); require(bool(heads) && bool(table), "graph write failed");
        std::ofstream summary(prefix + ".graph.json");
        summary << "{\"n\":" << n << ",\"native_2loops\":" << expected << ",\"charge\":" << charge
                << ",\"detached\":" << detached << ",\"trails\":" << trails << ",\"ports\":" << ports
                << ",\"native_length\":" << length << "}\n";
        require(bool(summary), "summary write failed");
        std::cout << "n=" << n << " Q=" << charge << " detached=" << detached << " trails=" << trails
                  << " ports=" << ports << " native_length=" << length << '\n';
    } catch (const std::exception& error) { std::cerr << "rllb-ports: " << error.what() << '\n'; return 1; }
}
