// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Theo H.
// Fast phase-coupled connector-trie dual, derived from the supplied n12
// global_trie_multilevel.cpp. The model is unchanged: one intact weight-3
// opening per trail. It does not certify unrestricted weight-2/split searches.
#include <algorithm>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif

namespace {
using U = std::uint64_t;
using Clock = std::chrono::steady_clock;
constexpr std::uint32_t absent = UINT32_MAX;
constexpr U checkpoint_magic = 0x4b52414654524e31ULL;
struct Trail { std::uint32_t first, count; };
struct State { std::uint32_t in = absent, out = absent; };
struct Pick { int in_level = -1, out_level = -1; std::uint32_t in = 0, out = 0; };
struct Level {
    int depth;
    std::vector<U> keys;
    std::vector<State> states;
    std::vector<double> theta, incoming, outgoing, best_theta;
    std::vector<std::int32_t> gradient;
    U available_in = 0, available_out = 0;
};
[[noreturn]] void fail(const std::string& text) { throw std::runtime_error(text); }
double seconds(Clock::time_point start) { return std::chrono::duration<double>(Clock::now() - start).count(); }
template<class T> void read(std::istream& stream, T& value) {
    if (!stream.read(reinterpret_cast<char*>(&value), sizeof(value))) fail("truncated binary input");
}
template<class T> void write(std::ostream& stream, const T& value) {
    stream.write(reinterpret_cast<const char*>(&value), sizeof(value));
}
std::int64_t integer(const std::string& value) {
    std::size_t used = 0;
    auto n = std::stoll(value, &used);
    if (used != value.size()) fail("invalid integer: " + value);
    return n;
}
double real(const std::string& value) {
    std::size_t used = 0;
    double x = std::stod(value, &used);
    if (used != value.size() || !std::isfinite(x)) fail("invalid number: " + value);
    return x;
}

std::vector<Trail> load_trails(const std::string& prefix, U& total, bool& heads_format) {
    std::ifstream file(prefix + ".trails.tsv");
    if (!file) fail("cannot read " + prefix + ".trails.tsv");
    std::string line;
    std::getline(file, line);
    heads_format = line.find("first_port") != std::string::npos;
    if (!heads_format && line.find("firstport") == std::string::npos) fail("unknown trail table header");
    std::vector<Trail> trails;
    while (std::getline(file, line)) {
        if (line.empty() || line == "\r") continue;
        std::istringstream row(line);
        U id, a, b, c, d, first, count;
        if (heads_format) {
            std::string head;
            if (!(row >> id >> a >> b >> c >> head)) fail("malformed heads trail row");
            first = a; count = b;
        } else {
            if (!(row >> id >> a >> b >> c >> d)) fail("malformed ports trail row");
            first = c; count = d;
        }
        if (id != trails.size() || first != total || !count || count > UINT32_MAX || total + count > UINT32_MAX)
            fail("invalid or oversized trail index");
        trails.push_back({static_cast<std::uint32_t>(first), static_cast<std::uint32_t>(count)});
        total += count;
    }
    if (!file.eof() || trails.empty() || trails.size() > INT32_MAX) fail("empty or invalid trail table");
    return trails;
}

std::vector<U> load_heads(const std::string& prefix, U count, bool heads_format, int n) {
    const std::string name = prefix + (heads_format ? ".heads.bin" : ".ports.bin");
    std::ifstream file(name, std::ios::binary);
    if (!file) fail("cannot read " + name);
    const U stride = heads_format ? 8 : 12;
    if (std::filesystem::file_size(name) != count * stride) fail("port binary length mismatch");
    std::vector<U> heads(count);
    // Large block reads avoid two iostream calls for each individual port.
    constexpr std::size_t block = 1 << 16;
    std::vector<char> bytes(block * stride);
    for (U begin = 0; begin < count; begin += block) {
        const U size = std::min<U>(block, count - begin);
        if (!file.read(bytes.data(), size * stride)) fail("truncated ports");
        for (U j = 0; j < size; ++j) {
            U head;
            std::memcpy(&head, bytes.data() + j * stride + (heads_format ? 0 : 4), 8);
            if (head >> (4 * (n - 3))) fail("head exceeds the declared endpoint width");
            for (int k = 0; k < n - 3; ++k)
                if (((head >> (4 * k)) & 15) >= U(n)) fail("invalid alphabet symbol");
            heads[begin + j] = head;
        }
    }
    return heads;
}

// Four stable, linear radix passes replace repeated comparison sorts and
// millions of binary searches. Each record carries a key and a port/role ID.
void radix_sort(std::vector<U>& data, std::vector<U>& scratch) {
    constexpr unsigned bits = 16, buckets = 1 << bits;
    std::vector<std::size_t> positions(buckets);
    scratch.resize(data.size());
    for (unsigned shift = 0; shift < 64; shift += bits) {
        std::fill(positions.begin(), positions.end(), 0);
        for (U x : data) ++positions[(x >> shift) & (buckets - 1)];
        std::size_t sum = 0;
        for (auto& position : positions) { auto size = position; position = sum; sum += size; }
        for (U x : data) scratch[positions[(x >> shift) & (buckets - 1)]++] = x;
        data.swap(scratch);
    }
}

Level make_level(int k, int h, const std::vector<U>& heads,
                 const std::vector<std::uint32_t>& owner, std::vector<U>& records, std::vector<U>& scratch) {
    Level level;
    level.depth = k;
    level.states.resize(heads.size());
    const unsigned slot_bits = std::bit_width(U(heads.size()) * 2 - 1);
    if (slot_bits + 4 * k > 64) fail("port graph exceeds radix encoding capacity");
    const U slot_mask = (U(1) << slot_bits) - 1;
    const U key_mask = (U(1) << (4 * k)) - 1;
    records.resize(heads.size() * 2);
    for (U i = 0; i < heads.size(); ++i) {
        records[i * 2] = ((heads[i] >> (4 * (h - k))) << slot_bits) | (i * 2);
        records[i * 2 + 1] = ((heads[i] & key_mask) << slot_bits) | (i * 2 + 1);
    }
    radix_sort(records, scratch);
    for (std::size_t begin = 0; begin < records.size();) {
        const U key = records[begin] >> slot_bits;
        std::size_t end = begin;
        std::uint32_t low[2] = {absent, absent}, high[2] = {0, 0};
        while (end < records.size() && (records[end] >> slot_bits) == key) {
            const U slot = records[end] & slot_mask;
            const auto trail = owner[slot >> 1];
            const unsigned role = slot & 1;
            low[role] = std::min(low[role], trail); high[role] = std::max(high[role], trail);
            ++end;
        }
        if (level.keys.size() >= absent) fail("too many connector keys");
        const auto node = static_cast<std::uint32_t>(level.keys.size());
        level.keys.push_back(key);
        for (std::size_t j = begin; j < end; ++j) {
            const U slot = records[j] & slot_mask, port = slot >> 1;
            const unsigned role = slot & 1, other = role ^ 1;
            if (low[other] != absent && (low[other] != owner[port] || high[other] != owner[port])) {
                if (role == 0) { level.states[port].in = node; ++level.available_in; }
                else { level.states[port].out = node; ++level.available_out; }
            }
        }
        begin = end;
    }
    // Ineligible roles use one sentinel value, so the scoring loop has no
    // separate availability flags or branches.
    const auto sentinel = static_cast<std::uint32_t>(level.keys.size());
    for (auto& state : level.states) {
        if (state.in == absent) state.in = sentinel;
        if (state.out == absent) state.out = sentinel;
    }
    level.theta.resize(level.keys.size());
    level.gradient.resize(level.keys.size());
    level.incoming.resize(level.keys.size() + 1);
    level.outgoing.resize(level.keys.size() + 1);
    return level;
}

U key_hash(const Level& level) {
    U hash = 1469598103934665603ULL;
    for (U key : level.keys) { hash ^= key; hash *= 1099511628211ULL; }
    return hash;
}
void load_prices(const std::string& path, int minimum, std::vector<Level>& levels) {
    std::ifstream file(path, std::ios::binary);
    if (!file) fail("cannot read checkpoint " + path);
    U magic; std::int32_t depth, count; double old_best;
    read(file, magic); read(file, depth); read(file, count); read(file, old_best);
    if (magic != checkpoint_magic || depth != minimum || count != int(levels.size())) fail("checkpoint header mismatch");
    for (auto& level : levels) {
        U size, hash; read(file, size); read(file, hash);
        if (size != level.keys.size() || hash != key_hash(level)) fail("checkpoint trie mismatch");
        if (!file.read(reinterpret_cast<char*>(level.theta.data()), size * sizeof(double))) fail("truncated checkpoint");
        for (double value : level.theta) if (!std::isfinite(value)) fail("non-finite checkpoint price");
    }
    if (file.peek() != std::char_traits<char>::eof()) fail("trailing checkpoint data");
    // Recompute from prices on THIS graph. A remembered bound is not a
    // transferable certificate, even if another graph has the same key set.
    (void)old_best;
}
void save_prices(const std::string& path, int minimum, const std::vector<Level>& levels, double best) {
    std::ofstream file(path, std::ios::binary | std::ios::trunc);
    if (!file) fail("cannot write checkpoint " + path);
    std::int32_t depth = minimum, count = static_cast<std::int32_t>(levels.size());
    write(file, checkpoint_magic); write(file, depth); write(file, count); write(file, best);
    for (const auto& level : levels) {
        U size = level.keys.size(), hash = key_hash(level);
        write(file, size); write(file, hash);
        file.write(reinterpret_cast<const char*>(level.best_theta.data()), size * sizeof(double));
    }
    if (!file) fail("checkpoint write failed");
}

// Preserve the archived n13 grouped-price model too. It is a different (coarser)
// price family than full trie keys. Keeping packed heads uses half the memory
// of the old eight-uint16 group-index record per port.
int grouped_bound(const std::vector<U>& heads, const std::vector<Trail>& trails, int n,
                  int minimum, int rounds, double step, std::int64_t charge, std::int64_t target,
                  int threads, const std::string& output, Clock::time_point started) {
    const int h = n - 3, group_width = n * n, group_count = (h - minimum) * group_width;
    std::vector<double> price(group_count), accumulated(group_count), gradient(group_count);
    std::vector<double> incoming(group_count), outgoing(group_count), history, scores(trails.size());
    std::vector<int> selected_in(trails.size()), selected_out(trails.size());
    double best = std::numeric_limits<double>::infinity(); int best_iteration = -1;
    const double prepare_seconds = seconds(started);
    const auto pricing_start = Clock::now();
    for (int iteration = 0; iteration <= rounds; ++iteration) {
        for (int k = minimum; k < h; ++k) {
            for (int j = 0; j < group_width; ++j) {
                const int key = (k - minimum) * group_width + j;
                incoming[key] = k - price[key]; outgoing[key] = k + price[key];
            }
        }
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 1) if(threads > 1)
#endif
        for (std::int64_t t = 0; t < std::int64_t(trails.size()); ++t) {
            const auto trail = trails[t]; U winner = trail.first, ties = 0;
            double maximum = -std::numeric_limits<double>::infinity();
            for (U p = trail.first, end = p + trail.count; p < end; ++p) {
                const U head = heads[p];
                const int first = int(head >> (4 * (h - 1))), last = head & 15;
                double in = minimum - 1, out = in;
                for (int k = minimum; k < h; ++k) {
                    const int offset = (k - minimum) * group_width;
                    const int a = offset + first * n + ((head >> (4 * (h - k))) & 15);
                    const int b = offset + int((head >> (4 * (k - 1))) & 15) * n + last;
                    in = std::max(in, incoming[a]); out = std::max(out, outgoing[b]);
                }
                const double value = in + out;
                if (value > maximum + 1e-7) { maximum = value; winner = p; ties = 1; }
                else if (std::fabs(value - maximum) <= 1e-7 && (++ties) % 113 == 0) winner = p;
            }
            const U head = heads[winner];
            const int first = int(head >> (4 * (h - 1))), last = head & 15;
            double in = minimum - 1, out = in; int chosen_in = -1, chosen_out = -1;
            for (int k = minimum; k < h; ++k) {
                const int offset = (k - minimum) * group_width;
                const int a = offset + first * n + ((head >> (4 * (h - k))) & 15);
                const int b = offset + int((head >> (4 * (k - 1))) & 15) * n + last;
                if (incoming[a] > in) { in = incoming[a]; chosen_in = a; }
                if (outgoing[b] > out) { out = outgoing[b]; chosen_out = b; }
            }
            scores[t] = maximum; selected_in[t] = chosen_in; selected_out[t] = chosen_out;
        }
        double two_upper = 0;
        for (double score : scores) two_upper += score;
        const double upper = two_upper / 2;
        if (!std::isfinite(upper)) fail("non-finite grouped dual");
        history.push_back(upper);
        if (upper < best) { best = upper; best_iteration = iteration; }
        if (iteration == rounds) break;
        std::fill(gradient.begin(), gradient.end(), 0);
        for (std::size_t t = 0; t < trails.size(); ++t) {
            if (selected_in[t] >= 0) --gradient[selected_in[t]];
            if (selected_out[t] >= 0) ++gradient[selected_out[t]];
        }
        for (int j = 0; j < group_count; ++j) {
            accumulated[j] += gradient[j] * gradient[j];
            if (gradient[j]) price[j] -= step * gradient[j] / std::sqrt(1.0 + accumulated[j]);
        }
    }
    if (best > double(INT64_MAX / 2)) fail("dual exceeds integer range");
    const auto overlap = std::int64_t(std::ceil(best + 1e-5));
    std::int64_t factorial = 1, f3 = 0;
    for (int i = 1; i <= n; ++i) { factorial *= i; if (i >= n - 2) f3 += factorial; }
    const std::int64_t joining = std::int64_t(h) * std::int64_t(trails.size()) - overlap;
    const auto length = f3 + charge + joining;
    const double pricing_seconds = seconds(pricing_start);
    std::ofstream out(output);
    if (!out) fail("cannot write " + output);
    out << "{\n\"scope\":\"one intact weight-3 cut per trail (NOT weight-2 or trail splits)\",\n"
        << "\"certified_for_unrestricted_search\":false,\"pricing\":\"grouped_first_last_symbols\",\n"
        << "\"n\":" << n << ",\"trails\":" << trails.size() << ",\"ports\":" << heads.size()
        << ",\"charge\":" << charge << ",\"min_key\":" << minimum
        << ",\"dual_overlap_upper_raw\":" << std::setprecision(12) << best
        << ",\"certified_overlap_upper\":" << overlap << ",\"joining_cost_lower_bound\":" << joining
        << ",\"length_lower_bound\":" << length << ",\"target_to_beat\":" << target
        << ",\"certified_reject_restricted\":" << (length >= target ? "true" : "false")
        << ",\"iterations\":" << rounds << ",\"best_iteration\":" << best_iteration << ",\"dual_history\":[";
    for (std::size_t i = 0; i < history.size(); ++i) { if (i) out << ','; out << std::setprecision(12) << history[i]; }
    out << "],\"timing_seconds\":{\"prepare\":" << prepare_seconds << ",\"pricing\":" << pricing_seconds
        << ",\"total\":" << seconds(started) << "},\"threads\":" << threads << "\n}\n";
    if (!out) fail("result write failed");
    std::cout << "RLLB_GROUPED n=" << n << " U<=" << overlap << " L>=" << length
              << " prepare_seconds=" << prepare_seconds << " pricing_seconds=" << pricing_seconds << '\n';
    return 0;
}

int run(int argc, char** argv) {
    if (argc == 2 && std::string(argv[1]) == "--help") {
        std::cout << "usage: rllb PREFIX CHARGE OUTPUT.json [min_key=7] [iterations=80] [step=0.04] [target=522736428] [prices_in|-] [prices_out|-] [--n 11|12|13] [--threads N] [--grouped]\n"
                     "Reads .trails.tsv plus .ports.bin (12-byte records) or .heads.bin (8-byte heads).\n"
                     "Prices full connector keys; one shared opening phase per trail. Restricted intact weight-3 model only.\n"
                     "Defaults to at most four OpenMP threads; --threads overrides it. N=11/13 require an explicit target.\n"
                     "--grouped uses the archived n13 endpoint-symbol grouping and AdaGrad; no price checkpoints.\n";
        return 0;
    }
    int n = 12, threads = 1;
    bool grouped = false;
#ifdef _OPENMP
    threads = std::min(4, omp_get_max_threads());
#endif
    std::vector<std::string> args;
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--grouped") grouped = true;
        else if (arg == "--n" || arg == "--threads") {
            if (++i == argc) fail("missing " + arg + " value");
            auto value = integer(argv[i]);
            if (value < 1 || value > 1024) fail("invalid " + arg + " value");
            (arg == "--n" ? n : threads) = int(value);
        } else args.push_back(arg);
    }
    if (args.size() < 3 || args.size() > 9) fail("use --help for arguments");
    if (n < 11 || n > 13) fail("N must be 11, 12, or 13");
    const int h = n - 3;
    const std::string prefix = args[0], output = args[2];
    const auto charge = integer(args[1]);
    const auto minimum_value = args.size() > 3 ? integer(args[3]) : 7;
    const auto rounds_value = args.size() > 4 ? integer(args[4]) : 80;
    if (charge < 0 || minimum_value < 1 || minimum_value >= h || rounds_value < 0 || rounds_value > INT32_MAX)
        fail("invalid charge, depth, or iteration count");
    const int minimum = int(minimum_value), rounds = int(rounds_value);
    const double step = args.size() > 5 ? real(args[5]) : .04;
    if (step < 0) fail("negative step");
    if (n != 12 && args.size() <= 6) fail("specify the target length when using --n 11 or --n 13");
    const auto target = args.size() > 6 ? integer(args[6]) : 522736428;
    const bool saving = args.size() > 8 && args[8] != "-";
    if (grouped && (saving || (args.size() > 7 && args[7] != "-"))) fail("grouped mode does not use full-key price checkpoints");
#ifdef _OPENMP
    omp_set_dynamic(0); omp_set_num_threads(threads);
#else
    if (threads != 1) fail("rebuild with OpenMP to use --threads");
#endif
    const auto started = Clock::now();
    U count = 0; bool heads_format;
    auto trails = load_trails(prefix, count, heads_format);
    std::int64_t factorial_check = 1, base_check = 0;
    for (int i = 1; i <= n; ++i) { factorial_check *= i; if (i >= n - 2) base_check += factorial_check; }
    base_check += std::int64_t(h) * std::int64_t(trails.size());
    if (charge > INT64_MAX - base_check) fail("charge exceeds length counter range");
    auto heads = load_heads(prefix, count, heads_format, n);
    if (grouped) return grouped_bound(heads, trails, n, minimum, rounds, step, charge, target,
                                      threads, output, started);
    const double read_seconds = seconds(started);
    std::vector<std::uint32_t> owner(count);
    for (std::uint32_t t = 0; t < trails.size(); ++t)
        std::fill_n(owner.begin() + trails[t].first, trails[t].count, t);
    std::vector<Level> levels;
    levels.reserve(h - minimum);
    std::vector<U> records, scratch;
    for (int k = minimum; k < h; ++k) {
        levels.push_back(make_level(k, h, heads, owner, records, scratch));
        const auto& level = levels.back();
        std::cerr << "trie depth=" << k << " keys=" << level.keys.size() << "\n";
    }
    heads.clear(); heads.shrink_to_fit(); owner.clear(); owner.shrink_to_fit();
    records.clear(); records.shrink_to_fit(); scratch.clear(); scratch.shrink_to_fit();
    if (args.size() > 7 && args[7] != "-") load_prices(args[7], minimum, levels);
    const double prepare_seconds = seconds(started);
    const auto pricing_start = Clock::now();
    const double fallback = .5 * (minimum - 1);
    double best = std::numeric_limits<double>::infinity(); int best_iteration = -1;
    std::vector<double> history, scores(trails.size());
    std::vector<Pick> picked(trails.size());
    for (int iteration = 0; iteration <= rounds; ++iteration) {
        for (auto& level : levels) {
            for (std::size_t j = 0; j < level.keys.size(); ++j) {
                level.incoming[j] = .5 * level.depth - level.theta[j];
                level.outgoing[j] = .5 * level.depth + level.theta[j];
            }
            level.incoming.back() = level.outgoing.back() = fallback;
        }
        // Parallelize only the independent trail evaluations. Sum and update
        // prices in original trail order, retaining deterministic arithmetic.
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 1) if(threads > 1)
#endif
        for (std::int64_t t = 0; t < std::int64_t(trails.size()); ++t) {
            const auto trail = trails[t];
            double maximum = -std::numeric_limits<double>::infinity();
            std::uint32_t winner = trail.first;
            for (std::uint32_t i = trail.first; i < trail.first + trail.count; ++i) {
                double incoming = fallback, outgoing = fallback;
                for (const auto& level : levels) {
                    const auto state = level.states[i];
                    incoming = std::max(incoming, level.incoming[state.in]);
                    outgoing = std::max(outgoing, level.outgoing[state.out]);
                }
                const double value = incoming + outgoing;
                if (value > maximum + 1e-11) { maximum = value; winner = i; }
            }
            Pick pick; double incoming = fallback, outgoing = fallback;
            for (int z = 0; z < int(levels.size()); ++z) {
                const auto& level = levels[z]; const auto state = level.states[winner];
                if (level.incoming[state.in] > incoming) {
                    incoming = level.incoming[state.in]; pick.in_level = z; pick.in = state.in;
                }
                if (level.outgoing[state.out] > outgoing) {
                    outgoing = level.outgoing[state.out]; pick.out_level = z; pick.out = state.out;
                }
            }
            scores[t] = maximum; picked[t] = pick;
        }
        double upper = 0;
        for (double score : scores) upper += score;
        if (!std::isfinite(upper)) fail("non-finite dual; reduce the step");
        if (upper < best) {
            best = upper; best_iteration = iteration;
            if (saving) for (auto& level : levels) level.best_theta = level.theta;
        }
        history.push_back(upper);
        if (iteration == rounds) break;
        std::vector<std::vector<std::uint32_t>> touched(levels.size());
        auto add = [&](int z, std::uint32_t key, int delta) {
            auto& gradient = levels[z].gradient[key];
            if (gradient == 0) touched[z].push_back(key);
            gradient += delta;
        };
        for (const auto& pick : picked) {
            if (pick.in_level >= 0) add(pick.in_level, pick.in, -1);
            if (pick.out_level >= 0) add(pick.out_level, pick.out, 1);
        }
        const double eta = step / std::sqrt(1.0 + .2 * iteration);
        for (std::size_t z = 0; z < levels.size(); ++z) {
            auto& level = levels[z];
            for (auto key : touched[z]) {
                if (level.gradient[key]) level.theta[key] -= eta * level.gradient[key];
                level.gradient[key] = 0;
            }
        }
    }
    const double price_seconds = seconds(pricing_start);
    if (best > double(INT64_MAX / 2)) fail("dual exceeds integer range");
    const auto overlap = std::int64_t(std::ceil(best + 1e-5));
    std::int64_t factorial = 1, f3 = 0;
    for (int i = 1; i <= n; ++i) { factorial *= i; if (i >= n - 2) f3 += factorial; }
    const std::int64_t joining = std::int64_t(h) * std::int64_t(trails.size()) - overlap;
    const auto length = f3 + charge + joining;
    std::ofstream out(output);
    if (!out) fail("cannot write " + output);
    out << "{\n\"scope\":\"one intact weight-3 cut per trail (NOT weight-2 or trail splits)\",\n"
        << "\"certified_for_unrestricted_search\":false,\n\"n\":" << n
        << ",\"trails\":" << trails.size() << ",\"ports\":" << count << ",\"charge\":" << charge
        << ",\"min_key\":" << minimum << ",\n\"trie_levels\":[";
    for (std::size_t z = 0; z < levels.size(); ++z) {
        const auto& level = levels[z]; if (z) out << ',';
        out << "{\"depth\":" << level.depth << ",\"nodes\":" << level.keys.size()
            << ",\"incoming_available\":" << level.available_in << ",\"outgoing_available\":" << level.available_out << '}';
    }
    out << "],\n\"dual_overlap_upper_raw\":" << std::setprecision(12) << best
        << ",\"certified_overlap_upper\":" << overlap << ",\n\"joining_cost_lower_bound\":" << joining
        << ",\"length_lower_bound\":" << length << ",\"target_to_beat\":" << target
        << ",\n\"certified_reject_restricted\":" << (length >= target ? "true" : "false")
        << ",\"iterations\":" << rounds << ",\"best_iteration\":" << best_iteration << ",\"dual_history\":[";
    for (std::size_t i = 0; i < history.size(); ++i) { if (i) out << ','; out << std::setprecision(9) << history[i]; }
    out << "],\n\"timing_seconds\":{\"read\":" << read_seconds << ",\"prepare\":" << prepare_seconds
        << ",\"pricing\":" << price_seconds << ",\"total\":" << seconds(started) << "},\"threads\":" << threads << "\n}\n";
    if (!out) fail("result write failed");
    if (saving) save_prices(args[8], minimum, levels, best);
    std::cout << "RLLB n=" << n << " trails=" << trails.size() << " Q=" << charge
              << " U<=" << overlap << " J>=" << joining << " L>=" << length
              << " restricted_reject=" << (length >= target ? "yes" : "no")
              << " prepare_seconds=" << prepare_seconds << " pricing_seconds=" << price_seconds << '\n';
    return 0;
}
} // namespace
int main(int argc, char** argv) {
    try { return run(argc, argv); }
    catch (const std::exception& error) { std::cerr << "rllb: " << error.what() << '\n'; return 1; }
}
