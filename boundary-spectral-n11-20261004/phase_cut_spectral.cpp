// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Theo H.
// Distributed without warranty; see the repository LICENSE for full terms.

// Expanded n=11 boundary family: every row's assigned-cycle starting phase is
// an allowed cut, not only the row head. Exact occupation is kept by a minimal
// wrapping prefix. Whole required cycles are still visited once; modules and
// their global order remain fixed. No claim of a global optimum.
#define BOUNDARY_TRANSFER_LIBRARY
#include "boundary_transfer.cpp"

// Spell a prefix of the infinite repetition of s, starting at the cyclic cut.
static std::string cyclicText(const std::string &s, size_t begin, size_t length) {
    require(!s.empty(), "nonempty period");
    std::string out;
    out.reserve(length);
    begin %= s.size();
    while (length) {
        size_t take = std::min(length, s.size() - begin);
        out.append(s, begin, take);
        length -= take;
        begin = 0;
    }
    return out;
}
static bool permutationFrame(const std::string &s) {
    auto x = s;
    std::sort(x.begin(), x.end());
    return x == alphabet.substr(0, 11);
}
// Course label, cyclic opening, and coverage-preserving wrapping prefix length.
struct PhasePort {
    int colour;
    size_t cut;
    int pad;
};
// Expand each selected course into its constituent-cycle openings.
// first/last are literal length-n boundaries; colourOfPort identifies ownership.
// A piece contains one period plus the minimal wrapping prefix for its cut.
// entryCost and exitCost include fixed outside attachments.
struct CoursePhaseModel {
    int n = 11, h = 11, courseCount = 0, portCount = 0, boundaryKeyCount = 0, maxStep = 20;
    uint64_t periodSum = 0;
    std::vector<std::string> periods, first, last;
    std::vector<PhasePort> port;
    std::vector<int> entryCost, exitCost, colourOfPort, colourSize;
    std::vector<std::array<int, 11>> prefixKeys, suffixKeys;
    CoursePhaseModel(const RowModel &m, const std::vector<int> &vs, const std::string &left,
                     const std::string &right) {
        std::map<int, int> root;
        for (int v : vs) {
            root.emplace(m.colour[v], v);
        }
        for (auto [rootId, start] : root) {
            (void)rootId;
            int colour = courseCount++;
            std::string text = m.head[start];
            std::vector<size_t> cuts, assigned;
            std::vector<int> pads;
            uint64_t offset = 0;
            int at = start;
            do {
                const auto &w = m.payload[at];
                int visible = int((w.size() - (m.n - 2)) / (m.n + 1));
                require(w.size() == size_t((m.n + 1) * visible + m.n - 2),
                        "visible length identity");
                for (int j = 0; j < visible; ++j) {
                    cuts.push_back(offset + size_t(j) * (m.n + 1));
                    pads.push_back(j ? m.n - 2 : m.h);
                    for (int i = 0; i < m.n; ++i) {
                        assigned.push_back(offset + size_t(j) * (m.n + 1) + i);
                    }
                }
                text += w.substr(m.h);
                offset += w.size() - m.h;
                at = m.next[at];
            } while (at != start);
            require(text.size() == offset + m.h && text.compare(offset, m.h, text, 0, m.h) == 0,
                    "cyclic literal closure");
            text.resize(offset);
            require(std::is_sorted(assigned.begin(), assigned.end()) &&
                        std::adjacent_find(assigned.begin(), assigned.end()) == assigned.end() &&
                        assigned.back() < offset,
                    "assigned starts partition");
            periodSum += offset;
            periods.push_back(std::move(text));
            colourSize.push_back(int(cuts.size()));
            for (size_t j = 0; j < cuts.size(); ++j) {
                size_t cut = cuts[j];
                auto it = std::lower_bound(assigned.begin(), assigned.end(), cut);
                size_t before = it == assigned.begin() ? assigned.back() : *std::prev(it);
                size_t backward = (cut + offset - before) % offset;
                require(backward > 0 && backward <= size_t(m.n), "preceding assigned window");
                // Rotation places this preceding designated window last.
                // Append enough symbols across the cut to complete it.
                int pad = m.n - int(backward);
                require(pad == pads[j], "minimum occupation-preserving wrapping prefix");
                port.push_back({colour, cut, pad});
                colourOfPort.push_back(colour);
                first.push_back(cyclicText(periods.back(), cut, m.n));
                last.push_back(
                    cyclicText(periods.back(), (cut + offset + pad - m.n) % offset, m.n));
                require(permutationFrame(first.back()) && permutationFrame(last.back()),
                        "literal phase boundary permutations");
                entryCost.push_back(m.n + pad - literalOverlap(left, first.back()));
                exitCost.push_back(m.n - literalOverlap(last.back(), right));
            }
        }
        portCount = int(port.size());
        require(courseCount >= 2 && courseCount <= 8, "n=11 selected module size");
        std::unordered_map<uint64_t, int> keys;
        keys.reserve(size_t(portCount) * 18);
        auto key = [&](uint64_t x) { return keys.emplace(x, int(keys.size())).first->second; };
        prefixKeys.resize(portCount);
        suffixKeys.resize(portCount);
        std::unordered_map<uint64_t, int> firstColour;
        firstColour.reserve(portCount * 2);
        for (int v = 0; v < portCount; ++v) {
            require(firstColour.emplace(boundaryKey(first[v], 0, n), colourOfPort[v]).second,
                    "distinct assigned entry permutations");
            for (int k = 0; k < n; ++k) {
                prefixKeys[v][k] = key(boundaryKey(first[v], 0, k));
                suffixKeys[v][k] = key(boundaryKey(last[v], n - k, k));
            }
        }
        for (int v = 0; v < portCount; ++v) {
            auto it = firstColour.find(boundaryKey(last[v], 0, n));
            require(it == firstColour.end() || it->second == colourOfPort[v],
                    "full-frame overlap cannot cross occupation colours");
        }
        boundaryKeyCount = int(keys.size());
    }
    int distance(int u, int v) const {
        return n + port[v].pad - literalOverlap(last[u], first[v]);
    }
    std::string piece(int v) const {
        const auto &p = port[v];
        return cyclicText(periods[p.colour], p.cut, periods[p.colour].size() + p.pad);
    }
};
struct PhaseAnswer {
    int objective = 0;
    std::vector<int> path;
};
// Subset DP over course ownership and final opening. Boundary keys aggregate
// equivalent seams; optional parents recover a literal witness. The constructor
// proves that full-frame overlaps cannot connect different courses here.
static PhaseAnswer phaseMinimum(const CoursePhaseModel &model, bool witness = true) {
    int allCourses = (1 << model.courseCount) - 1, unreachable = 30000;
    size_t cells = size_t(allCourses + 1) * model.portCount;
    require(cells < UINT32_MAX, "predecessor index");
    std::vector<int16_t> costByState(cells, unreachable);
    std::vector<uint32_t> parent(witness ? cells : 0, UINT32_MAX), owner(model.boundaryKeyCount);
    std::vector<int> costByBoundary(model.boundaryKeyCount, unreachable);
    for (int v = 0; v < model.portCount; ++v) {
        costByState[size_t(1 << model.colourOfPort[v]) * model.portCount + v] = model.entryCost[v];
    }
    for (int mask = 1; mask < allCourses; ++mask) {
        std::fill(costByBoundary.begin(), costByBoundary.end(), unreachable);
        for (int u = 0; u < model.portCount; ++u) {
            if (mask & (1 << model.colourOfPort[u])) {
                uint32_t index = uint32_t(size_t(mask) * model.portCount + u);
                int value = costByState[index];
                if (value == unreachable) {
                    continue;
                }
                for (int k = 0; k < model.n; ++k) {
                    int key = model.suffixKeys[u][k], candidate = value + model.n - k;
                    if (candidate < costByBoundary[key]) {
                        costByBoundary[key] = candidate;
                        owner[key] = index;
                    }
                }
            }
        }
        for (int v = 0; v < model.portCount; ++v) {
            if (!(mask & (1 << model.colourOfPort[v]))) {
                int best = unreachable;
                uint32_t before = UINT32_MAX;
                for (int k = 0; k < model.n; ++k) {
                    int key = model.prefixKeys[v][k];
                    if (costByBoundary[key] < best) {
                        best = costByBoundary[key];
                        before = owner[key];
                    }
                }
                size_t index = size_t(mask | (1 << model.colourOfPort[v])) * model.portCount + v;
                costByState[index] = int16_t(best + model.port[v].pad);
                if (witness) {
                    parent[index] = before;
                }
            }
        }
    }
    PhaseAnswer answer;
    answer.objective = unreachable;
    uint32_t at = UINT32_MAX;
    for (int v = 0; v < model.portCount; ++v) {
        uint32_t index = uint32_t(size_t(allCourses) * model.portCount + v);
        int a = costByState[index] + model.exitCost[v];
        if (a < answer.objective) {
            answer.objective = a;
            at = index;
        }
    }
    if (witness) {
        for (; at != UINT32_MAX; at = parent[at]) {
            answer.path.push_back(at % model.portCount);
        }
        std::reverse(answer.path.begin(), answer.path.end());
        require(answer.path.size() == size_t(model.courseCount), "complete colour path");
    }
    return answer;
}
// Existing small-instance oracle: enumerate predecessor openings directly.
static int phaseDenseMinimum(const CoursePhaseModel &p) {
    require(p.portCount <= 1000, "dense control guard");
    int allCourses = (1 << p.courseCount) - 1, unreachable = 30000;
    std::vector<uint8_t> cost(size_t(p.portCount) * p.portCount);
    for (int u = 0; u < p.portCount; ++u) {
        for (int v = 0; v < p.portCount; ++v) {
            cost[size_t(u) * p.portCount + v] = p.distance(u, v);
        }
    }
    std::vector<int16_t> costByState(size_t(allCourses + 1) * p.portCount, unreachable);
    for (int v = 0; v < p.portCount; ++v) {
        costByState[size_t(1 << p.colourOfPort[v]) * p.portCount + v] = p.entryCost[v];
    }
    for (int mask = 1; mask < allCourses; ++mask) {
        for (int u = 0; u < p.portCount; ++u) {
            if (mask & (1 << p.colourOfPort[u])) {
                int value = costByState[size_t(mask) * p.portCount + u];
                if (value == unreachable) {
                    continue;
                }
                for (int v = 0; v < p.portCount; ++v) {
                    if (!(mask & (1 << p.colourOfPort[v]))) {
                        auto &to =
                            costByState[size_t(mask | (1 << p.colourOfPort[v])) * p.portCount + v];
                        to = std::min(int(to), value + cost[size_t(u) * p.portCount + v]);
                    }
                }
            }
        }
    }
    int best = unreachable;
    for (int v = 0; v < p.portCount; ++v) {
        best =
            std::min(best, int(costByState[size_t(allCourses) * p.portCount + v]) + p.exitCost[v]);
    }
    return best;
}
// Count feasible course orders and opening choices by exact total cost.
static std::vector<I128> phasePolynomial(const CoursePhaseModel &p) {
    int full = (1 << p.courseCount) - 1, D = p.maxStep * p.courseCount + p.n, W = D + 1;
    size_t cells = size_t(full + 1) * p.portCount * W;
    require(cells <= 2500000000ULL / sizeof(I128), "exact phase polynomial RAM guard");
    std::vector<I128> d(cells), bucket(size_t(p.boundaryKeyCount) * W);
    for (int v = 0; v < p.portCount; ++v) {
        d[(size_t(1 << p.colourOfPort[v]) * p.portCount + v) * W + p.entryCost[v]] = 1;
    }
    for (int mask = 1; mask < full; ++mask) {
        int top = p.maxStep * __builtin_popcount(unsigned(mask));
        std::fill(bucket.begin(), bucket.end(), 0);
        for (int u = 0; u < p.portCount; ++u) {
            if (mask & (1 << p.colourOfPort[u])) {
                const I128 *from = &d[(size_t(mask) * p.portCount + u) * W];
                for (int k = 0; k < p.n; ++k) {
                    I128 *to = &bucket[size_t(p.suffixKeys[u][k]) * W];
                    for (int j = 0; j <= top; ++j) {
                        if (from[j]) {
                            to[j] = addChecked(to[j], from[j]);
                        }
                    }
                }
            }
        }
        const I128 *base = &bucket[size_t(p.prefixKeys[0][0]) * W];
        for (int v = 0; v < p.portCount; ++v) {
            if (!(mask & (1 << p.colourOfPort[v]))) {
                I128 *to = &d[(size_t(mask | (1 << p.colourOfPort[v])) * p.portCount + v) * W];
                for (int j = 0; j <= top; ++j) {
                    I128 remaining = base[j];
                    int pad = p.port[v].pad;
                    for (int k = 1; k < p.n; ++k) {
                        I128 count = bucket[size_t(p.prefixKeys[v][k]) * W + j];
                        require(remaining >= count, "phase overlap exclusion");
                        remaining -= count;
                        if (count) {
                            to[j + p.n + pad - k] = addChecked(to[j + p.n + pad - k], count);
                        }
                    }
                    if (remaining) {
                        to[j + p.n + pad] = addChecked(to[j + p.n + pad], remaining);
                    }
                }
            }
        }
    }
    std::vector<I128> P(W);
    for (int v = 0; v < p.portCount; ++v) {
        for (int j = 0; j <= D - p.exitCost[v]; ++j) {
            P[j + p.exitCost[v]] =
                addChecked(P[j + p.exitCost[v]], d[(size_t(full) * p.portCount + v) * W + j]);
        }
    }
    I128 total = 0, expected = 1;
    for (int s : p.colourSize) {
        require(U128(expected) <= maxSigned / U128(s), "phase path count bound");
        expected *= s;
    }
    for (int j = 2; j <= p.courseCount; ++j) {
        require(U128(expected) <= maxSigned / U128(j), "phase order count bound");
        expected *= j;
    }
    for (I128 x : P) {
        total = addChecked(total, x);
    }
    require(total == expected, "phase exact total path count");
    return P;
}
static void phaseApply(const CoursePhaseModel &p, long double z, const std::vector<long double> &x,
                       std::vector<long double> &y) {
    int full = (1 << p.courseCount) - 1;
    std::fill(y.begin(), y.end(), 0);
    y[0] = x[1];
    std::vector<long double> powers(2 * p.n + 1, 1);
    for (size_t j = 1; j < powers.size(); ++j) {
        powers[j] = powers[j - 1] * z;
    }
    for (int v = 0; v < p.portCount; ++v) {
        y[2 + size_t(1 << p.colourOfPort[v]) * p.portCount + v] = x[0] * powers[p.entryCost[v]];
    }
    std::vector<long double> bucket(p.boundaryKeyCount);
    for (int mask = 1; mask < full; ++mask) {
        std::fill(bucket.begin(), bucket.end(), 0);
        for (int u = 0; u < p.portCount; ++u) {
            if (mask & (1 << p.colourOfPort[u])) {
                for (int k = 0; k < p.n; ++k) {
                    bucket[p.suffixKeys[u][k]] += x[2 + size_t(mask) * p.portCount + u];
                }
            }
        }
        long double base = bucket[p.prefixKeys[0][0]];
        for (int v = 0; v < p.portCount; ++v) {
            if (!(mask & (1 << p.colourOfPort[v]))) {
                long double remaining = base, value = 0;
                int pad = p.port[v].pad;
                for (int k = 1; k < p.n; ++k) {
                    long double a = bucket[p.prefixKeys[v][k]];
                    remaining -= a;
                    value += a * powers[p.n + pad - k];
                }
                value += remaining * powers[p.n + pad];
                y[2 + size_t(mask | (1 << p.colourOfPort[v])) * p.portCount + v] = value;
            }
        }
    }
    for (int v = 0; v < p.portCount; ++v) {
        y[1] += x[2 + size_t(full) * p.portCount + v] * powers[p.exitCost[v]];
    }
}
static Numeric phaseNumerical(const CoursePhaseModel &p, const std::vector<I128> &P,
                              long double z) {
    Numeric a;
    a.rho = std::pow(evaluate(P, z), 1.L / (p.courseCount + 2));
    size_t N = 2 + (size_t(1) << p.courseCount) * p.portCount;
    std::vector<long double> x(N), y(N);
    x[0] = 1;
    for (int j = 0; j < p.courseCount + 2; ++j) {
        phaseApply(p, z, x, y);
        x.swap(y);
    }
    long double value = evaluate(P, z);
    a.krylovError = std::abs(x[0] - value) / value;
    for (size_t j = 1; j < N; ++j) {
        require(std::abs(x[j]) < 1e-15L * value, "phase Krylov support");
    }
    x.assign(N, 0);
    x[0] = 1;
    for (int iter = 1; iter <= 1600; ++iter) {
        phaseApply(p, z, x, y);
        long double norm = 0;
        for (size_t j = 0; j < N; ++j) {
            y[j] = x[j] + y[j] / a.rho;
            norm += std::abs(y[j]);
        }
        long double delta = 0;
        for (size_t j = 0; j < N; ++j) {
            y[j] /= norm;
            delta += std::abs(y[j] - x[j]);
        }
        x.swap(y);
        a.iterations = iter;
        if (delta < 1e-14L) {
            break;
        }
    }
    phaseApply(p, z, x, y);
    long double sx = 0, sy = 0;
    for (size_t j = 0; j < N; ++j) {
        sx += x[j];
        sy += y[j];
    }
    a.measured = sy / sx;
    long double err = 0;
    for (size_t j = 0; j < N; ++j) {
        err += std::abs(y[j] - a.rho * x[j]);
    }
    a.residual = err / (a.rho * sx);
    require(a.residual < 1e-10L && a.krylovError < 1e-10L, "phase numerical spectral agreement");
    return a;
}
static std::string phaseReplacement(const CoursePhaseModel &p, const PhaseAnswer &a) {
    std::string piece;
    std::set<int> colours;
    for (int v : a.path) {
        require(colours.insert(p.colourOfPort[v]).second, "phase colour used once");
        auto word = p.piece(v);
        require(word.substr(0, p.n) == p.first[v] && word.substr(word.size() - p.n) == p.last[v],
                "expanded literal port frames");
        int overlap =
            piece.empty() ? 0 : literalOverlap(piece.substr(piece.size() - p.n), p.first[v]);
        piece += word.substr(overlap);
    }
    require(colours.size() == size_t(p.courseCount), "expanded occupation complete");
    return piece;
}
static uint64_t joinedLength(const std::vector<std::string> &pieces) {
    uint64_t L = 0;
    for (size_t j = 0; j < pieces.size(); ++j) {
        L += pieces[j].size() - (j ? literalOverlap(pieces[j - 1].substr(pieces[j - 1].size() - 11),
                                                    pieces[j].substr(0, 11))
                                   : 0);
    }
    return L;
}
// Join certified pieces using maximal literal boundary overlaps.
static std::string joinedWord(const std::vector<std::string> &pieces) {
    std::string word;
    word.reserve(joinedLength(pieces));
    for (const auto &piece : pieces) {
        int k =
            word.empty() ? 0 : literalOverlap(word.substr(word.size() - 11), piece.substr(0, 11));
        word += piece.substr(k);
    }
    return word;
}
#ifndef PHASE_SPECTRAL_LIBRARY
int main(int argc, char **argv) try {
    require(argc == 6,
            "usage: phase_cut_spectral ROWS CIRCLES WHOLE_ROW_WORD FRESH_OUT MAX_PASSES");
    std::filesystem::path out(argv[4]);
    require(!std::filesystem::exists(out), "fresh phase output");
    std::filesystem::create_directories(out);
    RowModel m;
    m.load(argv[1], argv[2]);
    Scan original = scan(m, argv[3]);
    require(!original.missing && !original.multiple && !original.interleaved,
            "whole-row initial control");
    std::vector<std::string> pieces;
    for (int id : original.order) {
        auto [a, b] = original.intervals.at(id);
        pieces.push_back(original.word.substr(a, b - a));
    }
    require(joinedWord(pieces) == original.word, "exact baseline module/frame reconstruction");
    std::ofstream log(out / "coordinate.jsonl"), metrics(out / "phase-ports.jsonl");
    int changes = 0, passes = 0;
    uint64_t allPorts = 0;
    double spectralSeconds = 0;
    auto started = std::chrono::steady_clock::now();
    int maxPasses = std::stoi(argv[5]);
    require(maxPasses >= 1 && maxPasses <= 10, "bounded passes");
    for (int pass = 1; pass <= maxPasses; ++pass) {
        int gains = 0;
        for (size_t j = 0; j < pieces.size(); ++j) {
            int id = original.order[j];
            std::string left = j ? pieces[j - 1].substr(pieces[j - 1].size() - 11) : "";
            std::string right = j + 1 < pieces.size() ? pieces[j + 1].substr(0, 11) : "";
            CoursePhaseModel p(m, m.modules.at(id), left, right);
            auto answer = phaseMinimum(p);
            int64_t constant = int64_t(p.periodSum) - p.n * (p.courseCount + 1),
                    candidate = constant + answer.objective;
            int64_t before = int64_t(pieces[j].size()) -
                             literalOverlap(left, pieces[j].substr(0, 11)) -
                             literalOverlap(pieces[j].substr(pieces[j].size() - 11), right);
            if (pass == 1) {
                allPorts += p.portCount;
                metrics << "{\"position\":" << j << ",\"module\":" << id
                        << ",\"colours\":" << p.courseCount << ",\"phase_ports\":" << p.portCount
                        << ",\"occupation_dimension\":"
                        << (2 + uint64_t(p.portCount) * (uint64_t(1) << (p.courseCount - 1)))
                        << ",\"scalar_spectral_block\":" << p.courseCount + 2
                        << ",\"minimum_adjusted_exponent\":" << answer.objective
                        << ",\"current_two_terminal_cost\":" << before
                        << ",\"optimal_two_terminal_cost\":" << candidate << "}\n";
                metrics.flush();
            }
            if (pass == 1 && j == 0) {
                require(answer.objective == phaseDenseMinimum(p), "phase dense min-plus control");
                auto timer = std::chrono::steady_clock::now();
                auto P = phasePolynomial(p);
                int lo = 0, hi = int(P.size()) - 1;
                while (!P[lo]) {
                    ++lo;
                }
                while (!P[hi]) {
                    --hi;
                }
                require(lo == answer.objective,
                        "phase coefficient extraction agrees with exact shortest path");
                std::ofstream f(out / "phase-polynomial.json");
                f << "{\"module\":" << id << ",\"constant\":" << constant
                  << ",\"minimum_exponent\":" << lo << ",\"degree\":" << hi
                  << ",\"coefficients\":[";
                for (size_t k = 0; k < P.size(); ++k) {
                    if (k) {
                        f << ',';
                    }
                    f << '"' << decimal(U128(P[k])) << '"';
                }
                f << "]}\n";
                std::ofstream ns(out / "phase-spectrum.json");
                auto num = phaseNumerical(p, P, 0.8L);
                ns << std::setprecision(20) << "{\"z\":0.8,\"analytic_perron_root\":" << num.rho
                   << ",\"unreduced_numeric_perron_root\":" << num.measured
                   << ",\"relative_residual\":" << num.residual
                   << ",\"krylov_relative_error\":" << num.krylovError
                   << ",\"iterations\":" << num.iterations << "}\n";
                spectralSeconds =
                    std::chrono::duration<double>(std::chrono::steady_clock::now() - timer).count();
            }
            if (candidate < before) {
                auto replacement = phaseReplacement(p, answer);
                int64_t realized =
                    int64_t(replacement.size()) - literalOverlap(left, replacement.substr(0, 11)) -
                    literalOverlap(replacement.substr(replacement.size() - 11), right);
                require(realized == candidate, "phase exact literal objective");
                uint64_t oldLength = joinedLength(pieces);
                pieces[j] = std::move(replacement);
                uint64_t newLength = joinedLength(pieces);
                require(int64_t(newLength) - int64_t(oldLength) == candidate - before,
                        "two-terminal global length identity");
                ++gains;
                ++changes;
                log << "{\"pass\":" << pass << ",\"position\":" << j << ",\"module\":" << id
                    << ",\"saving\":" << before - candidate << ",\"length\":" << newLength << "}\n";
                log.flush();
            }
            if (j % 25 == 0) {
                std::cout << "phase_pass=" << pass << " modules=" << j + 1
                          << " length=" << joinedLength(pieces) << " seconds="
                          << std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                                           started)
                                 .count()
                          << std::endl;
            }
        }
        passes = pass;
        if (!gains) {
            break;
        }
    }
    auto word = joinedWord(pieces);
    require(word.size() == joinedLength(pieces), "final word ledger");
    std::string filename = "n11-" + std::to_string(word.size()) + ".txt";
    std::ofstream output(out / filename, std::ios::binary);
    output << word;
    require(bool(output), "phase output word");
    // Preserve the actual new pieces, including the altered open connector.
    // Two four-bit symbols per byte; a final unused nibble is 15. The index
    // retains exact lengths so the literal cut audit needs no old row parsing.
    std::ofstream packed(out / "pieces.nibbles", std::ios::binary), index(out / "pieces-index.txt");
    index << "PIECES_NIBBLE_V1 11 " << pieces.size() << '\n';
    uint64_t byteOffset = 0;
    for (size_t j = 0; j < pieces.size(); ++j) {
        const auto &s = pieces[j];
        index << original.order[j] << ' ' << byteOffset << ' ' << s.size() << '\n';
        for (size_t k = 0; k < s.size(); k += 2) {
            int a = int(alphabet.find(s[k])),
                b = k + 1 < s.size() ? int(alphabet.find(s[k + 1])) : 15;
            packed.put(char((a << 4) | b));
        }
        byteOffset += (s.size() + 1) / 2;
    }
    require(bool(packed) && bool(index), "packed literal pieces");
    std::ofstream result(out / "result.json");
    result << "{\"n\":11,\"baseline_length\":" << original.length << ",\"length\":" << word.size()
           << ",\"modules\":" << pieces.size() << ",\"phase_ports\":" << allPorts
           << ",\"coordinate_passes\":" << passes << ",\"accepted_changes\":" << changes
           << ",\"spectral_seconds\":" << spectralSeconds << ",\"seconds\":"
           << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
           << ",\"fixed_module_order\":true,\"whole_cycles_once\":true,\"independent_scan_"
              "required\":true}\n";
    std::cout << "phase_final_length=" << word.size() << " changes=" << changes << std::endl;
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
#endif
