// Exact n=11 two-terminal polynomial transfer and boundary-closed spectrum.
// This deliberately names its restriction: fixed modules, whole required
// cycles visited once, arbitrary cycle order and ports, fixed outside frames.
// It is NOT an enumeration of all n=11 superpermutations or arbitrary row cuts.
#define main upstream_construct_main
#include "construct.cpp"
#undef main
#include <cmath>
#include <complex>
#include <filesystem>
#include <iomanip>
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <unordered_map>

using I128 = __int128;
using U128 = unsigned __int128;
static constexpr U128 maxSigned = (U128(1) << 127) - 1;
static std::string decimal(U128 x) {
    if (!x) {
        return "0";
    }
    std::string s;
    while (x) {
        s.push_back(char('0' + x % 10));
        x /= 10;
    }
    std::reverse(s.begin(), s.end());
    return s;
}
static I128 addChecked(I128 a, I128 b) {
    require(a >= 0 && b >= 0 && U128(a) <= maxSigned - U128(b), "count overflow");
    return a + b;
}
// Exact suffix-prefix overlap; an empty outside boundary contributes zero.
static int literalOverlap(const std::string &a, const std::string &b) {
    for (int k = int(std::min(a.size(), b.size())); k > 0; --k) {
        if (a.compare(a.size() - k, k, b, 0, k) == 0) {
            return k;
        }
    }
    return 0;
}
// The leading 1 distinguishes lengths even when the boundary begins with zero.
// Each following symbol occupies four bits.
static uint64_t boundaryKey(const std::string &s, int from, int length) {
    uint64_t x = 1;
    for (int j = 0; j < length; ++j) {
        x = (x << 4) | alphabet.find(s[from + j]);
    }
    return x;
}
// Matching length-h row heads and tails defines successor cycles (courses).
// colour identifies a course; module joins courses through connector circles.
// payload spells each row, and next/prev locate its cyclic neighbors.
struct RowModel {
    int n = 11, h = 8;
    std::vector<std::string> payload, head, lastFrame;
    std::vector<int> next, prev, colour, module;
    std::map<int, std::vector<int>> modules;
    std::unordered_map<uint64_t, int> ids;
    void load(const char *rowfile, const char *circlefile) {
        std::ifstream in(rowfile);
        std::string magic, s;
        int degree;
        size_t nr;
        require(bool(in >> magic >> degree >> nr) && magic == "MACROV1" && degree == 11,
                "n=11 rows");
        payload.reserve(nr);
        head.reserve(nr);
        ids.reserve(nr * 2);
        for (size_t j = 0; j < nr; ++j) {
            int sat, v;
            require(bool(in >> s >> sat >> v), "row input");
            auto w = row_word({parse(s), uint8_t(sat), v});
            std::string text;
            for (auto x : w) {
                text += alphabet[x];
            }
            payload.push_back(std::move(text));
            head.push_back(payload.back().substr(0, h));
            require(ids.emplace(boundaryKey(head.back(), 0, h), int(j)).second, "unique heads");
        }
        require(!(in >> s), "trailing rows");
        DSU base(nr), joined(nr);
        next.resize(nr);
        prev.assign(nr, -1);
        for (size_t j = 0; j < nr; ++j) {
            auto &t = payload[j];
            auto it = ids.find(boundaryKey(t, int(t.size()) - h, h));
            require(it != ids.end(), "row successor");
            next[j] = it->second;
            require(prev[next[j]] == -1, "row predecessor");
            prev[next[j]] = int(j);
            base.join(j, next[j]);
            joined.join(j, next[j]);
        }
        std::ifstream circles(circlefile);
        require(bool(circles), "circle file");
        while (circles >> s) {
            require(s.size() == size_t(h), "circle shape");
            int first = -1;
            for (int k = 0; k < h; ++k) {
                auto it = ids.find(boundaryKey(s, 0, h));
                if (it != ids.end()) {
                    if (first < 0) {
                        first = it->second;
                    } else {
                        joined.join(first, it->second);
                    }
                }
                std::rotate(s.begin(), s.begin() + 1, s.end());
            }
        }
        colour.resize(nr);
        module.resize(nr);
        lastFrame.resize(nr);
        for (size_t j = 0; j < nr; ++j) {
            colour[j] = base.find(j);
            module[j] = joined.find(j);
            modules[module[j]].push_back(int(j));
            const auto &t = payload[prev[j]];
            lastFrame[j] = t.substr(t.size() - n);
        }
    }
};
struct Scan {
    uint64_t length = 0;
    int missing = 0, multiple = 0, interleaved = 0;
    std::vector<int> order;
    std::map<int, std::pair<size_t, size_t>> intervals;
    std::string word;
};
static Scan scan(const RowModel &m, const char *path) {
    std::ifstream in(path, std::ios::binary);
    require(bool(in), "word file");
    Scan s;
    s.word = std::string((std::istreambuf_iterator<char>(in)), {});
    while (!s.word.empty() && (s.word.back() == '\n' || s.word.back() == '\r')) {
        s.word.pop_back();
    }
    s.length = s.word.size();
    for (char c : s.word) {
        require(alphabet.find(c) < 11, "word alphabet");
    }
    std::vector<int> seen(m.payload.size());
    int last = -1;
    std::set<int> finished;
    for (size_t p = 0; p + m.h <= s.word.size();) {
        auto it = m.ids.find(boundaryKey(s.word, int(p), m.h));
        if (it != m.ids.end() &&
            s.word.compare(p, m.payload[it->second].size(), m.payload[it->second]) == 0) {
            int j = it->second, g = m.module[j];
            ++seen[j];
            if (g != last) {
                if (last >= 0) {
                    finished.insert(last);
                }
                if (finished.count(g)) {
                    ++s.interleaved;
                }
                s.order.push_back(g);
                last = g;
            }
            auto jt = s.intervals.find(g);
            if (jt == s.intervals.end()) {
                s.intervals[g] = {p, p + m.payload[j].size()};
            } else {
                jt->second.second = p + m.payload[j].size();
            }
            p += m.payload[j].size() - m.h;
        } else {
            ++p;
        }
    }
    for (size_t j = 0; j < seen.size(); ++j) {
        // Certify absence of every missing greedy row against the ENTIRE word.
        if (!seen[j] && s.word.find(m.payload[j]) == std::string::npos) {
            ++s.missing;
        }
        s.multiple += seen[j] > 1;
    }
    return s;
}
// A port chooses a row head at which to open a course. entryCost/exitCost
// include outside attachments. Interned prefix/suffix keys group equal seams
// for sparse transitions without a quadratic port-to-port matrix.
struct BoundaryPortModel {
    int courseCount = 0, portCount = 0, h = 8, n = 11, boundaryKeyCount = 0;
    std::vector<int> globalRows, colourOfPort, entryCost, exitCost;
    std::vector<std::string> heads, ends;
    std::vector<std::array<int, 9>> prefixKeys, suffixKeys;
    std::vector<std::vector<int>> prefTargets;
    std::vector<int> colourSize;
    BoundaryPortModel(const RowModel &m, const std::vector<int> &vs, const std::string &left,
                      const std::string &right)
        : globalRows(vs) {
        portCount = int(vs.size());
        std::map<int, int> names;
        for (int v : vs) {
            names.emplace(m.colour[v], 0);
        }
        for (auto &x : names) {
            x.second = courseCount++;
        }
        colourSize.resize(courseCount);
        prefixKeys.resize(portCount);
        suffixKeys.resize(portCount);
        std::unordered_map<uint64_t, int> keys;
        keys.reserve(size_t(portCount) * 16);
        auto id = [&](uint64_t x) {
            auto it = keys.emplace(x, int(keys.size())).first;
            return it->second;
        };
        for (int v : vs) {
            colourOfPort.push_back(names.at(m.colour[v]));
            ++colourSize[colourOfPort.back()];
            heads.push_back(m.head[v]);
            ends.push_back(m.lastFrame[v]);
            entryCost.push_back(n - literalOverlap(left, m.payload[v].substr(0, n)));
            exitCost.push_back(n - literalOverlap(m.lastFrame[v], right));
        }
        for (int v = 0; v < portCount; ++v) {
            for (int k = 0; k <= h; ++k) {
                prefixKeys[v][k] = id(boundaryKey(heads[v], 0, k));
                suffixKeys[v][k] = id(boundaryKey(heads[v], h - k, k));
            }
        }
        boundaryKeyCount = int(keys.size());
        prefTargets.resize(boundaryKeyCount);
        for (int v = 0; v < portCount; ++v) {
            for (int k = 1; k < h; ++k) {
                prefTargets[prefixKeys[v][k]].push_back(v);
            }
        }
    }
    int distance(int u, int v) const {
        return h - literalOverlap(heads[u], heads[v]);
    }
};
struct Quotient {
    int blocks = 0, rounds = 0;
    bool stable = false;
    std::vector<int> label;
};
// Exact colour-respecting polynomial strong lumpability, relative to fixed
// terminal weights. A sparse signature stores positive-overlap counts. Other
// edges all have cost h, whose multiplicity is inferred from block sizes.
static Quotient refine(const BoundaryPortModel &p, int blockCap) {
    Quotient q;
    q.label.resize(p.portCount);
    std::map<std::pair<int, int>, int> initial;
    for (int v = 0; v < p.portCount; ++v) {
        auto it =
            initial.emplace(std::make_pair(p.colourOfPort[v], p.exitCost[v]), int(initial.size()))
                .first;
        q.label[v] = it->second;
    }
    q.blocks = int(initial.size());
    for (int round = 0; round < 30; ++round) {
        std::vector<std::vector<std::pair<int, int>>> channels(p.boundaryKeyCount);
        for (int k = 0; k < p.boundaryKeyCount; ++k) {
            if (!p.prefTargets[k].empty()) {
                std::map<int, int> counts;
                for (int v : p.prefTargets[k]) {
                    ++counts[q.label[v]];
                }
                channels[k].assign(counts.begin(), counts.end());
            }
        }
        std::map<std::vector<int>, int> signatures;
        std::vector<int> next(p.portCount);
        // Same-colour moves are never permitted.
        std::vector<int> blockColour(q.blocks, -1);
        for (int v = 0; v < p.portCount; ++v) {
            blockColour[q.label[v]] = p.colourOfPort[v];
        }
        for (int u = 0; u < p.portCount; ++u) {
            std::vector<int> key{q.label[u]};
            for (int k = 1; k < p.h; ++k) {
                key.push_back(-k);
                for (auto [b, count] : channels[p.suffixKeys[u][k]]) {
                    if (blockColour[b] != p.colourOfPort[u]) {
                        key.push_back(b);
                        key.push_back(count);
                    }
                }
            }
            next[u] = int(signatures.emplace(std::move(key), int(signatures.size())).first->second);
        }
        int nb = int(signatures.size());
        ++q.rounds;
        if (nb == q.blocks) {
            q.stable = true;
            return q;
        }
        q.label = std::move(next);
        q.blocks = nb;
        if (nb > blockCap) {
            return q;
        }
    }
    return q;
}
// costByState[mask, port] visits exactly mask's courses and ends at port.
// Publish predecessor costs by suffix, then query matching prefixes.
static int minimum(const BoundaryPortModel &p) {
    int allCourses = (1 << p.courseCount) - 1, unreachable = 30000;
    std::vector<int16_t> costByState(size_t(allCourses + 1) * p.portCount, unreachable);
    std::vector<int> costByBoundary(p.boundaryKeyCount, unreachable);
    for (int v = 0; v < p.portCount; ++v) {
        costByState[size_t(1 << p.colourOfPort[v]) * p.portCount + v] = p.entryCost[v];
    }
    for (int mask = 1; mask < allCourses; ++mask) {
        std::fill(costByBoundary.begin(), costByBoundary.end(), unreachable);
        for (int v = 0; v < p.portCount; ++v) {
            if (mask & (1 << p.colourOfPort[v])) {
                int a = costByState[size_t(mask) * p.portCount + v];
                if (a == unreachable) {
                    continue;
                }
                for (int k = 0; k < p.h; ++k) {
                    costByBoundary[p.suffixKeys[v][k]] =
                        std::min(costByBoundary[p.suffixKeys[v][k]], a + p.h - k);
                }
            }
        }
        for (int v = 0; v < p.portCount; ++v) {
            if (!(mask & (1 << p.colourOfPort[v]))) {
                int a = unreachable;
                for (int k = 0; k < p.h; ++k) {
                    a = std::min(a, costByBoundary[p.prefixKeys[v][k]]);
                }
                costByState[size_t(mask | (1 << p.colourOfPort[v])) * p.portCount + v] = a;
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
// Exact coefficients, using 128-bit integers with a proved-by-checked-count
// upper guard. Every positive overlap is unique for two duplicate-free heads:
// the first symbol of the target cannot occur at two source positions.
static std::vector<I128> polynomial(const BoundaryPortModel &p, uint64_t memoryCap) {
    int full = (1 << p.courseCount) - 1, D = 2 * p.n + p.h * (p.courseCount - 1), W = D + 1;
    size_t cells = size_t(full + 1) * p.portCount * W;
    require(cells <= memoryCap / sizeof(I128), "polynomial memory guard");
    std::vector<I128> d(cells), bucket(size_t(p.boundaryKeyCount) * W);
    for (int v = 0; v < p.portCount; ++v) {
        d[(size_t(1 << p.colourOfPort[v]) * p.portCount + v) * W + p.entryCost[v]] = 1;
    }
    for (int mask = 1; mask < full; ++mask) {
        int top = p.n + p.h * (__builtin_popcount(unsigned(mask)) - 1);
        std::fill(bucket.begin(), bucket.end(), 0);
        for (int v = 0; v < p.portCount; ++v) {
            if (mask & (1 << p.colourOfPort[v])) {
                const I128 *from = &d[(size_t(mask) * p.portCount + v) * W];
                for (int k = 0; k < p.h; ++k) {
                    I128 *to = &bucket[size_t(p.suffixKeys[v][k]) * W];
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
                    for (int k = 1; k < p.h; ++k) {
                        I128 count = bucket[size_t(p.prefixKeys[v][k]) * W + j];
                        require(remaining >= count, "disjoint positive overlap channels");
                        remaining -= count;
                        if (count) {
                            to[j + p.h - k] = addChecked(to[j + p.h - k], count);
                        }
                    }
                    if (remaining) {
                        to[j + p.h] = addChecked(to[j + p.h], remaining);
                    }
                }
            }
        }
    }
    std::vector<I128> P(W);
    for (int v = 0; v < p.portCount; ++v) {
        for (int j = 0; j <= D - p.exitCost[v]; ++j) {
            I128 count = d[(size_t(full) * p.portCount + v) * W + j];
            if (count) {
                P[j + p.exitCost[v]] = addChecked(P[j + p.exitCost[v]], count);
            }
        }
    }
    I128 expected = 1;
    for (int s : p.colourSize) {
        require(U128(expected) <= maxSigned / U128(s), "path bound overflow");
        expected *= s;
    }
    for (int j = 2; j <= p.courseCount; ++j) {
        require(U128(expected) <= maxSigned / U128(j), "factorial overflow");
        expected *= j;
    }
    I128 total = 0;
    for (I128 x : P) {
        total = addChecked(total, x);
    }
    require(total == expected, "all order/port combinations counted");
    return P;
}
// Existing small-instance reference: enumerate every predecessor directly.
static std::vector<I128> densePolynomial(const BoundaryPortModel &p) {
    require(p.portCount <= 100, "dense audit bound");
    int full = (1 << p.courseCount) - 1, D = 2 * p.n + p.h * (p.courseCount - 1), W = D + 1;
    std::vector<I128> d(size_t(full + 1) * p.portCount * W);
    for (int v = 0; v < p.portCount; ++v) {
        d[(size_t(1 << p.colourOfPort[v]) * p.portCount + v) * W + p.entryCost[v]] = 1;
    }
    for (int mask = 1; mask < full; ++mask) {
        for (int u = 0; u < p.portCount; ++u) {
            if (mask & (1 << p.colourOfPort[u])) {
                for (int v = 0; v < p.portCount; ++v) {
                    if (!(mask & (1 << p.colourOfPort[v]))) {
                        int cost = p.distance(u, v);
                        for (int j = 0; j <= D - cost; ++j) {
                            I128 x = d[(size_t(mask) * p.portCount + u) * W + j];
                            if (x) {
                                auto &to =
                                    d[(size_t(mask | (1 << p.colourOfPort[v])) * p.portCount + v) *
                                          W +
                                      j + cost];
                                to = addChecked(to, x);
                            }
                        }
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
    return P;
}
static long double evaluate(const std::vector<I128> &P, long double z) {
    long double v = 0;
    for (auto it = P.rbegin(); it != P.rend(); ++it) {
        v = v * z + static_cast<long double>(*it);
    }
    return v;
}
// Apply the unreduced boundary-return operator. One reset edge connects the
// accepting terminal to the start; all accepted excursions have r+2 edges.
static void apply(const BoundaryPortModel &p, long double z, const std::vector<long double> &x,
                  std::vector<long double> &y) {
    int full = (1 << p.courseCount) - 1;
    size_t off = 2;
    std::fill(y.begin(), y.end(), 0);
    y[0] = x[1];
    std::vector<long double> powers(2 * p.n + 1, 1);
    for (size_t j = 1; j < powers.size(); ++j) {
        powers[j] = powers[j - 1] * z;
    }
    for (int v = 0; v < p.portCount; ++v) {
        y[off + size_t(1 << p.colourOfPort[v]) * p.portCount + v] = x[0] * powers[p.entryCost[v]];
    }
    std::vector<long double> bucket(p.boundaryKeyCount);
    for (int mask = 1; mask < full; ++mask) {
        std::fill(bucket.begin(), bucket.end(), 0);
        for (int u = 0; u < p.portCount; ++u) {
            if (mask & (1 << p.colourOfPort[u])) {
                for (int k = 0; k < p.h; ++k) {
                    bucket[p.suffixKeys[u][k]] += x[off + size_t(mask) * p.portCount + u];
                }
            }
        }
        long double base = bucket[p.prefixKeys[0][0]];
        for (int v = 0; v < p.portCount; ++v) {
            if (!(mask & (1 << p.colourOfPort[v]))) {
                long double remaining = base, value = 0;
                for (int k = 1; k < p.h; ++k) {
                    long double a = bucket[p.prefixKeys[v][k]];
                    remaining -= a;
                    value += a * powers[p.h - k];
                }
                value += remaining * powers[p.h];
                y[off + size_t(mask | (1 << p.colourOfPort[v])) * p.portCount + v] = value;
            }
        }
    }
    for (int v = 0; v < p.portCount; ++v) {
        y[1] += x[off + size_t(full) * p.portCount + v] * powers[p.exitCost[v]];
    }
}
struct Numeric {
    long double rho = 0, measured = 0, residual = 0, krylovError = 0;
    int iterations = 0;
};
// Check the polynomial-derived spectral radius against the explicitly applied
// boundary-return operator. Normalize iterates to avoid unbounded growth.
static Numeric numerical(const BoundaryPortModel &p, const std::vector<I128> &P, long double z) {
    Numeric a;
    a.rho = std::pow(evaluate(P, z), 1.L / (p.courseCount + 2));
    int full = (1 << p.courseCount) - 1;
    size_t N = 2 + size_t(full + 1) * p.portCount;
    std::vector<long double> x(N), y(N);
    x[0] = 1;
    for (int j = 0; j < p.courseCount + 2; ++j) {
        apply(p, z, x, y);
        x.swap(y);
    }
    long double val = evaluate(P, z);
    a.krylovError = std::abs(x[0] - val) / val;
    for (size_t j = 1; j < N; ++j) {
        require(std::abs(x[j]) < 1e-15L * val, "graded Krylov support");
    }
    x.assign(N, 0);
    x[0] = 1;
    for (int iter = 1; iter <= 1600; ++iter) {
        apply(p, z, x, y);
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
    apply(p, z, x, y);
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
    require(a.residual < 1e-10L && a.krylovError < 1e-10L, "spectral agreement");
    return a;
}
[[maybe_unused]] static int selfTest() {
    std::mt19937 rng(59054380);
    int cases = 0;
    for (int r = 2; r <= 5; ++r) {
        for (int trial = 0; trial < 5; ++trial) {
            RowModel m;
            std::set<std::string> heads;
            for (int c = 0; c < r; ++c) {
                for (int j = 0; j < 3; ++j) {
                    std::string frame = alphabet.substr(0, 11);
                    do {
                        std::shuffle(frame.begin(), frame.end(), rng);
                    } while (!heads.insert(frame.substr(0, 8)).second);
                    m.payload.push_back(frame);
                    m.head.push_back(frame.substr(0, 8));
                    m.colour.push_back(c);
                    std::reverse(frame.begin(), frame.end());
                    m.lastFrame.push_back(frame);
                }
            }
            std::vector<int> vs(m.payload.size());
            std::iota(vs.begin(), vs.end(), 0);
            BoundaryPortModel p(m, vs, trial % 2 ? alphabet.substr(0, 11) : "",
                                trial % 2 ? m.lastFrame.back() : "");
            auto P = polynomial(p, 100000000);
            require(P == densePolynomial(p), "random dense coefficient check");
            int lo = 0;
            while (!P[lo]) {
                ++lo;
            }
            require(lo == minimum(p), "random min-plus check");
            auto q = refine(p, p.portCount);
            require(q.stable, "random refinement termination");
            std::vector<std::vector<int>> signatures(q.blocks);
            for (int u = 0; u < p.portCount; ++u) {
                std::vector<int> key(size_t(q.blocks) * (p.h + 1));
                for (int v = 0; v < p.portCount; ++v) {
                    if (p.colourOfPort[u] != p.colourOfPort[v]) {
                        ++key[size_t(q.label[v]) * (p.h + 1) + p.distance(u, v)];
                    }
                }
                auto &saved = signatures[q.label[u]];
                if (saved.empty()) {
                    saved = key;
                } else {
                    require(saved == key, "dense strong lumpability audit");
                }
            }
            ++cases;
        }
    }
    std::cout << "{\"random_exact_cases\":" << cases
              << ",\"all_dense_polynomial_minplus_partition_checks_pass\":true}\n";
    return 0;
}
#ifndef BOUNDARY_SPECTRAL_LIBRARY
int main(int argc, char **argv) try {
    if (argc == 2 && std::string(argv[1]) == "--self-test") {
        return selfTest();
    }
    require(argc == 6,
            "usage: boundary_spectral ROWS CIRCLES WHOLE_ROW_WORD RECORD_WORD FRESH_OUT");
    std::filesystem::path out(argv[5]);
    require(!std::filesystem::exists(out), "fresh output");
    std::filesystem::create_directories(out);
    RowModel m;
    m.load(argv[1], argv[2]);
    Scan original = scan(m, argv[3]), record = scan(m, argv[4]);
    require(original.missing == 0 && original.multiple == 0 && original.interleaved == 0 &&
                original.order.size() == m.modules.size(),
            "whole-row positive control");
    std::ofstream controls(out / "controls.json");
    controls << "{\"n\":11,\"required_rows\":" << m.payload.size()
             << ",\"modules\":" << m.modules.size() << ",\"baseline_length\":" << original.length
             << ",\"record_length\":" << record.length
             << ",\"record_missing_intact_rows\":" << record.missing
             << ",\"record_multiple_intact_rows\":" << record.multiple
             << ",\"record_interleaved_module_runs\":" << record.interleaved
             << ",\"record_is_in_whole_row_family\":"
             << (record.missing == 0 && record.multiple == 0 && record.interleaved == 0 ? "true"
                                                                                        : "false")
             << "}\n";
    std::ofstream metrics(out / "modules.jsonl"), spectra(out / "spectra.jsonl");
    spectra << std::setprecision(20);
    int smaller = 0, stable = 0, selected = 0, denseChecked = 0;
    uint64_t ports = 0, blocks = 0;
    auto start = std::chrono::steady_clock::now();
    for (size_t position = 0; position < original.order.size(); ++position) {
        int id = original.order[position];
        auto [begin, end] = original.intervals.at(id);
        size_t leftKeep = position ? original.intervals.at(original.order[position - 1]).second : 0;
        size_t rightKeep = position + 1 < original.order.size()
                               ? original.intervals.at(original.order[position + 1]).first
                               : original.length;
        require(leftKeep >= begin && rightKeep <= end, "literal boundary accounting");
        std::string left = position ? original.word.substr(leftKeep - m.n, m.n) : "";
        std::string right =
            position + 1 < original.order.size() ? original.word.substr(rightKeep, m.n) : "";
        BoundaryPortModel p(m, m.modules.at(id), left, right);
        Quotient q = refine(p, p.portCount);
        ports += p.portCount;
        blocks += q.blocks;
        stable += q.stable;
        smaller += q.blocks < p.portCount;
        uint64_t rowCost = 0;
        for (int v : p.globalRows) {
            rowCost += m.payload[v].size() - m.h;
        }
        int originalObj =
            int(end - begin - m.h - rowCost) - int(leftKeep - begin) - int(end - rightKeep);
        int optimum = minimum(p) - 2 * m.n;
        metrics << "{\"position\":" << position << ",\"module\":" << id
                << ",\"colours\":" << p.courseCount << ",\"ports\":" << p.portCount
                << ",\"fixed_boundary_partition_blocks\":" << q.blocks
                << ",\"partition_stable\":" << (q.stable ? "true" : "false")
                << ",\"refinement_rounds\":" << q.rounds
                << ",\"universal_right_boundary_distinct_frames\":"
                << std::set<std::string>(p.ends.begin(), p.ends.end()).size()
                << ",\"occupation_state_dimension\":"
                << (2 + uint64_t(p.portCount) * (uint64_t(1) << (p.courseCount - 1)))
                << ",\"scalar_reachable_spectral_block\":" << p.courseCount + 2
                << ",\"original_objective\":" << originalObj << ",\"optimal_objective\":" << optimum
                << "}\n";
        metrics.flush();
        bool choose = position == 0 || id == 373209 || id == 373210;
        if (choose) {
            auto P = polynomial(p, 2500000000ULL);
            int lo = 0, hi = int(P.size()) - 1;
            while (!P[lo]) {
                ++lo;
            }
            while (!P[hi]) {
                --hi;
            }
            require(lo - 2 * m.n == optimum, "coefficient/min-plus agreement");
            if (p.portCount <= 100) {
                require(P == densePolynomial(p), "independent dense polynomial agreement");
                ++denseChecked;
            }
            std::ofstream poly(out / ("polynomial-" + std::to_string(id) + ".json"));
            poly << "{\"module\":" << id << ",\"colours\":" << p.courseCount
                 << ",\"known_piece_cost\":" << rowCost + m.h - 2 * m.n
                 << ",\"minimum_exponent\":" << lo << ",\"degree\":" << hi << ",\"coefficients\":[";
            for (size_t j = 0; j < P.size(); ++j) {
                if (j) {
                    poly << ',';
                }
                poly << '"' << decimal(U128(P[j])) << '"';
            }
            poly << "]}\n";
            for (long double z : {0.5L, 0.8L, 1.L}) {
                auto a = numerical(p, P, z);
                spectra << "{\"module\":" << id << ",\"z\":" << z
                        << ",\"block_dimension\":" << p.courseCount + 2
                        << ",\"polynomial_value\":" << evaluate(P, z)
                        << ",\"analytic_perron_root\":" << a.rho
                        << ",\"unreduced_numeric_perron_root\":" << a.measured
                        << ",\"relative_residual\":" << a.residual
                        << ",\"krylov_relative_error\":" << a.krylovError
                        << ",\"power_iterations\":" << a.iterations << "}\n";
                spectra.flush();
            }
            ++selected;
            std::cout << "spectral_module=" << id << " ports=" << p.portCount
                      << " quotient=" << q.blocks << " scalar_block=" << p.courseCount + 2
                      << " minimum=" << optimum << std::endl;
        }
        if (position % 25 == 0) {
            std::cout
                << "audited_modules=" << position + 1 << " seconds="
                << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count()
                << std::endl;
        }
    }
    std::ofstream result(out / "result.json");
    result << "{\"n\":11,\"modules_audited\":" << original.order.size() << ",\"ports\":" << ports
           << ",\"partition_blocks\":" << blocks << ",\"stable_partitions\":" << stable
           << ",\"modules_with_fewer_partition_blocks\":" << smaller
           << ",\"exact_polynomials_solved\":" << selected
           << ",\"independent_dense_polynomial_checks\":" << denseChecked << ",\"seconds\":"
           << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count()
           << ",\"all_superpermutations_exhausted\":false,\"new_word_generated\":false}\n";
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
#endif
