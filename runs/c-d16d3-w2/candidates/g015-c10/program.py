import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D = 3: bipartite Haar graphs from difference bases.
#
# H(m, S) has sides a_i, b_j (i, j in Z_m) with a_i ~ b_{i+s} for s in S.
# If |S| = d and S - S covers all of Z_m, then every same-side pair is at
# distance <= 2 (a common neighbour exists), and every cross pair is at
# distance <= 3 (use s1 - s2 + 0 with 0 in S). So the graph is d-regular,
# bipartite, of diameter 3, with 2m vertices. The question is how large m can
# be for a given d, which is a covering (difference basis) problem. The C
# engine below searches it with simulated annealing, raising m step by step.
# ----------------------------------------------------------------------------

DIFF_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>

#define MAXK 64
#define MAXM 4096

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M;
static int S[MAXK];
static int cnt[MAXM];
static unsigned char inS[MAXM];
static int cost;

static int md(int x) { x %= M; if (x < 0) x += M; return x; }

/* cost = number of nonzero residues x with cnt[x] == 0 (uncovered differences) */
static void bump(int x, int sign) {
    if (sign < 0) {
        cnt[x]--;
        if (cnt[x] == 0 && x != 0) cost++;
    } else {
        if (cnt[x] == 0 && x != 0) cost--;
        cnt[x]++;
    }
}

static void diffs_of(int i, int sign) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        bump(md(S[i] - S[j]), sign);
        bump(md(S[j] - S[i]), sign);
    }
}

static void set_elem(int i, int v) {
    diffs_of(i, -1);
    inS[S[i]] = 0;
    S[i] = v;
    inS[v] = 1;
    diffs_of(i, +1);
}

static void rebuild(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    cost = 0;
    for (int x = 1; x < M; x++) if (cnt[x] == 0) cost++;
}

static void random_start(void) {
    memset(inS, 0, sizeof(unsigned char) * (size_t)M);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int v;
        do { v = rint_(M); } while (inS[v]);
        S[i] = v;
        inS[v] = 1;
    }
    rebuild();
}

/* Simulated annealing chunk. Element S[0] = 0 stays fixed (translation WLOG). */
static int anneal_chunk(long L) {
    for (long it = 0; it < L; it++) {
        if (cost == 0) return 1;
        if (M <= K) break;
        double T = 0.08 + 0.7 * (1.0 - (double)it / (double)L);
        int i = 1 + rint_(K - 1);
        int r;
        do { r = rint_(M); } while (inS[r]);
        int old = S[i];
        int oldcost = cost;
        set_elem(i, r);
        int delta = cost - oldcost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) continue;
        set_elem(i, old);
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    K = atoi(argv[1]);
    uint64_t seed = (uint64_t)strtoull(argv[2], NULL, 10);
    double total = atof(argv[3]);
    int m0 = atoi(argv[4]);
    if (K < 2 || K > MAXK) { printf("0 0\n"); return 0; }
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 0x1234567ULL);
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int best_m = 0;
    int best_S[MAXK];
    int m = m0 > K ? m0 : K;

    while (m < MAXM) {
        M = m;
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        double remain = total - el;
        if (remain <= 0.05) break;
        double cap = 0.5 * remain;
        double tm0 = el;
        int found = 0;
        while (!found) {
            double now = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (now - tm0 > cap) break;
            random_start();
            found = anneal_chunk(400000L);
        }
        if (!found) break;
        best_m = m;
        memcpy(best_S, S, sizeof(int) * (size_t)K);
        m++;
    }

    if (best_m == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_m, K);
    for (int i = 0; i < K; i++) printf("%d\n", best_S[i]);
    return 0;
}
"""


def _haar_search(d, D, m0, seed, budget):
    """Run the difference-basis search and return a validated (n, edges) Haar graph, or None."""
    if budget < 1.0:
        return None
    try:
        out = lib.run_c(DIFF_C, [d, seed, round(budget, 2), m0], timeout=budget + 5)
    except Exception:
        return None
    nums = out.split()
    if len(nums) < 2:
        return None
    m, k = int(nums[0]), int(nums[1])
    if m < 1 or k != d or len(nums) < 2 + k:
        return None
    S = [int(x) for x in nums[2:2 + k]]
    if len(set(S)) != k or any(not 0 <= s < m for s in S):
        return None
    n, E = lib.haar_graph(m, S)
    if lib.is_valid(n, E, d, D):
        return n, E
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). With d >= q+1 each vertex has
# spare capacity s = d - q - 1. Choose S so that every line holds <= s points
# of S and every point lies on <= s lines indexed by S. Add an A-vertex joined
# to the q+1 lines through each P in S, and a B-vertex joined to the q+1 points
# on each line j in S.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.85 * time_limit - 1.5

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Bold change for D >= 3: Haar graphs of a difference basis of Z_m.
    # Order 2m, degree d, diameter 3. The search raises m while annealing succeeds.
    if D >= 3 and time.monotonic() < end:
        remain = end - time.monotonic()
        budget = remain if D == 3 else 0.35 * remain
        if budget > 1.0:
            m0 = max(d, best[0] // 2 - 2)
            consider(_haar_search(d, D, m0, seed, budget))

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        consider(_best_gq(d))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
