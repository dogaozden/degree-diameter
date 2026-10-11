"""Diameter-3 bipartite search with a difference-cover (Haar graph) construction.

New construction: the Haar graph H(Z_n, S) has parts A = {a_i} and B = {b_j}, with a_i ~ b_{i+s}
for s in S, |S| = d. It is d-regular and bipartite on 2n vertices. Two A-vertices are at distance 2
iff S - S covers Z_n, and every A-B pair is within distance 3 once S - S = Z_n (since
h - g in S - S + S). So any difference cover S of Z_n with |S| = d gives a valid diameter-3
graph on 2n vertices. The C engine searches for a difference cover of Z_n by simulated annealing,
increasing n while covers are found.

Safe fallbacks: the projective-plane arc extensions and K_{d,d} stay in the candidate list, and
every candidate is checked with lib.is_valid before the largest valid one is returned.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXN 1024

static int K, N;
static int S[MAXK];
static int inS[MAXN];
static int cnt[MAXN];
static int zeros;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double cpu(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int md(int v) {
    v %= N;
    return v < 0 ? v + N : v;
}

/* Change the multiplicity of a nonzero residue r in the difference multiset. */
static void bump(int r, int d) {
    if (r == 0) return;
    if (d > 0) {
        if (cnt[r] == 0) zeros--;
        cnt[r]++;
    } else {
        cnt[r]--;
        if (cnt[r] == 0) zeros++;
    }
}

/* Add (d = +1) or remove (d = -1) the differences between x and all S[j], j != skip. */
static void touch(int x, int skip, int d) {
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        bump(md(x - S[j]), d);
        bump(md(S[j] - x), d);
    }
}

/* Simulated annealing for a difference cover of Z_N of size K. Returns 1 on success (S in S[]). */
static int anneal(double slice_end) {
    while (cpu() < slice_end) {
        memset(inS, 0, sizeof(int) * N);
        memset(cnt, 0, sizeof(int) * N);
        zeros = N - 1;
        for (int i = 0; i < K; i++) {
            int x;
            do {
                x = (int)(rnd() % (uint64_t)N);
            } while (inS[x]);
            inS[x] = 1;
            S[i] = x;
        }
        for (int i = 0; i < K; i++)
            for (int j = i + 1; j < K; j++) {
                bump(md(S[i] - S[j]), 1);
                bump(md(S[j] - S[i]), 1);
            }
        if (zeros == 0) return 1;

        const long L = 4000000;
        double T = 1.0;
        double alpha = pow(0.02, 1.0 / (double)L);
        for (long it = 0; it < L; it++) {
            if ((it & 4095) == 0 && cpu() > slice_end) break;
            int i = (int)(rnd() % (uint64_t)K);
            int s = S[i], x;
            do {
                x = (int)(rnd() % (uint64_t)N);
            } while (inS[x]);
            int old = zeros;
            touch(s, i, -1);
            inS[s] = 0;
            touch(x, i, +1);
            inS[x] = 1;
            S[i] = x;
            int delta = zeros - old;
            if (delta > 0 && rnd01() >= exp(-(double)delta / T)) {
                touch(x, i, -1);
                inS[x] = 0;
                touch(s, i, +1);
                inS[s] = 1;
                S[i] = s;
            }
            if (zeros == 0) return 1;
            T *= alpha;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    K = atoi(argv[1]);
    int nlo = atoi(argv[2]);
    double budget = atof(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    if (K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    int nmax = K * (K - 1) + 1;
    if (nmax > MAXN - 1) nmax = MAXN - 1;
    if (nlo < K + 1) nlo = K + 1;

    double t_end = cpu() + budget;
    int bestN = 0;
    int bestS[MAXK];
    for (int n = nlo; n <= nmax; n++) {
        N = n;
        double now = cpu();
        if (now >= t_end) break;
        double rem = t_end - now;
        double slice = rem * 0.4;
        if (slice < 0.5) slice = rem;
        if (!anneal(now + slice)) break;
        bestN = n;
        memcpy(bestS, S, sizeof(int) * K);
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d", bestN, K);
    for (int i = 0; i < K; i++) printf(" %d", bestS[i]);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Difference-cover Haar graph search (new construction for D >= 3).
# ----------------------------------------------------------------------------

def _haar_search(d, budget, seed, timeout):
    """Ask the C engine for a difference cover S of Z_n with |S| = d; return the Haar graph or None."""
    nlo = max(d + 1, d * d // 2)
    text = lib.run_c(C_SOURCE, [d, nlo, f"{budget:.2f}", seed],
                     stdin_graph=None, timeout=timeout)
    nums = [int(x) for x in text.split()]
    if len(nums) < 2 or nums[0] <= 0:
        return None
    n, k = nums[0], nums[1]
    S = nums[2:2 + k]
    if k != d or len(S) != k or len(set(s % n for s in S)) != k:
        return None
    return lib.haar_graph(n, S)


def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    cands = [fallback]
    rng = random.Random(seed * 7919 + d)

    if D >= 3 and d >= 2:
        try:
            cands.extend(_arc_extensions(d, t0 + 0.12 * time_limit, rng))
        except Exception:
            pass
        elapsed = time.monotonic() - t0
        budget = 0.75 * time_limit - elapsed - 1.0
        timeout = 0.92 * time_limit - elapsed
        if budget > 2.0 and timeout > budget:
            try:
                g = _haar_search(d, budget, seed, timeout)
                if g is not None:
                    cands.append(g)
            except Exception:
                pass

    if D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                cands.append(gq)
        except Exception:
            pass

    valid = []
    for g in cands:
        try:
            if lib.is_valid(g[0], g[1], d, D):
                valid.append(g)
        except Exception:
            pass
    if not valid:
        return 1, []
    return max(valid, key=lambda g: g[0])
