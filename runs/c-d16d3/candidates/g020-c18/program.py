"""Diameter-3 bipartite search: cyclic Haar graphs from difference covers, plus arc-extended projective planes.

New construction (for D >= 3): the Haar graph of Z_m with connection set S, |S| = d. Vertices a_i = i and
b_j = m + j, with a_i ~ b_{i+s} for s in S. The graph is bipartite and d-regular with 2m vertices.
Diameter 3 holds exactly when:
  (1) S - S covers every nonzero residue (a-a and b-b distances are then 2), and
  (2) S union (S - S + S) covers Z_m (a-b distances are then at most 3).
So the search is for a difference cover of size d in Z_m with m as large as possible. Order 2m with m > 197
beats the d=16 record of 394. The C engine runs simulated annealing over the elements of S, minimising the
number of uncovered residues, and checks condition (2) on each zero-cost state. The largest feasible m is kept.

Fallbacks: the arc-extended PG(2,q) graphs (Python), the generalized quadrangle W(q) for D >= 4, and K_{d,d}.
Every candidate is checked with lib.is_valid, and the largest valid graph is returned.
"""
import itertools
import random
import time

import lib

C_HAAR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 2048

static int K, M;
static int S[MAXK];
static int tS[MAXK];
static int bestS[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int cov[MAXM];
static int zeros;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static inline int md(int a) { a %= M; if (a < 0) a += M; return a; }

/* zeros = number of residues r in 1..M-1 with cnt[r] == 0 */
static inline void inc(int r) { if (cnt[r] == 0) zeros--; cnt[r]++; }
static inline void dec(int r) { cnt[r]--; if (cnt[r] == 0) zeros++; }

static void drop(int i) {
    int x = S[i];
    for (int j = 0; j < K; j++) if (j != i) {
        dec(md(x - S[j]));
        dec(md(S[j] - x));
    }
}

static void put(int i) {
    int y = S[i];
    for (int j = 0; j < K; j++) if (j != i) {
        inc(md(y - S[j]));
        inc(md(S[j] - y));
    }
}

static void init_state(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(inS, 0, sizeof(int) * (size_t)M);
    zeros = M - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int y;
        do { y = 1 + rndint(M - 1); } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            inc(md(S[i] - S[j]));
            inc(md(S[j] - S[i]));
        }
}

/* Condition (2): every residue is in S or in S - S + S. */
static int covers_all(void) {
    memset(cov, 0, sizeof(int) * (size_t)M);
    for (int a = 0; a < K; a++) cov[S[a]] = 1;
    for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++)
            for (int c = 0; c < K; c++)
                cov[md(S[a] - S[b] + S[c])] = 1;
    for (int r = 0; r < M; r++) if (!cov[r]) return 0;
    return 1;
}

static int solve(double end, int *out) {
    const long ITER = 300000;
    while (cpu() < end) {
        init_state();
        for (long it = 0; it < ITER; it++) {
            if ((it & 2047) == 0 && cpu() >= end) return 0;
            double T = 0.6 * pow(0.03 / 0.6, (double)it / (double)ITER);
            int i = 1 + rndint(K - 1);
            int x = S[i];
            int y;
            do { y = 1 + rndint(M - 1); } while (inS[y]);
            int z0 = zeros;
            drop(i);
            inS[x] = 0;
            S[i] = y;
            inS[y] = 1;
            put(i);
            int delta = zeros - z0;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                if (zeros == 0 && (it & 15) == 0 && covers_all()) {
                    for (int j = 0; j < K; j++) out[j] = S[j];
                    return 1;
                }
            } else {
                drop(i);
                inS[y] = 0;
                S[i] = x;
                inS[x] = 1;
                put(i);
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    K = atoi(argv[1]);
    int mlo = atoi(argv[2]);
    int mhi = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    if (K < 2 || K > MAXK) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (mhi > MAXM - 1) mhi = MAXM - 1;
    if (mlo < K + 1) mlo = K + 1;

    double end = cpu() + budget;
    int bestM = -1;
    double rounds[3] = {0.35, 1.5, 4.0};
    for (int r = 0; r < 3; r++) {
        for (int m = mlo; m <= mhi; m++) {
            if (m <= bestM) continue;
            if (cpu() >= end) break;
            M = m;
            double me = cpu() + rounds[r];
            if (me > end) me = end;
            if (solve(me, tS)) {
                bestM = m;
                for (int j = 0; j < K; j++) bestS[j] = tS[j];
            }
        }
    }
    if (bestM < 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestM, K);
    for (int j = 0; j < K; j++) printf("%d ", bestS[j]);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Difference-cover Haar graph search (diameter 3, degree d).
# ----------------------------------------------------------------------------

def _haar_search(d, budget, seed):
    """Return (n, edges) of the best cyclic Haar graph found, or None."""
    mhi = d * (d - 1) + 1
    mlo = max(d + 1, (3 * mhi) // 4)
    if mhi >= 2000:
        return None
    text = lib.run_c(C_HAAR, [d, mlo, mhi, seed % 1000003, f"{budget:.2f}"],
                     timeout=budget + 10.0)
    tok = text.split()
    if len(tok) < 2:
        return None
    m, k = int(tok[0]), int(tok[1])
    if m <= 0 or k != d or len(tok) < 2 + k:
        return None
    S = sorted({int(x) % m for x in tok[2:2 + k]})
    edges = [(i, m + (i + s) % m) for i in range(m) for s in S]
    return 2 * m, edges


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), Python fallback.
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found within about 75% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = (1, [])
    fallback = lib.haar_graph(d, range(d))
    if lib.is_valid(fallback[0], fallback[1], d, D):
        best = fallback

    rng = random.Random(seed * 7919 + d)

    if D >= 3:
        try:
            for g in _arc_extensions(d, t0 + 0.12 * time_limit, rng):
                if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                    best = g
        except Exception:
            pass

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
                best = gq
        except Exception:
            pass

    if D >= 3 and d >= 2:
        budget = 0.75 * time_limit - (time.monotonic() - t0)
        if budget >= 2.0:
            try:
                res = _haar_search(d, budget, seed)
                if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                    best = res
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
