import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts Z_M x| Z_K2 with K base
# vertices per side and d darts per base vertex.
#
# Structure: dart t = layer*K + i joins A_i to B_{dj[t]} with voltage ds[t].
# Each layer is a permutation of the K base targets, so the base is d-regular.
#
# Moves:
#   (a) change one voltage ds[t]                       (parent's only move)
#   (b) swap the two targets of one layer at sources i1, i2   (new: changes the
#       base graph itself while keeping every vertex at degree exactly d)
#
# Cost = (unreached (representative, vertex) pairs over the 2K representatives,
#         by left-multiplication symmetry) + penalty * duplicate darts.
# Zero cost means diameter <= D. The engine stops at the first zero.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXT 256
#define PEN 1000LL

static int d, Dd, K;
static long long M, K2, R, G, N;
static long long pw[64];
static uint64_t rs;
static int dj[MAXT];
static long long ds[MAXT];
static int *adj, *cnt, *stamp, *qu;
static int curstamp = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static long long rndint(long long n) {
    return (long long)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

/* Element (a, b) of Z_M x| Z_K2 is coded a*K2 + b; (a,b)(c,e) = (a + R^b c, b + e). */
static inline long long gmul(long long x, long long y) {
    long long a = x / K2, b = x % K2;
    long long c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M) * K2 + (b + e) % K2;
}

static long long compute_cost(int T) {
    long long dup = 0;
    for (int a = 0; a < T; a++) {
        for (int b = a + 1; b < T; b++) {
            if (a % K == b % K && dj[a] == dj[b] && ds[a] == ds[b]) dup++;
        }
    }
    for (long long v = 0; v < N; v++) cnt[v] = 0;
    for (int t = 0; t < T; t++) {
        long long i = t % K, j = dj[t], s = ds[t];
        for (long long g = 0; g < G; g++) {
            long long a = i * G + g;
            long long b = (K + j) * G + gmul(g, s);
            adj[a * d + cnt[a]++] = (int)b;
            adj[b * d + cnt[b]++] = (int)a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        long long src = (long long)r * G;
        curstamp++;
        int head = 0, tail = 0;
        stamp[src] = curstamp;
        qu[tail++] = (int)src;
        for (int lv = 0; lv < Dd; lv++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                for (int e = 0; e < d; e++) {
                    int v = adj[(long long)u * d + e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total + PEN * dup;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D seed time K M K2 R\n");
        return 1;
    }
    d = atoi(argv[1]);
    Dd = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoll(argv[6]);
    K2 = atoll(argv[7]);
    R = atoll(argv[8]);
    if (d < 1 || d > 64 || K < 1 || K > 8 || d * K > MAXT || M < 1 || K2 < 1 || K2 > 60) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2LL * K * G;
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    pw[0] = 1 % M;
    for (long long b = 1; b < K2; b++) pw[b] = (pw[b - 1] * (R % M)) % M;

    adj = malloc(sizeof(int) * (size_t)N * (size_t)d);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !cnt || !stamp || !qu) {
        printf("0 0\n");
        return 0;
    }

    int T = d * K;
    for (int l = 0; l < d; l++) {
        int perm[8];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int jx = (int)rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[jx];
            perm[jx] = tmp;
        }
        for (int i = 0; i < K; i++) {
            dj[l * K + i] = perm[i];
            ds[l * K + i] = rndint(G);
        }
    }

    long long cost = compute_cost(T);
    clock_t c0 = clock();
    double elapsed = 0.0;
    long long it = 0;

    while (cost > 0) {
        if ((it & 31) == 0) {
            elapsed = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (elapsed > limit) break;
        }
        it++;
        double temp = 3.0 * (1.0 - elapsed / limit) + 0.05;
        if (temp < 0.05) temp = 0.05;

        int do_swap = (K >= 2) && (rnd64() % 2 == 0);
        if (!do_swap) {
            int t = (int)rndint(T);
            long long old = ds[t];
            long long nw = rndint(G);
            if (nw == old) continue;
            ds[t] = nw;
            long long c2 = compute_cost(T);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                ds[t] = old;
            }
        } else {
            int l = (int)rndint(d);
            int i1 = (int)rndint(K);
            int i2 = (int)rndint(K - 1);
            if (i2 >= i1) i2++;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dj[t1];
            dj[t1] = dj[t2];
            dj[t2] = tmp;
            long long c2 = compute_cost(T);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = dj[t1];
                dj[t1] = dj[t2];
                dj[t2] = tmp;
            }
        }
    }

    if (cost == 0) {
        printf("%lld %lld\n", N, (long long)T * G);
        for (int t = 0; t < T; t++) {
            long long i = t % K, j = dj[t], s = ds[t];
            for (long long g = 0; g < G; g++) {
                long long a = i * G + g;
                long long b = (K + j) * G + gmul(g, s);
                printf("%lld %lld\n", a, b);
            }
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (unchanged from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# Group sampling and C call wrapper.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 of order near target (order = m*k2), or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            return m, 1, 1
        if m > 2:
            cands = [1, m - 1] + [rng.randrange(2, m) for _ in range(40)]
        else:
            cands = [1]
        for c in cands:
            c %= m
            if c and math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


def _run_search(d, D, seed, secs, k, m, k2, r):
    """Run the C annealer for about secs seconds. Returns (n, edges) or None."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{secs:.2f}", k, m, k2, r],
                         timeout=secs + 3.0)
        n, edges = lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return None
    if n <= 0 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and 2d vertices, which is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C annealing over bi-Cayley lifts. Each success raises the
    # target order, so the search climbs past the current best graph.
    attempts = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        k = rng.choice([1, 1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 25 + 2)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        slice_t = min(remaining, max(2.0, remaining / 4.0))
        out = _run_search(d, D, seed * 1000 + attempts, slice_t, k, m, k2, r)
        attempts += 1
        if out is not None:
            consider(out[0], out[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
