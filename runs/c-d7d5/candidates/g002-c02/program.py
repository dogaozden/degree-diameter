import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: iterated annealing over bi-Cayley lifts.
#
# Group: Z_M x| Z_K2 with r^K2 = 1 mod M, element (a, b) coded as a*K2 + b,
# product (a, b)(c, e) = (a + r^b c, b + e), as in lib.semidirect_group.
# Base: K vertices per side, d layers. Each layer is a permutation of range(K),
# so every vertex has degree exactly d. Dart t = l*K + i joins A_{i,g} to
# B_{dJ[t], g*dS[t]} for all g. Left multiplication by h is an automorphism,
# so BFS from the 2K orbit representatives decides diameter.
#
# Moves: voltage change, and (new) swap of two base targets inside one layer,
# which keeps every layer a permutation. Restarts perturb the best state found
# so far (iterated local search) instead of always starting from scratch.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXK 8
#define MAXT 512
#define MAXG 4096
#define PEN 1000
#define MAXN 200000
#define ITERS 40000

static int d, D, K, M, K2, R, G, N, T;
static long long pw[64];
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int bestJ[MAXT], bestS[MAXT];
static int *adj, *deg, *vis, *que, *seenk;
static int stamp_v = 0, stamp_k = 0;
static uint64_t rs;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(nxt() % (uint64_t)n);
}

static double urand(void) {
    return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long na = ((long long)a + pw[b] * (long long)c) % M;
    int nb = (b + e) % K2;
    return (int)na * K2 + nb;
}

static void build_adj(void) {
    memset(deg, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            int a = dI[t] * G + g;
            int b = (K + dJ[t]) * G + gmul(g, dS[t]);
            if (deg[a] < d) adj[a * d + deg[a]++] = b;
            if (deg[b] < d) adj[b * d + deg[b]++] = a;
        }
    }
}

static long long cost_eval(void) {
    build_adj();

    long long dup = 0;
    stamp_k++;
    for (int t = 0; t < T; t++) {
        int key = (dI[t] * K + dJ[t]) * G + dS[t];
        if (seenk[key] == stamp_k) dup++;
        else seenk[key] = stamp_k;
    }

    long long total = 0;
    int reps[2 * MAXK];
    int nr = 0;
    for (int i = 0; i < K; i++) reps[nr++] = i * G;
    for (int j = 0; j < K; j++) reps[nr++] = (K + j) * G;

    for (int r = 0; r < nr; r++) {
        int src = reps[r];
        stamp_v++;
        int head = 0, tail = 0;
        vis[src] = stamp_v;
        que[tail++] = src;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = que[head++];
                for (int k = 0; k < d; k++) {
                    int v = adj[u * d + k];
                    if (vis[v] != stamp_v) {
                        vis[v] = stamp_v;
                        que[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total + (long long)PEN * dup;
}

static void output_graph(void) {
    printf("%d %d\n", N, T * G);
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            int a = dI[t] * G + g;
            int b = (K + dJ[t]) * G + gmul(g, dS[t]);
            printf("%d %d\n", a, b);
        }
    }
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(G);
        }
    }
}

static void perturb_best(int k) {
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int p = 0; p < k; p++) {
        if (K >= 2 && rndint(2) == 0) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1];
            dJ[t1] = dJ[t2];
            dJ[t2] = tmp;
        } else {
            dS[rndint(T)] = rndint(G);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    R = atoi(argv[6]);
    double secs = atof(argv[7]);
    unsigned long long seed = strtoull(argv[8], NULL, 10);

    if (d < 1 || d > 64 || D < 1 || K < 1 || K > MAXK || M < 1 || K2 < 1 || K2 > 64) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (G > MAXG) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * K * G;
    T = d * K;
    if (N > MAXN || T > MAXT) {
        printf("0 0\n");
        return 0;
    }

    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (pw[b - 1] * R) % M;

    adj = (int *)malloc(sizeof(int) * (size_t)N * (size_t)d);
    deg = (int *)malloc(sizeof(int) * (size_t)N);
    vis = (int *)calloc((size_t)N, sizeof(int));
    que = (int *)malloc(sizeof(int) * (size_t)N);
    seenk = (int *)calloc((size_t)K * K * G, sizeof(int));
    if (!adj || !deg || !vis || !que || !seenk) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    long long bestcost = LLONG_MAX;

    while (elapsed(t0) < secs) {
        if (bestcost != LLONG_MAX && rndint(3) != 0) {
            perturb_best(2 + rndint(5));
        } else {
            random_init();
        }
        long long cost = cost_eval();
        if (cost < bestcost) {
            bestcost = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }

        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= secs) break;
            double frac = (double)it / ITERS;
            double temp = 1.5 * (1.0 - frac) + 0.05;

            if (K < 2 || rndint(10) < 6) {
                int idx = rndint(T);
                int old = dS[idx];
                int nw = rndint(G);
                if (nw == old) continue;
                dS[idx] = nw;
                long long c2 = cost_eval();
                if (c2 <= cost || urand() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                } else {
                    dS[idx] = old;
                }
            } else {
                int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                int tmp = dJ[t1];
                dJ[t1] = dJ[t2];
                dJ[t2] = tmp;
                long long c2 = cost_eval();
                if (c2 <= cost || urand() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                } else {
                    tmp = dJ[t1];
                    dJ[t1] = dJ[t2];
                    dJ[t2] = tmp;
                }
            }

            if (cost < bestcost) {
                bestcost = cost;
                memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
                memcpy(bestS, dS, sizeof(int) * (size_t)T);
            }
        }
        if (cost == 0) {
            output_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Group enumeration helper: semidirect products Z_m x| Z_k2 whose order m*k2
# is at least a target. Roots r with r^k2 = 1 mod m and gcd(r, m) = 1 are
# cached per (m, k2); non-trivial roots are preferred.
# ----------------------------------------------------------------------------

_ROOT_CACHE = {}


def _roots(m, k2):
    """All r in [1, m) with gcd(r, m) = 1 and r^k2 = 1 mod m."""
    key = (m, k2)
    if key not in _ROOT_CACHE:
        out = []
        if m >= 2:
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    out.append(r)
        _ROOT_CACHE[key] = out
    return _ROOT_CACHE[key]


def _group_near(g_target, k2, rng):
    """Return (m, k2, r) with m * k2 >= g_target and m * k2 close to it, or None."""
    m0 = max(2, -(-g_target // k2))
    for m in range(m0, m0 + 40):
        rs = _roots(m, k2)
        if not rs:
            continue
        nontriv = [r for r in rs if r > 1]
        pool = nontriv or rs
        r = rng.choice(pool)
        try:
            lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return m, k2, r
    return None


K_CHOICES = [1, 2, 2, 3, 3, 4, 5]
K2_CHOICES = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately for calibration-style cases.
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

    # Main search: anneal voltages and base permutations of bi-Cayley lifts.
    failures = 0
    while time.monotonic() < deadline - 0.5 and failures < 4:
        K = rng.choice(K_CHOICES)
        base = best_n // (2 * K)
        g_target = base + 1 + rng.randrange(0, max(2, base // 12 + 1))
        k2 = rng.choice(K2_CHOICES)
        g = _group_near(g_target, k2, rng)
        if g is None:
            continue
        m, k2, r = g
        remaining = deadline - time.monotonic()
        slice_s = min(remaining - 0.5, 7.0)
        if slice_s < 0.5:
            break
        seed_c = rng.randrange(1, 1 << 30)
        try:
            out = lib.run_c(C_SOURCE, [d, D, K, m, k2, r, f"{slice_s:.2f}", seed_c],
                            timeout=slice_s + 10.0)
            n, e = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            failures += 1
            continue
        if n > 0:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
