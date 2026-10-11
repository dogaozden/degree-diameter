import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# Search engine in C: simulated annealing over the voltages of a bi-Cayley lift
# over the semidirect product Z_m x| Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base: k vertices per side, d layers, each layer a permutation of range(k).
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s}. Every vertex has degree d.
# Cost = unreached (representative, vertex) pairs + duplicate-dart penalty.
# The C program prints the first cost-0 graph it finds, or "0 0" on timeout.
#
# Moving the annealing loop into C lets it evaluate far more voltage settings
# per second than the Python version did.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define PEN 1000

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, M_, K2_, N_, ND_;
static int *powr;
static int *di, *dj, *ds;
static int *adj, *deg, *vis, *qu;
static int stamp_ = 0;

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_, c = y / K2_, dd = y % K2_;
    long long t = ((long long)a + (long long)powr[b] * c) % M_;
    return (int)(t * K2_ + (b + dd) % K2_);
}

static long long cost(void) {
    int N = N_, G = G_, d = d_, k = k_;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int t = 0; t < ND_; t++) {
        int i = di[t], j = dj[t], s = ds[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + gmul(g, s);
            adj[a * d + deg[a]++] = b;
            adj[b * d + deg[b]++] = a;
        }
    }
    long long dup = 0;
    for (int a = 0; a < ND_; a++)
        for (int b = a + 1; b < ND_; b++)
            if (di[a] == di[b] && dj[a] == dj[b] && ds[a] == ds[b]) dup++;

    if (stamp_ > 1900000000) {
        memset(vis, 0, sizeof(int) * (size_t)N);
        stamp_ = 0;
    }
    long long total = 0;
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        stamp_++;
        int head = 0, tail = 1;
        qu[0] = src;
        vis[src] = stamp_;
        for (int lev = 0; lev < D_ && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                for (int q = 0; q < d; q++) {
                    int v = adj[u * d + q];
                    if (vis[v] != stamp_) {
                        vis[v] = stamp_;
                        qu[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total + (long long)PEN * dup;
}

static void init_random(void) {
    int k = k_;
    int *perm = malloc(sizeof(int) * (size_t)k);
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            di[t] = i;
            dj[t] = perm[i];
            ds[t] = rndint(G_);
        }
    }
    free(perm);
}

static void output_graph(void) {
    int G = G_, k = k_;
    printf("%d %d\n", N_, ND_ * G);
    for (int t = 0; t < ND_; t++) {
        for (int g = 0; g < G; g++) {
            int a = di[t] * G + g;
            int b = (k + dj[t]) * G + gmul(g, ds[t]);
            printf("%d %d\n", a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D seed time_limit k m k2 r\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    k_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    int R = atoi(argv[8]);

    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 4; i++) rnd64();

    if (d_ < 1 || k_ < 1 || M_ < 1 || K2_ < 1) { printf("0 0\n"); return 0; }

    G_ = M_ * K2_;
    N_ = 2 * k_ * G_;
    ND_ = d_ * k_;

    powr = malloc(sizeof(int) * (size_t)K2_);
    powr[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) powr[b] = (int)((long long)powr[b - 1] * R % M_);

    di = malloc(sizeof(int) * (size_t)ND_);
    dj = malloc(sizeof(int) * (size_t)ND_);
    ds = malloc(sizeof(int) * (size_t)ND_);
    adj = malloc(sizeof(int) * (size_t)N_ * d_);
    deg = malloc(sizeof(int) * (size_t)N_);
    vis = calloc((size_t)N_, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N_);

    clock_t c0 = clock();
    const int ITERS = 30000;

    for (;;) {
        init_random();
        long long c = cost();
        for (int it = 0; it < ITERS && c != 0; it++) {
            if ((it & 63) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > tl) {
                printf("0 0\n");
                return 0;
            }
            int t = rndint(ND_);
            int old = ds[t];
            ds[t] = rndint(G_);
            long long c2 = cost();
            double temp = 2.0 * (1.0 - (double)it / ITERS) + 0.05;
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / temp)) {
                c = c2;
            } else {
                ds[t] = old;
            }
        }
        if (c == 0) {
            output_graph();
            return 0;
        }
        if ((double)(clock() - c0) / CLOCKS_PER_SEC > tl) {
            printf("0 0\n");
            return 0;
        }
    }
    return 0;
}
'''


def _sample_group(target, rng):
    """Return (m, k2, r) for a random semidirect product Z_m x| Z_k2 of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return m, k2, r
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 4.0))
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

    # Exact constructions: return immediately (calibration-style cases).
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

    # Main search: the C engine anneals voltages for one group/base choice per call.
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        k = rng.choice([1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        slice_s = min(remaining - 0.5, max(2.0, budget / 8.0))
        if slice_s < 0.5:
            break
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), round(slice_s, 3), k, m, k2, r],
                            timeout=slice_s + 15.0)
            n, e = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            continue
        if n > best_n:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
