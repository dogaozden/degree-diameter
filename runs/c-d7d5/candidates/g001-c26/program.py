import itertools
import math
import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline families (kept from the parent as the safe fallback).
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
# Bold change: a C engine that searches bi-Cayley lifts over semidirect
# products Z_m x| Z_k2 with a base of K vertices per side and d layers.
#
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (K+j)*G + h.
# Each layer l is a permutation perm[l] of range(K) plus a voltage vol[l][i];
# dart (l,i) joins A_{i,g} to B_{perm[l][i], g*vol} for every g. This gives
# every vertex degree exactly d. Left multiplication is an automorphism, so
# the BFS only needs the 2K identity representatives.
# Simulated annealing minimises unreached (rep, vertex) pairs plus a penalty
# for duplicate darts. The engine keeps raising the target order, starting
# from the minimum order given by Python.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define PEN 1000LL

static int d_, D_;
static double BUDGET = 10.0;
static clock_t T0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

/* group Z_m x| Z_k2, element (a,b) coded as a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) */
static int GM = 1, GK = 1, GG = 1;
static int pw[64];

static int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int na = (a + (int)(((long long)pw[b] * c) % GM)) % GM;
    int nb_ = (b + e) % GK;
    return na * GK + nb_;
}

static void set_group(int m, int k2, int r) {
    GM = m; GK = k2; GG = m * k2;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % m);
}

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int pick_r(int m, int k2) {
    if (k2 == 1 || m <= 2 || rndint(3) == 0) return 1;
    for (int t = 0; t < 300; t++) {
        int r = 2 + rndint(m - 2);
        if (gcdi(r, m) == 1 && pmod(r, k2, m) == 1 % m) return r;
    }
    return -1;
}

/* lift state */
static int DD = 1, KK = 1;
static int perm[MAXD][MAXK], vol[MAXD][MAXK];
static int sperm[MAXD][MAXK], svol[MAXD][MAXK];
static int capN = 0;
static int *nb = NULL, *cnt = NULL, *vis = NULL, *queue = NULL;
static int stamp = 0;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(nb); free(cnt); free(vis); free(queue);
    capN = N + 64;
    nb = malloc(sizeof(int) * (size_t)capN * MAXD);
    cnt = calloc((size_t)capN, sizeof(int));
    vis = calloc((size_t)capN, sizeof(int));
    queue = malloc(sizeof(int) * (size_t)capN);
    stamp = 0;
}

static long long evalcost(void) {
    int K = KK, d = DD, G = GG, N = 2 * K * G;
    int nd = d * K;
    long long dup = 0;
    for (int x = 0; x < nd; x++) {
        for (int y = x + 1; y < nd; y++) {
            int l1 = x / K, i1 = x % K, l2 = y / K, i2 = y % K;
            if (i1 == i2 && perm[l1][i1] == perm[l2][i2] && vol[l1][i1] == vol[l2][i2]) dup++;
        }
    }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) {
            int j = perm[l][i], s = vol[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                nb[a * d + cnt[a]++] = b;
                nb[b * d + cnt[b]++] = a;
            }
        }
    }
    if (stamp > 1000000000) {
        memset(vis, 0, sizeof(int) * (size_t)capN);
        stamp = 0;
    }
    long long total = 0;
    for (int q = 0; q < 2 * K; q++) {
        int src = (q < K) ? q * G : (K + (q - K)) * G;
        stamp++;
        int head = 0, tail = 0;
        queue[tail++] = src;
        vis[src] = stamp;
        for (int lev = 0; lev < D_ && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = queue[head++];
                for (int t = 0; t < d; t++) {
                    int v = nb[u * d + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        queue[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total + PEN * dup;
}

static void init_state(void) {
    for (int l = 0; l < DD; l++) {
        for (int i = 0; i < KK; i++) perm[l][i] = i;
        for (int i = KK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = t;
        }
        for (int i = 0; i < KK; i++) vol[l][i] = rndint(GG);
    }
}

static void mutate(void) {
    if (rnd01() < 0.6) {
        int l = rndint(DD), i = rndint(KK);
        vol[l][i] = rndint(GG);
    } else {
        int l = rndint(DD), i1 = rndint(KK), i2 = rndint(KK);
        int t = perm[l][i1]; perm[l][i1] = perm[l][i2]; perm[l][i2] = t;
    }
}

static int anneal(int iters) {
    init_state();
    long long cost = evalcost();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 255) == 0 && elapsed() > BUDGET) return 0;
        memcpy(sperm, perm, sizeof perm);
        memcpy(svol, vol, sizeof vol);
        mutate();
        long long c2 = evalcost();
        double temp = 2.0 * (1.0 - (double)it / iters) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            memcpy(perm, sperm, sizeof perm);
            memcpy(vol, svol, sizeof vol);
        }
    }
    return cost == 0;
}

static int *bestE = NULL;
static int bestM = 0, bestNv = 0;

static void record(void) {
    int K = KK, d = DD, G = GG, N = 2 * K * G;
    int m = d * K * G;
    int *E = malloc(sizeof(int) * 2 * (size_t)m);
    int c = 0;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) {
            int j = perm[l][i], s = vol[l][i];
            for (int g = 0; g < G; g++) {
                E[2 * c] = i * G + g;
                E[2 * c + 1] = (K + j) * G + gmul(g, s);
                c++;
            }
        }
    }
    free(bestE);
    bestE = E;
    bestM = m;
    bestNv = N;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    BUDGET = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 1 || d_ > MAXD || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    DD = d_;
    T0 = clock();

    int bestN = minN;
    ensure_cap(2 * MAXK * 4 + (minN > 0 ? minN : 0) + 64);

    while (elapsed() < BUDGET) {
        int K = 1 + rndint(4);
        int base = bestN / (2 * K) + 1;
        int spread = base / 16 + 1;
        int G = base + rndint(spread);
        int cands[32], nc = 0;
        for (int x = 1; x <= 30 && x <= G; x++) {
            if (G % x == 0) cands[nc++] = x;
        }
        int k2 = cands[rndint(nc)];
        int m = G / k2;
        int r = pick_r(m, k2);
        if (r < 0) continue;
        int N = 2 * K * G;
        ensure_cap(N);
        set_group(m, k2, r);
        KK = K;
        if (anneal(3000)) {
            if (N > bestN) {
                bestN = N;
                record();
            }
        }
    }

    if (bestE == NULL) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestNv, bestM);
    for (int c = 0; c < bestM; c++) {
        printf("%d %d\n", bestE[2 * c], bestE[2 * c + 1]);
    }
    return 0;
}
'''


def build(d, D, seed, time_limit):
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

    # Exact constructions first.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold search: C annealing over semidirect-product bi-Cayley lifts,
    # starting above the best order found so far.
    if D >= 3 and 3 <= d <= 12 and time_limit > 8:
        budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                            timeout=budget + 10.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
