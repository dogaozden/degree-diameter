"""Bi-cyclic voltage lifts (Z_m, one or two orbits per side) found by annealing, with an increasing order scan.

A lift has K orbits per side and d layers. Layer l sends orbit i to orbit SIG[l][i] with voltage VOL[l][i]
in Z_m: A(i,x) ~ B(SIG[l][i], x + VOL[l][i]). The result is d-regular and bipartite on 2*K*m vertices.
Translation by Z_m is an automorphism, so the diameter is at most D iff BFS of depth D from each of the
2K class representatives reaches every vertex. Annealing minimises the number of unreached pairs. The
order m is raised whenever an annealing run succeeds, and retries get longer as failures accumulate.
Python keeps a valid fallback (K_{d,d}, or a known D = 3 or 4 construction) and validates the C output.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096
#define MAXD 16
#define MAXK 2
#define BIG 1000000L

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M, N;
static int SIG[MAXD][MAXK];
static int VOL[MAXD][MAXK];
static int BSIG[MAXD][MAXK], BVOL[MAXD][MAXK];
static int BK, BM;
static int ADJ[MAXV][MAXD];
static int VIS[MAXV];
static int STAMP = 0;
static int QU[MAXV];

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void build_adj(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = SIG[l][i], v = VOL[l][i];
            for (int x = 0; x < M; x++) {
                int a = i * M + x;
                int b = K * M + j * M + (x + v) % M;
                ADJ[a][l] = b;
                ADJ[b][l] = a;
            }
        }
}

/* Number of duplicated darts (two layers with the same target and voltage in one orbit). */
static int dups(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (SIG[l1][i] == SIG[l2][i] && VOL[l1][i] == VOL[l2][i]) c++;
    return c;
}

/* Unreached (representative, vertex) pairs over the 2K class representatives. */
static long cost_fn(void) {
    int dp = dups();
    if (dp) return BIG + dp;
    build_adj();
    if (STAMP > 1000000000) {
        memset(VIS, 0, sizeof VIS);
        STAMP = 0;
    }
    long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * M;
        STAMP++;
        int h = 0, t = 0;
        VIS[src] = STAMP;
        QU[t++] = src;
        for (int dep = 0; dep < D && h < t; dep++) {
            int e = t;
            while (h < e) {
                int u = QU[h++];
                for (int s = 0; s < d; s++) {
                    int v = ADJ[u][s];
                    if (VIS[v] != STAMP) {
                        VIS[v] = STAMP;
                        QU[t++] = v;
                    }
                }
            }
        }
        total += N - t;
    }
    return total;
}

static void randperm(int *p, int k) {
    for (int i = 0; i < k; i++) p[i] = i;
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int s = p[i];
        p[i] = p[j];
        p[j] = s;
    }
}

/* One annealing run for K orbits and order m. Returns 1 if the lift has diameter <= D. */
static int anneal(int k, int m, long steps) {
    K = k;
    M = m;
    N = 2 * K * M;
    for (int l = 0; l < d; l++) {
        randperm(SIG[l], K);
        for (int i = 0; i < K; i++) VOL[l][i] = rndint(M);
    }
    long cost = cost_fn();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.02;
        if (K > 1 && rnd01() < 0.3) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int tmp = SIG[l][i1];
            SIG[l][i1] = SIG[l][i2];
            SIG[l][i2] = tmp;
            long c2 = cost_fn();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                tmp = SIG[l][i1];
                SIG[l][i1] = SIG[l][i2];
                SIG[l][i2] = tmp;
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = VOL[l][i], nv = rndint(M);
            if (nv == old) continue;
            VOL[l][i] = nv;
            long c2 = cost_fn();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                VOL[l][i] = old;
            }
        }
    }
    return cost == 0;
}

static void print_best(void) {
    if (BK == 0) {
        printf("0 0\n");
        return;
    }
    int n = 2 * BK * BM;
    long m = (long)BK * BM * d;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < BK; i++)
            for (int x = 0; x < BM; x++) {
                int a = i * BM + x;
                int b = BK * BM + BSIG[l][i] * BM + (x + BVOL[l][i]) % BM;
                printf("%d %d\n", a, b);
            }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    if (t_end < t0 + 0.1) t_end = t0 + 0.1;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long lim = moore < MAXV ? moore : MAXV;
    int bm[MAXK + 1] = {0, 0, 0};
    int fails[MAXK + 1] = {0, 0, 0};
    BK = 0;
    BM = 0;
    long bestN = 0;

    while (now() < t_end) {
        int k = rndint(10) < 7 ? 1 : 2;
        if (2L * k * (bm[k] + 1) > lim) {
            k = 3 - k;
            if (2L * k * (bm[k] + 1) > lim) break;
        }
        int m = bm[k] + 1;
        if (fails[k] > 60 && rndint(2)) m += 1;
        if (2L * k * m > lim) continue;
        long steps = 3000 + rndint(3000) + 1500L * (fails[k] < 60 ? fails[k] : 60);
        if (anneal(k, m, steps)) {
            bm[k] = m;
            fails[k] = 0;
            if (2L * k * m > bestN) {
                bestN = 2L * k * m;
                BK = k;
                BM = m;
                memcpy(BSIG, SIG, sizeof SIG);
                memcpy(BVOL, VOL, sizeof VOL);
            }
        } else {
            fails[k]++;
        }
    }
    print_best();
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
