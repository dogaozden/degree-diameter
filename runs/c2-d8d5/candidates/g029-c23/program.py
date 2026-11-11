"""Bi-Cayley lift search (bold rewrite).

Construction: a bipartite lift of a d-regular base multigraph on k+k blocks.
Each layer l is a bijection between the A blocks and the B blocks, and each
dart carries a voltage in a finite group G = Z_M x| Z_K2. The lift has
2*k*|G| vertices and is d-regular, with edges A(i,x) -- B(j, x*s).

G acts on the lift by left multiplication and preserves both sides, so the
diameter check only needs BFS from the 2k block representatives. The C
annealer uses this to search voltages and layer permutations far faster than
the previous numpy version. It keeps the largest valid lift found, and it
samples the block count k and the group order g over a window just above the
current best order.

Fallbacks: K_{d,d} always, and the projective-plane incidence graph for D = 3.
Every returned graph passes lib.is_valid.
"""
import math
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

#define DMAX 64
#define KMAX 8
#define NCAP (1 << 21)

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndd(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* Group Z_M x| Z_K2 (order G = M*K2), element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int d, D, K, G, M, K2, R;
static int rp[64];
static int Afwd[DMAX][KMAX], Sv[DMAX][KMAX], Binv[DMAX][KMAX], Bv[DMAX][KMAX];
static int *vis, *qbuf;
static int stamp = 0;

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int a2 = (int)(((long long)a + (long long)rp[b] * c) % M);
    int b2 = (b + e) % K2;
    return a2 * K2 + b2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = (long long)rp[nb] * a % M;
    int a2 = (int)((M - t) % M);
    return a2 * K2 + nb;
}

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = ((b % m) + m) % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void powtable(void) {
    rp[0] = 1 % M;
    for (int b = 1; b < K2; b++) rp[b] = (int)((long long)rp[b - 1] * R % M);
}

static void make_group(int g) {
    int divs[32], nd = 0;
    for (int t = 1; t <= 12 && t <= g; t++) if (g % t == 0) divs[nd++] = t;
    K2 = (rndd() < 0.4) ? 1 : divs[rndi(nd)];
    M = g / K2;
    G = g;
    R = 0;
    if (K2 > 1 && M > 1) {
        R = 1;
        for (int t = 0; t < 300; t++) {
            int r = 1 + rndi(M - 1);
            if (gcd_(r, M) == 1 && powmod(r, K2, M) == 1 % M) { R = r; break; }
        }
    }
    powtable();
}

static void layer_tables(int l) {
    for (int i = 0; i < K; i++) {
        int j = Afwd[l][i];
        Binv[l][j] = i;
        Bv[l][j] = ginv(Sv[l][i]);
    }
}

static void rand_state(void) {
    for (int l = 0; l < d; l++) {
        int p[KMAX];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            Afwd[l][i] = p[i];
            Sv[l][i] = rndi(G);
        }
        layer_tables(l);
    }
}

/* Neighbour of vertex v along layer l. A block i occupies ids i*G..; B block j occupies (K+j)*G.. */
static inline int nbr(int v, int l) {
    int KG = K * G;
    int x = v % G;
    if (v < KG) {
        int i = v / G;
        return (K + Afwd[l][i]) * G + gmul(x, Sv[l][i]);
    } else {
        int j = v / G - K;
        return Binv[l][j] * G + gmul(x, Bv[l][j]);
    }
}

/* Number of vertices at distance > D from src. */
static long long rep_cost(int src) {
    int N = 2 * K * G;
    if (++stamp == 0x7fffffff) {
        memset(vis, 0, sizeof(int) * NCAP);
        stamp = 1;
    }
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    vis[src] = stamp;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            for (int l = 0; l < d; l++) {
                int u = nbr(v, l);
                if (vis[u] != stamp) {
                    vis[u] = stamp;
                    qbuf[tail++] = u;
                }
            }
        }
        if (tail == N) break;
    }
    return (long long)(N - tail);
}

/* Orbit representatives: x = 0 in each block. Zero cost means diameter <= D. */
static long long full_cost(void) {
    long long c = 0;
    for (int b = 0; b < 2 * K; b++) c += rep_cost(b * G);
    return c;
}

/* Simulated annealing over voltages and layer permutations, time-bounded. */
static int anneal(double end) {
    double start = now();
    double span = end - start;
    if (span <= 0) return 0;
    rand_state();
    long long cost = full_cost();
    const double T0 = 2.0, T1 = 0.05;
    double T = T0;
    long long it = 0;
    while (cost > 0) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn >= end) return 0;
            double frac = (tn - start) / span;
            if (frac > 1.0) frac = 1.0;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        int typ, l, i1, i2 = -1, oldv = 0;
        if (K >= 2 && rndd() < 0.3) {
            typ = 1;
            l = rndi(d);
            i1 = rndi(K);
            i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int t = Afwd[l][i1]; Afwd[l][i1] = Afwd[l][i2]; Afwd[l][i2] = t;
            layer_tables(l);
        } else {
            typ = 0;
            l = rndi(d);
            i1 = rndi(K);
            oldv = Sv[l][i1];
            int nv = rndi(G - 1);
            if (nv >= oldv) nv++;
            Sv[l][i1] = nv;
            layer_tables(l);
        }
        long long nc = full_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            if (typ == 1) {
                int t = Afwd[l][i1]; Afwd[l][i1] = Afwd[l][i2]; Afwd[l][i2] = t;
            } else {
                Sv[l][i1] = oldv;
            }
            layer_tables(l);
        }
    }
    return 1;
}

static void emit(void) {
    int KG = K * G, N = 2 * KG;
    long long cap = (long long)KG * d;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    long long m = 0;
    int nb[DMAX];
    for (int v = 0; v < KG; v++) {
        for (int l = 0; l < d; l++) nb[l] = nbr(v, l);
        for (int a = 1; a < d; a++) {
            int x = nb[a], b = a - 1;
            while (b >= 0 && nb[b] > x) { nb[b + 1] = nb[b]; b--; }
            nb[b + 1] = x;
        }
        for (int a = 0; a < d; a++) {
            if (a == 0 || nb[a] != nb[a - 1]) {
                eu[m] = v;
                ev[m] = nb[a];
                m++;
            }
        }
    }
    printf("%d %lld\n", N, m);
    for (long long e = 0; e < m; e++) printf("%d %d\n", eu[e], ev[e]);
    free(eu);
    free(ev);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    int startN = atoi(argv[5]);
    int kmax = argc > 6 ? atoi(argv[6]) : 6;
    if (d < 1 || d > DMAX || D < 1 || kmax < 1) { printf("0 0\n"); return 0; }
    if (kmax > KMAX) kmax = KMAX;

    vis = calloc(NCAP, sizeof(int));
    qbuf = malloc(sizeof(int) * NCAP);
    if (!vis || !qbuf) { printf("0 0\n"); return 0; }

    static int sA[DMAX][KMAX], sS[DMAX][KMAX];
    int bestN = startN, bK = 0, bG = 0, bM = 0, bK2 = 0, bR = 0;
    int found = 0;

    double t0 = now();
    while (now() - t0 < tl) {
        int k = 1 + rndi(kmax);
        int base = bestN / (2 * k) + 1;
        int W = base / 20 + 1;
        int g = base + rndi(W);
        if (g < 2) g = 2;
        if (2LL * k * g > NCAP) continue;
        K = k;
        make_group(g);
        double remain = tl - (now() - t0);
        double slice = tl * 0.1;
        if (slice < 1.0) slice = 1.0;
        if (slice > remain) slice = remain;
        if (slice <= 0) break;
        if (anneal(now() + slice)) {
            bestN = 2 * K * G;
            found = 1;
            for (int l = 0; l < d; l++)
                for (int i = 0; i < K; i++) {
                    sA[l][i] = Afwd[l][i];
                    sS[l][i] = Sv[l][i];
                }
            bK = K; bG = G; bM = M; bK2 = K2; bR = R;
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    K = bK; G = bG; M = bM; K2 = bK2; R = bR;
    powtable();
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            Afwd[l][i] = sA[l][i];
            Sv[l][i] = sS[l][i];
        }
    for (int l = 0; l < d; l++) layer_tables(l);
    emit();
    return 0;
}
"""


KMAX_ARG = 6


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _lift_search(d, D, seed, seconds, start_n):
    """Run the C bi-Cayley lift annealer; returns parsed (n, edges), possibly (0, [])."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", start_n, KMAX_ARG],
                    stdin_graph=None, timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    best = fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 when d - 1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    budget = time_limit - (time.monotonic() - t0) - 6.0
    if budget >= 2.0:
        try:
            n, e = _lift_search(d, D, seed, budget, best[0])
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
