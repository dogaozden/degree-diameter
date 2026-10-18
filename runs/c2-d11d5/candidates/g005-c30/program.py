"""Bi-Cayley voltage-lift search in C for the d=11, D=5 target, with a safe K_{d,d} fallback.

The C engine fixes a semidirect group Z_m x| Z_k2 and a base of K blocks per side. Each layer is a
permutation between the A and B blocks, with one group voltage per (layer, A-block) dart. Left
multiplication by any group element is an automorphism, so the lift has diameter <= D iff every
block representative (block, identity) reaches all N vertices within D steps. One evaluation is
therefore 2K BFS runs, not a full all-pairs check. Simulated annealing minimises the total number
of unreached (representative, vertex) pairs, and the order target is raised after each success.
Python keeps the best valid graph found, checks it with lib.is_valid, and falls back to K_{d,d}.
"""
import time

import lib


C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define MAXG 12000
#define MAXN (2 * MAXK * MAXG)

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Current lift state: group Z_M x| Z_K2 (element a*K2+b), K blocks per side, G = M*K2. */
static int K, G, M, K2, R, N;
static long long pw[64];
static int lay[MAXD][MAXK];   /* lay[l][i] = B-block joined to A-block i in layer l */
static int sv[MAXD][MAXK];    /* voltage of that dart */
static int adj[MAXN * MAXD];  /* adj[v*d + l] = neighbour of v in layer l */
static int vis[MAXN];
static int qu[MAXN];
static int stamp_ = 0;
static int have = 0;

/* Best lift stored for output. */
static int bK, bM, bK2, bR;
static int blay[MAXD][MAXK], bsv[MAXD][MAXK];

static long long powmod(long long b, long long e, long long m) {
    long long res = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) res = res * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return res;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void set_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    R = r;
    G = m * k2;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        pw[b] = p;
        p = (p * r) % m;
    }
}

/* (a,b)*(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long ra = (a + pw[b] * c) % M;
    int rb = (b + e) % K2;
    return (int)(ra * K2 + rb);
}

static const int K2_CHOICES[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Sample Z_m x| Z_k2 with m*k2 >= target and r^k2 = 1 mod m, gcd(r,m) = 1. */
static int sample_group(int target, int *m, int *k2, int *r) {
    int nch = (int)(sizeof(K2_CHOICES) / sizeof(int));
    for (int tries = 0; tries < 200; tries++) {
        int kk2 = K2_CHOICES[rndint(nch)];
        int mm = (target + kk2 - 1) / kk2;
        if (mm < 2) mm = 2;
        int rr = 1;
        if (kk2 > 1) {
            int found = 0;
            for (int t = 0; t < 60; t++) {
                int c = 1 + rndint(mm - 1);
                if (gcd_i(c, mm) == 1 && powmod(c, kk2, mm) == 1 % mm) {
                    rr = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        *m = mm;
        *k2 = kk2;
        *r = rr;
        return 1;
    }
    return 0;
}

static void build_adj(void) {
    N = 2 * K * G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) {
            int p = lay[l][i], s = sv[l][i];
            for (int g = 0; g < G; g++) {
                int u = i * G + g;
                int w = (K + p) * G + gmul(g, s);
                adj[u * d + l] = w;
                adj[w * d + l] = u;
            }
        }
    }
}

/* Total unreached (representative, vertex) pairs. Zero iff the lift has diameter <= D. */
static long eval_cost(void) {
    build_adj();
    long total = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        stamp_++;
        int head = 0, tail = 0;
        qu[tail++] = src;
        vis[src] = stamp_;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qu[head++];
                const int *a = adj + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int w = a[l];
                    if (vis[w] != stamp_) {
                        vis[w] = stamp_;
                        qu[tail++] = w;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) sv[l][i] = rndint(G);
    }
}

/* Simulated annealing on the current (K, G) group. Returns 1 when a valid lift is reached. */
static int anneal(double deadline, long patience) {
    random_state();
    long cost = eval_cost();
    long best = cost;
    long last = 0;
    double t_start = now();
    double span = deadline - t_start;
    if (span < 1e-3) span = 1e-3;
    double T0 = 0.05 * (double)cost + 1.0;
    double T = T0;
    for (long t = 1; cost > 0; t++) {
        if ((t & 31) == 0) {
            double nt = now();
            if (nt > deadline) break;
            double frac = (nt - t_start) / span;
            if (frac > 1.0) frac = 1.0;
            T = T0 * (1.0 - frac) + 0.05;
        }
        if (t - last > patience) break;

        if (K >= 2 && rnd01() < 0.3) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int a = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = a;
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                a = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = a;
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = sv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                sv[l][i] = old;
            }
        }
        if (cost < best) {
            best = cost;
            last = t;
        }
    }
    return cost == 0;
}

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

static void save_best(void) {
    bK = K;
    bM = M;
    bK2 = K2;
    bR = R;
    memcpy(blay, lay, sizeof lay);
    memcpy(bsv, sv, sizeof sv);
}

/* Sorted, de-duplicated neighbours of vertex u into out; returns the count. */
static int collect(int u, int *out) {
    int tmp[MAXD], c = 0;
    for (int l = 0; l < d; l++) tmp[c++] = adj[u * d + l];
    for (int i = 1; i < c; i++) {
        int x = tmp[i], j = i - 1;
        while (j >= 0 && tmp[j] > x) {
            tmp[j + 1] = tmp[j];
            j--;
        }
        tmp[j + 1] = x;
    }
    int q = 0;
    for (int i = 0; i < c; i++)
        if (i == 0 || tmp[i] != tmp[i - 1]) out[q++] = tmp[i];
    return q;
}

static void output_best(void) {
    K = bK;
    set_group(bM, bK2, bR);
    memcpy(lay, blay, sizeof lay);
    memcpy(sv, bsv, sizeof sv);
    if (eval_cost() != 0) {
        printf("0 0\n");
        return;
    }
    int nA = K * G, n = 2 * K * G;
    int out[MAXD];
    long m = 0;
    for (int u = 0; u < nA; u++) m += collect(u, out);
    printf("%d %ld\n", n, m);
    for (int u = 0; u < nA; u++) {
        int c = collect(u, out);
        for (int j = 0; j < c; j++) printf("%d %d\n", u, out[j]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long hint = argc > 5 ? atol(argv[5]) : 0;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    double t_end = now() + limit * 0.93 - 0.3;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long base = 2L * d;
    if (hint > base) base = hint;
    double delta = fmax(4.0, 0.05 * (double)base);

    while (now() < t_end && base < moore) {
        long aim = base + (long)ceil(delta);
        if (aim > moore) aim = moore;
        int k = 2 + rndint(5);                     /* base blocks per side: 2..6 */
        long Gmin = (aim + 2L * k - 1) / (2L * k);
        if (Gmin > MAXG) continue;
        int mm, kk2, rr;
        if (!sample_group((int)Gmin, &mm, &kk2, &rr)) continue;
        if ((long)mm * kk2 > MAXG) continue;
        K = k;
        set_group(mm, kk2, rr);
        long Nn = 2L * K * G;
        if (Nn > moore || Nn <= base) continue;

        double slice_end = now() + 6.0;
        if (slice_end > t_end) slice_end = t_end;
        if (anneal(slice_end, 3000)) {
            save_best();
            have = 1;
            base = Nn;
            delta = fmax(4.0, 0.04 * (double)base);
        } else {
            delta = fmax(2.0, delta * 0.6);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    output_best();
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}. It is optimal for D = 2 (bipartite Moore bound 2d).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions (these return immediately for calibration-style cases).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bi-Cayley lift search in C, seeded with the best order found so far.
    total = max(1.0, 0.85 * time_limit - 2.0)
    budget = round(total - (time.monotonic() - t0), 2)
    if budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, best_n],
                             stdin_graph=None, timeout=budget + 15)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
