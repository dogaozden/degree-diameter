"""Bi-Cayley voltage-lift search with a C annealing engine.

Base graph: K blocks per side, d permutation layers, voltages in a semidirect product
Z_m x| Z_k2. Every vertex has degree d and the graph is bipartite by construction.
The C engine anneals layers and voltages with exact reachability checks (only block
representatives are tracked, by group transitivity), and ratchets the order goal up.

Safe fallbacks: K_{d,d} (or C_{2D} for d=2), projective-plane incidence graphs, and
the Araujo-Pardo-Lopez graph. Every returned graph passes lib.is_valid.
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

#define MAXN 20000
#define MAXD 16
#define MAXK 8
#define PEN 1000L

static int d, D;
static int K, G, m, k2, N;
static long powr[64];
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static int pl[MAXD][MAXK];      /* pl[l][i]: B block joined to A block i in layer l */
static int sv[MAXD][MAXK];      /* voltage of that dart */
static int nbr[MAXD][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN], acc[MAXN];
static uint64_t *evres;

static int bestU[MAXN * MAXD / 2];
static int bestV[MAXN * MAXD / 2];
static int best_ne = 0, best_N = 0;
static long wins[MAXK + 1], trials[MAXK + 1];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long mod) {
    long r = 1 % mod;
    b %= mod;
    while (e) {
        if (e & 1) r = r * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return r;
}

/* Semidirect product Z_m x| Z_k2, element (a,b) coded as a*k2+b,
   (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    long a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long aa = (a + powr[b] * c) % m;
    return (int)(aa * k2 + (b + e) % k2);
}

static int ginv(int x) {
    long a = x / k2, b = x % k2;
    long nb = (k2 - b) % k2;
    long t = (powr[nb] * a) % m;
    long na = (m - t) % m;
    return (int)(na * k2 + nb);
}

/* Dart (l,i): A_{i,g} ~ B_{j,g*s} with j = pl[l][i], s = sv[l][i]. */
static void set_dart(int l, int i) {
    int j = pl[l][i], s = sv[l][i];
    int si = ginv(s);
    int Ab = i * G, Bb = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][Ab + g] = Bb + gmul(g, s);
        nbr[l][Bb + g] = Ab + gmul(g, si);
    }
}

/* Reach bitmasks over the 2K block representatives. Returns the number of
   (vertex, block) pairs not within distance D; the result is left in evres. */
static long eval_unreached(void) {
    uint64_t *A = bufA, *B = bufB;
    memset(A, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) A[(long)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = A[v];
            for (int l = 0; l < d; l++) x |= A[nbr[l][v]];
            B[v] = x;
            changed |= (x != A[v]);
        }
        uint64_t *t = A; A = B; B = t;
        if (!changed) break;
    }
    evres = A;
    long tot = 0;
    int full = 2 * K;
    for (int v = 0; v < N; v++) tot += full - __builtin_popcountll(A[v]);
    return tot;
}

/* Two darts of the same A block with the same B block and voltage are multi-edges. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (pl[l1][i] == pl[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    long u = eval_unreached();
    return u + PEN * dupcount();
}

static int sample_group(long target) {
    static const int ks[] = {1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 8, 9, 10, 12};
    int nks = (int)(sizeof(ks) / sizeof(ks[0]));
    for (int tr = 0; tr < 60; tr++) {
        k2 = ks[rndint(nks)];
        long mm = (target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        long r = 1;
        if (k2 > 1 && mm > 2 && (rnd() & 1)) {
            int found = 0;
            for (int t = 0; t < 200 && !found; t++) {
                long c = 1 + rndint((int)(mm - 1));
                if (gcdl(c, mm) == 1 && powmod(c, k2, mm) == 1) { r = c; found = 1; }
            }
        }
        if (2L * K * mm * k2 > MAXN) continue;
        m = (int)mm;
        G = m * k2;
        N = 2 * K * G;
        powr[0] = 1 % m;
        for (int b = 1; b < k2; b++) powr[b] = powr[b - 1] * r % m;
        return 1;
    }
    return 0;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) pl[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pl[l][i]; pl[l][i] = pl[l][j]; pl[l][j] = t;
        }
        for (int i = 0; i < K; i++) sv[l][i] = rndint(G);
        for (int i = 0; i < K; i++) set_dart(l, i);
    }
}

static int sa_search(long iters) {
    long cost = full_cost();
    memcpy(acc, evres, sizeof(uint64_t) * (size_t)N);
    if (cost == 0) return 1;
    long best_c = cost, last = 0;
    long patience = iters / 4 + 500;
    double T0 = 2.0 + 0.05 * (double)cost, T1 = 0.2;
    uint64_t full = (2 * K >= 64) ? ~0ULL : ((1ULL << (2 * K)) - 1);
    for (long t = 0; t < iters; t++) {
        if ((t & 31) == 0 && now() > t_end) break;
        if (t - last > patience) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int kind = 0, l = 0, i = 0, i2 = 0, oldS = 0;
        if (K >= 2 && rnd01() < 0.2) {
            kind = 1;
            l = rndint(d);
            i = rndint(K);
            do { i2 = rndint(K); } while (i2 == i);
            int tmp = pl[l][i]; pl[l][i] = pl[l][i2]; pl[l][i2] = tmp;
            set_dart(l, i);
            set_dart(l, i2);
        } else {
            int targeted = 0;
            if (rnd01() < 0.4) {
                int v = -1;
                for (int tr = 0; tr < 30 && v < 0; tr++) {
                    int c = rndint(N);
                    if (acc[c] != full) v = c;
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndint(d);
                    if (b < K) {
                        i = b;
                    } else {
                        int j = b - K;
                        i = 0;
                        for (int q = 0; q < K; q++)
                            if (pl[l][q] == j) { i = q; break; }
                    }
                    targeted = 1;
                }
            }
            if (!targeted) { l = rndint(d); i = rndint(K); }
            oldS = sv[l][i];
            int ns = rndint(G);
            if (ns == oldS) continue;
            sv[l][i] = ns;
            set_dart(l, i);
        }
        long c2 = full_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            memcpy(acc, evres, sizeof(uint64_t) * (size_t)N);
            if (cost < best_c) { best_c = cost; last = t; }
            if (cost == 0) return 1;
        } else {
            if (kind == 1) {
                int tmp = pl[l][i]; pl[l][i] = pl[l][i2]; pl[l][i2] = tmp;
                set_dart(l, i);
                set_dart(l, i2);
            } else {
                sv[l][i] = oldS;
                set_dart(l, i);
            }
        }
    }
    return cost == 0;
}

static void record_best(void) {
    int ne = 0;
    int A = K * G;
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++) {
            bestU[ne] = v;
            bestV[ne] = nbr[l][v];
            ne++;
        }
    best_ne = ne;
    best_N = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [best_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long bestn = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + (limit > 4.0 ? limit - 2.0 : limit * 0.6);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    double goal = bestn * 1.02 + 2.0;
    while (now() < t_end) {
        int Kc = 1;
        double bs = -1.0;
        for (int k = 1; k <= MAXK; k++) {
            double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.1 * rnd01();
            if (sc > bs) { bs = sc; Kc = k; }
        }
        if (rnd01() < 0.2) Kc = 1 + rndint(MAXK);
        K = Kc;
        long target = (long)(goal / (2.0 * K)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target) || 2L * K * G <= bestn) {
            goal = bestn * 1.01 + 1.0;
            continue;
        }
        trials[K]++;
        random_state();
        if (sa_search(8000)) {
            wins[K]++;
            record_best();
            bestn = N;
            goal = N * 1.03 + 1.0;
        } else {
            double g2 = bestn * 1.01 + 1.0;
            double g3 = goal * 0.995;
            goal = g3 > g2 ? g3 : g2;
        }
    }

    if (best_ne == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_N, best_ne);
    for (int e = 0; e < best_ne; e++) printf("%d %d\n", bestU[e], bestV[e]);
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

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D == 2:
        return best

    # Exact constructions (valid for every D >= 3).
    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    except Exception:
        pass
    if D == 3 and lib.is_prime_power(d - 1):
        return best
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bi-Cayley lift search in C, started from the order goal set by best_n.
    remaining = final - time.monotonic() - 3.0
    if remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             timeout=remaining + 15.0)
            n, e = lib.parse_graph_text(text)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    return best
