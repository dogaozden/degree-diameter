"""Voltage-lift search over semidirect groups Z_m x| Z_k2 for the bipartite
degree/diameter problem.

A candidate is a bi-Cayley lift with K blocks per side. Each block pair is
joined by d darts (layer permutations plus group voltages). The C engine
anneals the voltages and layer permutations so that every vertex reaches
every block representative within distance D. Lift symmetry makes that
equivalent to diameter <= D. The search grows the best valid order found so
far, and every returned graph is checked with lib.is_valid.
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

#define MAXD 16
#define MAXK 8
#define MAXPW 64

typedef uint64_t u64;
typedef uint32_t u32;

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (u64)n); }
static double rndd(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d, D, K, M, K2, R, G, NV;
static int pw[MAXPW];
static int perm[MAXD][MAXK], iperm[MAXD][MAXK], volt[MAXD][MAXK], vinv[MAXD][MAXK];
static int *nb;
static u32 *ra, *rb;
static const int PEN = 20;
static const int RUN = 20000;

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* Semidirect product Z_M x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + R^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int a2 = (int)((a + (long long)pw[b] * c) % M);
    int b2 = (b + e) % K2;
    return a2 * K2 + b2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nbb = (K2 - b) % K2;
    int t = (int)((long long)pw[nbb] * a % M);
    int a2 = (M - t) % M;
    return a2 * K2 + nbb;
}

static void refresh_inv(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) vinv[l][i] = ginv(volt[l][i]);
}

/* A-vertex i*G+x  ~  B-vertex (K+j)*G + x*s  for dart (i -> j = perm[l][i], s = volt[l][i]). */
static void build_nb(void) {
    refresh_inv();
    for (int i = 0; i < K; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < d; l++)
                nb[v * d + l] = (K + perm[l][i]) * G + gmul(x, volt[l][i]);
        }
    for (int j = 0; j < K; j++)
        for (int y = 0; y < G; y++) {
            int w = (K + j) * G + y;
            for (int l = 0; l < d; l++) {
                int i = iperm[l][j];
                nb[w * d + l] = i * G + gmul(y, vinv[l][i]);
            }
        }
}

static int count_dup(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && volt[l1][i] == volt[l2][i]) dup++;
    return dup;
}

/* Cost = (vertex, block) pairs not within distance D, plus duplicate-dart penalty. */
static long long evaluate(void) {
    build_nb();
    int dup = count_dup();
    u32 *cur = ra, *nxt = rb;
    for (int v = 0; v < NV; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            u32 x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nb[v * d + l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u32 *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long long un = 0;
    for (int v = 0; v < NV; v++) un += 2 * K - __builtin_popcount(cur[v]);
    return un + (long long)PEN * dup;
}

static void randomize_state(void) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            perm[l][i] = p[i];
            iperm[l][p[i]] = i;
            volt[l][i] = rndi(G);
        }
    }
}

/* Swapping the same positions twice restores the state. */
static void swap_perm(int l, int i1, int i2) {
    int a = perm[l][i1], b = perm[l][i2];
    perm[l][i1] = b; perm[l][i2] = a;
    iperm[l][b] = i1; iperm[l][a] = i2;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;

    if (d < 1 || d > MAXD || D < 1 || K < 1 || K > MAXK || M < 2 ||
        K2 < 1 || K2 >= MAXPW || R < 1 || R >= M) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_i(R, M) != 1) { printf("0 0\n"); return 0; }
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * R % M);
    if ((long long)pw[K2 - 1] * R % M != 1 % M) { printf("0 0\n"); return 0; }

    G = M * K2;
    NV = 2 * K * G;
    if (G < 2 || NV > 200000) { printf("0 0\n"); return 0; }

    nb = malloc(sizeof(int) * (size_t)NV * d);
    ra = malloc(sizeof(u32) * (size_t)NV);
    rb = malloc(sizeof(u32) * (size_t)NV);
    if (!nb || !ra || !rb) { printf("0 0\n"); return 0; }

    const double T0 = 10.0, T1 = 0.3;
    clock_t c0 = clock();
    int found = 0;

    while (!found) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        randomize_state();
        long long cost = evaluate();

        for (int it = 0; it < RUN; it++) {
            if ((it & 127) == 0) {
                double el2 = (double)(clock() - c0) / CLOCKS_PER_SEC;
                if (el2 >= tl) break;
            }
            double frac = (double)it / (double)RUN;
            double T = T0 * pow(T1 / T0, frac);

            int kind = 0, l = 0, i1 = 0, i2 = 0, oldv = 0, nv = 0;
            if (K >= 2 && rndd() < 0.15) {
                kind = 1;
                l = rndi(d);
                i1 = rndi(K);
                i2 = rndi(K - 1);
                if (i2 >= i1) i2++;
                swap_perm(l, i1, i2);
            } else {
                kind = 0;
                l = rndi(d);
                i1 = rndi(K);
                oldv = volt[l][i1];
                nv = rndi(G - 1);
                if (nv >= oldv) nv++;
                volt[l][i1] = nv;
            }

            long long nc = evaluate();
            long long delta = nc - cost;
            if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
                cost = nc;
                if (cost == 0) { found = 1; break; }
            } else {
                if (kind == 1) swap_perm(l, i1, i2);
                else volt[l][i1] = oldv;
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }

    build_nb();
    printf("%d %d\n", NV, K * G * d);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[v * d + l]);
    return 0;
}
"""


_K_CHOICES = (1, 2, 3, 4, 5, 6)
_K2_CHOICES = (1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x| Z_k2 with order m*k2 >= target, or None."""
    for _ in range(100):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        units = [c for c in range(1, m)
                 if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if not units:
            continue
        return m, k2, rng.choice(units)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact or known constructions for D = 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            n2, e2 = lib.araujo_lopez_graph(d - 2)
            consider(n2, e2)
        except Exception:
            pass

    # Main search: voltage lifts over semidirect products, anneal in C,
    # keep growing the best valid order.
    deadline = t0 + max(2.0, 0.85 * time_limit - 2.0)
    trials = {k: 0 for k in _K_CHOICES}
    wins = {k: 0 for k in _K_CHOICES}
    errors = 0
    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 1.5 or errors >= 3:
                break

            if rng.random() < 0.25:
                k = rng.choice(_K_CHOICES)
            else:
                k = max(_K_CHOICES,
                        key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.05 * rng.random())

            base_n = best[0]
            gmin = base_n // (2 * k) + 1
            target = gmin + rng.randrange(0, gmin // 60 + 1)
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
            if 2 * k * m * k2 <= base_n:
                continue

            slice_t = min(remaining - 0.5, 3.0 + 7.0 * rng.random())
            if slice_t < 0.5:
                break
            trials[k] += 1
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, rng.randrange(1, 1 << 30), f"{slice_t:.2f}", k, m, k2, r],
                    timeout=slice_t + 15.0,
                )
                n2, e2 = lib.parse_graph_text(out)
            except Exception:
                errors += 1
                continue
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
                wins[k] += 1
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
