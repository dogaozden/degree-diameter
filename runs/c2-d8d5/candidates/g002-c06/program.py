import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define PEN 1000L
#define ITERS 8000
#define PATIENCE 2000

/* Bi-Cayley lifts over groups G = Z_M x| Z_K2 (element a*K2+b, (a,b)(c,f) = (a+r^b c, b+f)).
   Base graph: K block indices on each side (A: 0..K-1, B: K..2K-1), d layers.
   Layer l joins A-block i to B-block sig[l][i] (sig[l] is a permutation) with voltage vol[l][i]:
   (A,i,x) ~ (B,j,x*s). Every vertex then has degree d. Cost = unreached (vertex, block) pairs
   + PEN * duplicate darts. Cost 0 means diameter <= D. */

static int d, D;
static int K, G, M, K2;
static int pw[64];
static uint64_t rs;
static double budget;
static clock_t t0;
static int best_n = 0, best_m = 0, found = 0;
static int *best_eu = NULL, *best_ev = NULL;
static int *sig = NULL, *vol = NULL, *nbr = NULL;
static uint64_t *bufA = NULL, *bufB = NULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC > budget; }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, f = y % K2;
    int A = (int)(((long long)a + (long long)pw[b] * c) % M);
    int B = (b + f) % K2;
    return A * K2 + B;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int t = (int)(((long long)pw[nb] * a) % M);
    int A = (M - t) % M;
    return A * K2 + nb;
}

/* Recompute the neighbour entries touched by dart (layer l, A-block i). */
static void upd(int l, int i) {
    int j = sig[l * K + i], s = vol[l * K + i], si = ginv(s);
    for (int x = 0; x < G; x++) {
        int a = i * G + x;
        nbr[(size_t)a * d + l] = (K + j) * G + gmul(x, s);
        int b = (K + j) * G + x;
        nbr[(size_t)b * d + l] = i * G + gmul(x, si);
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (sig[l1 * K + i] == sig[l2 * K + i] && vol[l1 * K + i] == vol[l2 * K + i]) c++;
    return c;
}

static long evalcost(void) {
    int N = 2 * K * G;
    int full2 = 2 * K;
    uint64_t *R = bufA, *S = bufB;
    for (int v = 0; v < N; v++) R[v] = 0;
    for (int b = 0; b < full2; b++) R[(size_t)b * G] |= 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = R[v];
            const int *nv = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= R[nv[l]];
            S[v] = x;
            if (x != R[v]) changed = 1;
        }
        uint64_t *tmp = R; R = S; S = tmp;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += full2 - __builtin_popcountll(R[v]);
    return unr;
}

static long fullcost(void) {
    return evalcost() + PEN * (long)dupcount();
}

/* Choose a random group of order >= target: Z_M x| Z_K2 with r^K2 = 1 mod M. */
static void setup_group(int target) {
    static const int k2s[] = {1, 1, 1, 2, 2, 3, 4, 5, 6, 8};
    int k2 = k2s[rndint(10)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && m > 2 && rnd01() < 0.7) {
        for (int tries = 0; tries < 200; tries++) {
            int c = 2 + rndint(m - 2);
            if (gcd_i(c, m) == 1 && powmod_i(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    M = m;
    K2 = k2;
    G = m * k2;
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * r % M);
}

static void run_trial(void) {
    int N = 2 * K * G;
    sig = malloc(sizeof(int) * (size_t)d * K);
    vol = malloc(sizeof(int) * (size_t)d * K);
    nbr = malloc(sizeof(int) * (size_t)N * d);
    bufA = malloc(sizeof(uint64_t) * (size_t)N);
    bufB = malloc(sizeof(uint64_t) * (size_t)N);
    if (!sig || !vol || !nbr || !bufA || !bufB) {
        free(sig); free(vol); free(nbr); free(bufA); free(bufB);
        sig = vol = NULL; nbr = NULL; bufA = bufB = NULL;
        return;
    }

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) sig[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[l * K + i];
            sig[l * K + i] = sig[l * K + j];
            sig[l * K + j] = t;
        }
        for (int i = 0; i < K; i++) vol[l * K + i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) upd(l, i);

    long cost = fullcost();
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best_c = cost, last = 0;

    for (long it = 0; it < ITERS && cost > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        if (it - last > PATIENCE) break;
        double temp = 0.5 + 0.03 * c0 * (1.0 - (double)it / ITERS);
        long nc;
        if (K >= 2 && rnd01() < 0.3) {
            int l = rndint(d);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = sig[l * K + i1];
            sig[l * K + i1] = sig[l * K + i2];
            sig[l * K + i2] = t;
            upd(l, i1);
            upd(l, i2);
            nc = fullcost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                t = sig[l * K + i1];
                sig[l * K + i1] = sig[l * K + i2];
                sig[l * K + i2] = t;
                upd(l, i1);
                upd(l, i2);
                continue;
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int idx = l * K + i;
            int old = vol[idx];
            int nv = rndint(G);
            if (nv == old) continue;
            vol[idx] = nv;
            upd(l, i);
            nc = fullcost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                vol[idx] = old;
                upd(l, i);
                continue;
            }
        }
        if (cost < best_c) { best_c = cost; last = it; }
    }

    if (cost == 0 && N > best_n) {
        int nA = K * G;
        int me = nA * d;
        int *eu = malloc(sizeof(int) * (size_t)me);
        int *ev = malloc(sizeof(int) * (size_t)me);
        if (eu && ev) {
            int k = 0;
            for (int a = 0; a < nA; a++)
                for (int l = 0; l < d; l++) {
                    eu[k] = a;
                    ev[k] = nbr[(size_t)a * d + l];
                    k++;
                }
            free(best_eu);
            free(best_ev);
            best_eu = eu;
            best_ev = ev;
            best_m = me;
            best_n = N;
            found = 1;
        } else {
            free(eu);
            free(ev);
        }
    }

    free(sig); free(vol); free(nbr); free(bufA); free(bufB);
    sig = vol = NULL;
    nbr = NULL;
    bufA = bufB = NULL;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed seconds minN\n");
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    int minN = atoi(argv[5]);
    best_n = minN;
    if (d < 1 || D < 1 || d > 60) {
        printf("0 0\n");
        return 0;
    }
    t0 = clock();

    static const int Ks[] = {1, 2, 2, 3, 3, 4, 5, 6, 8};
    while (!timeup()) {
        K = Ks[rndint(9)];
        int cur = best_n;
        int base = cur / (2 * K);
        int target = base + 1 + rndint(base / 40 + 1);
        setup_group(target);
        run_trial();
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
    return 0;
}
"""


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions for D = 3.
    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1) and best_n == pg[0]:
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main search: bi-Cayley lifts over semidirect products, searched in C.
    budget = time_limit * 0.85 - 2.0 - (time.monotonic() - start)
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                            timeout=budget + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
