"""Bi-Cayley lift search engine in C, with exact constructions as fallbacks.

Each candidate is a d-regular bipartite lift over a semidirect product Z_M x| Z_K2 with a
base of K + K vertices. Layer l pairs A_i with B_{sig[l][i]} through a voltage sv[l][i]. The C
annealer minimises the number of (vertex, block) pairs at distance > D. Left multiplication is
an automorphism, so checking the eccentricity of the K+K block representatives is enough.
Every returned graph is checked with lib.is_valid, and K_{d,d} is the fallback.
"""
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

#define MAXK 8
#define PEN 12

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int d, D;
static long moore;
static double t_end;

/* current lift */
static int K, G, M, K2;
static long NN;
static int *rp;               /* rp[b] = r^b mod M */
static int *sig, *sv, *isig;  /* sig, sv indexed [l*K+i]; isig indexed [l*K+p] */
static int *nbr;              /* nbr[l*NN+v] */
static uint64_t *cur, *nxt;

static long gcdl(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }
static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect product: element a*K2+b, (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = (a + (long long)rp[b] * c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long ap = (M - ((long long)a * rp[nb]) % M) % M;
    return (int)(ap * K2 + nb);
}

static long moore_bound(void) {
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        if (s > 1000000000L) break;
        p *= (d - 1);
        if (p > 1000000000L) p = 1000000000L;
    }
    return 2 * s;
}

/* A vertex (i,g) = i*G+g; B vertex (p,h) = (K+p)*G+h.
 * Edge: A_{i,g} ~ B_{sig[l][i], g*sv[l][i]} in layer l. */
static void fill_layer(int l) {
    int *nb = nbr + (size_t)l * (size_t)NN;
    for (int i = 0; i < K; i++) isig[l * K + sig[l * K + i]] = i;
    for (int i = 0; i < K; i++) {
        int p = sig[l * K + i], s = sv[l * K + i];
        for (int g = 0; g < G; g++) nb[i * G + g] = (K + p) * G + gmul(g, s);
    }
    for (int p = 0; p < K; p++) {
        int i = isig[l * K + p];
        int si = ginv(sv[l * K + i]);
        for (int h = 0; h < G; h++) nb[(K + p) * G + h] = i * G + gmul(h, si);
    }
}

/* Cost = (vertex, block) pairs at distance > D, plus penalty for duplicate darts. */
static long eval_cost(void) {
    int twoK = 2 * K;
    for (long v = 0; v < NN; v++) cur[v] = 0;
    for (int b = 0; b < twoK; b++) cur[(long)b * G] |= 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (long v = 0; v < NN; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[(long)l * NN + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long unr = 0;
    for (long v = 0; v < NN; v++) unr += twoK - __builtin_popcountll(cur[v]);
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig[l * K + i] == sig[l2 * K + i] && sv[l * K + i] == sv[l2 * K + i]) dup++;
    return unr + PEN * dup;
}

static long anneal(long maxit, long patience) {
    long cost = eval_cost();
    long bestc = cost, last = 0;
    for (long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 15) == 0 && now() > t_end) break;
        if (it - last > patience) break;
        double T = 2.0 * (1.0 - (double)it / (double)maxit) + 0.05;
        int l = rndint(d);
        if (K == 1 || rnd01() < 0.6) {
            int idx = l * K + rndint(K);
            int old = sv[idx];
            int nw = rndint(G);
            if (nw == old) continue;
            sv[idx] = nw;
            fill_layer(l);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                sv[idx] = old;
                fill_layer(l);
            }
        } else {
            int a = l * K + rndint(K), b = l * K + rndint(K);
            if (a == b) continue;
            int t = sig[a]; sig[a] = sig[b]; sig[b] = t;
            fill_layer(l);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                t = sig[a]; sig[a] = sig[b]; sig[b] = t;
                fill_layer(l);
            }
        }
        if (cost < bestc) { bestc = cost; last = it; }
    }
    return cost;
}

static void setup(int k, long Mc, int k2) {
    K = k;
    M = (int)Mc;
    K2 = k2;
    G = M * K2;
    NN = 2L * K * G;
    long r = 1;
    if (K2 > 1 && M >= 3) {
        for (int tr = 0; tr < 300; tr++) {
            long c = 2 + rndint(M - 2);
            if (gcdl(c, M) == 1 && powmodl(c, K2, M) == 1 % M) { r = c; break; }
        }
    }
    rp = malloc(sizeof(int) * (size_t)K2);
    rp[0] = 1 % M;
    for (int b = 1; b < K2; b++) rp[b] = (int)((long long)rp[b - 1] * r % M);
    sig = malloc(sizeof(int) * (size_t)d * K);
    sv = malloc(sizeof(int) * (size_t)d * K);
    isig = malloc(sizeof(int) * (size_t)d * K);
    nbr = malloc(sizeof(int) * (size_t)d * (size_t)NN);
    cur = malloc(sizeof(uint64_t) * (size_t)NN);
    nxt = malloc(sizeof(uint64_t) * (size_t)NN);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) sig[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[l * K + i]; sig[l * K + i] = sig[l * K + j]; sig[l * K + j] = t;
        }
        for (int i = 0; i < K; i++) sv[l * K + i] = rndint(G);
    }
    for (int l = 0; l < d; l++) fill_layer(l);
}

static void free_all(void) {
    free(rp); free(sig); free(sv); free(isig); free(nbr); free(cur); free(nxt);
}

static const int KCH[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long min_n = atol(argv[5]);
    t_end = now() + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || D < 2 || d > 64) { printf("0 0\n"); return 0; }
    moore = moore_bound();

    long best_n = min_n;
    int *bestnbr = NULL;
    long bestNN = 0;
    int bestK = 0, bestG = 0;
    int nk = (int)(sizeof(KCH) / sizeof(KCH[0]));

    while (now() < t_end) {
        if (best_n + 2 > moore) break;
        int k = 1 + rndint(MAXK);
        double frac = 1.01 + 0.04 * rnd01();
        long need = (long)((double)best_n * frac) / (2L * k) + 1;
        int k2 = KCH[rndint(nk)];
        long Mc = (need + k2 - 1) / k2;
        if (Mc < 2) Mc = 2;
        long Gc = Mc * k2;
        long N = 2L * k * Gc;
        if (N > moore || N > 400000L || N <= best_n) continue;

        setup(k, Mc, k2);
        long cost = anneal(15000, 3000);
        if (cost == 0 && NN > best_n) {
            best_n = NN;
            free(bestnbr);
            bestnbr = malloc(sizeof(int) * (size_t)d * (size_t)NN);
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)d * (size_t)NN);
            bestNN = NN;
            bestK = K;
            bestG = G;
        }
        free_all();
    }

    if (bestnbr) {
        long KG = (long)bestK * bestG;
        printf("%ld %ld\n", bestNN, KG * d);
        for (long u = 0; u < KG; u++)
            for (int l = 0; l < d; l++)
                printf("%ld %d\n", u, bestnbr[(long)l * bestNN + u]);
    } else {
        printf("0 0\n");
    }
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    # Exact constructions (diameter 3 graphs are also valid for D >= 3).
    if D >= 3 and d >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Main search: C bi-Cayley lift annealing, ratcheted above the best fallback order.
    budget = 0.8 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget >= 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                             stdin_graph=None, timeout=budget + 3.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
