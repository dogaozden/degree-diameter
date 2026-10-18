"""Bi-Cayley lift search in C with transitive reach cost, plus exact seeds.

Vertices of a lift over a group G: A_{i,g} = i*G + g and B_{p,h} = (K+p)*G + h, with K base
vertices per side. Layer l is a perfect matching A_{i,g} ~ B_{p,g*s}, with p = layers[l][i] and
voltage s = S[l][i], so the graph is d-regular and bipartite. Left translations are automorphisms,
so the diameter check only needs distances from the 2K representatives g = identity. The C engine
anneals layer permutations and voltages on a bitmask deficit (unreached representative pairs plus
duplicate-edge penalty), over semidirect products Z_M x| Z_K2. It accepts only lifts strictly
larger than the best graph seen so far, which ratchets the order upward.

Python supplies the exact seeds (projective planes, Araujo-Pardo-Lopez graph), calls the C engine
with the remaining time, and returns the largest graph that lib.is_valid accepts.
"""
import time

import lib


C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXDEG 24
#define MAXK 4
#define MAXG 12000
#define MAXNV (2 * MAXK * MAXG)
#define MAXK2 40
#define PEN 1000
#define PATIENCE 4000

static int d, D;
static int K, M, K2, R, G, N;
static int layers[MAXDEG][MAXK], S[MAXDEG][MAXK], invlay[MAXDEG][MAXK];
static int powr[MAXK2], ginv[MAXG];
static int nbr[MAXDEG * MAXNV];
static uint16_t reA[MAXNV], reB[MAXNV], curreach[MAXNV];
static uint16_t *g_res;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

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

static long long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2LL * D;
    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000LL) break;
    }
    return 2 * s;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Semidirect product Z_M x| Z_K2, element (a,b) coded as a*K2+b, (a,b)*(c,e) = (a + R^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)powr[b] * c + a) % M;
    return (int)t * K2 + (b + e) % K2;
}

static void setup_group(void) {
    G = M * K2;
    N = 2 * K * G;
    powr[0] = 1 % M;
    for (int b = 1; b < K2; b++) powr[b] = (int)((long long)powr[b - 1] * R % M);
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2, nb = (K2 - b) % K2;
        long long ia = (M - ((long long)powr[nb] * a) % M) % M;
        ginv[x] = (int)ia * K2 + nb;
    }
}

static void build_layer(int l) {
    int *nb = nbr + (size_t)l * N;
    for (int i = 0; i < K; i++) invlay[l][layers[l][i]] = i;
    for (int i = 0; i < K; i++) {
        int p = layers[l][i], s = S[l][i], si = ginv[s];
        for (int g = 0; g < G; g++) nb[i * G + g] = (K + p) * G + gmul(g, s);
        for (int h = 0; h < G; h++) nb[(K + p) * G + h] = i * G + gmul(h, si);
    }
}

static long dupcount(void) {
    long cnt = 0;
    int tot = d * K;
    for (int a = 0; a < tot; a++) {
        int la = a / K, ia = a % K;
        for (int b = a + 1; b < tot; b++) {
            int lb = b / K, ib = b % K;
            if (ia == ib && layers[la][ia] == layers[lb][ib] && S[la][ia] == S[lb][ib]) cnt++;
        }
    }
    return cnt;
}

/* Deficit = unreached (vertex, representative) pairs + penalty for duplicate darts.
 * Result bitmasks are left in g_res. */
static long full_cost(void) {
    uint16_t *cur = reA, *nxt = reB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = (uint16_t)(1u << b);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint16_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l * N + v]];
            nxt[v] = x;
        }
        uint16_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    g_res = cur;
    long unre = 0;
    int full = 2 * K;
    for (int v = 0; v < N; v++) unre += full - __builtin_popcount(cur[v]);
    return unre + PEN * dupcount();
}

static int accept(long c2, long cost, double T) {
    if (c2 <= cost) return 1;
    return rnd01() < exp(-(double)(c2 - cost) / T);
}

static int anneal(double deadline) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layers[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        build_layer(l);
    }
    long cost = full_cost();
    memcpy(curreach, g_res, sizeof(uint16_t) * N);
    if (cost == 0) return 1;
    double c0 = (double)cost;
    if (c0 < 1) c0 = 1;
    double T0 = 0.02 * c0 + 1.0;
    long best = cost, last_imp = 0;
    int full = (1 << (2 * K)) - 1;

    for (long it = 1;; it++) {
        if ((it & 31) == 0 && now() > deadline) return 0;
        if (it - last_imp > PATIENCE) return 0;
        double T = T0 * exp(-(double)it / 4000.0);
        if (T < 0.5) T = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = t;
            build_layer(l);
            long c2 = full_cost();
            if (accept(c2, cost, T)) {
                cost = c2;
                memcpy(curreach, g_res, sizeof(uint16_t) * N);
            } else {
                t = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = t;
                build_layer(l);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            if (rnd01() < 0.4) {
                for (int tr = 0; tr < 30; tr++) {
                    int v = rndint(N);
                    if (curreach[v] != full) {
                        int blk = v / G;
                        if (blk < K) i = blk;
                        else i = invlay[l][blk - K];
                        break;
                    }
                }
            }
            int old = S[l][i], nv = rndint(G);
            if (nv == old) continue;
            S[l][i] = nv;
            build_layer(l);
            long c2 = full_cost();
            if (accept(c2, cost, T)) {
                cost = c2;
                memcpy(curreach, g_res, sizeof(uint16_t) * N);
            } else {
                S[l][i] = old;
                build_layer(l);
            }
        }
        if (cost < best) {
            best = cost;
            last_imp = it;
        }
        if (cost == 0) return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long best_n = atol(argv[5]);
    if (d < 3 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + limit;
    long long mb = moore_bound();

    static const int K2LIST[18] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    int found = 0;
    int sK = 0, sM = 0, sK2 = 0, sR = 1;
    static int sL[MAXDEG][MAXK], sS[MAXDEG][MAXK];

    while (now() < t_end - 0.5 && best_n < mb) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    k = c;
                }
            }
        }
        int kk2 = K2LIST[rndint(18)];
        long long gmin = best_n / (2LL * k) + 1;
        long long m = (gmin + kk2 - 1) / kk2 + rndint(3);
        if (m < 2) m = 2;
        if (2LL * k * m * kk2 > mb || 2LL * k * m * kk2 > MAXNV || m * kk2 > MAXG) continue;

        int r = 1;
        if (kk2 > 1 && m > 2 && rnd01() >= 0.3) {
            r = -1;
            for (int tr = 0; tr < 80; tr++) {
                long long c = 2 + rndint((int)(m - 2));
                if (gcdll(c, m) == 1 && powmod(c, kk2, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
            if (r < 0) continue;
        }

        K = k;
        M = (int)m;
        K2 = kk2;
        R = r;
        setup_group();
        trials[k]++;
        double remaining = t_end - now();
        double attempt = remaining / 6.0;
        if (attempt < 1.5) attempt = 1.5;
        if (attempt > 15.0) attempt = 15.0;
        if (attempt > remaining) attempt = remaining;
        if (anneal(now() + attempt)) {
            wins[k]++;
            found = 1;
            best_n = N;
            sK = K;
            sM = M;
            sK2 = K2;
            sR = R;
            memcpy(sL, layers, sizeof(layers));
            memcpy(sS, S, sizeof(S));
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    K = sK;
    M = sM;
    K2 = sK2;
    R = sR;
    setup_group();
    memcpy(layers, sL, sizeof(layers));
    memcpy(S, sS, sizeof(S));
    for (int l = 0; l < d; l++) build_layer(l);
    printf("%d %ld\n", N, (long)d * K * G);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, nbr[l * N + v]);
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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact seeds.
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

    # Bi-Cayley lift search in C, starting from the best exact graph found so far.
    total = max(1.0, 0.8 * time_limit - 3.0)
    deadline = t0 + total
    remaining = deadline - time.monotonic()
    if d >= 3 and D >= 2 and remaining > 4.0:
        try:
            text = lib.run_c(C_LIFT, [d, D, seed, round(remaining - 1.0, 2), best_n],
                             timeout=remaining + 20.0)
            n, edges = lib.parse_graph_text(text)
            consider(n, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
