"""Bold change for the weak d11D5 case: the lift search now runs entirely in C.

Construction family: bi-Cayley lifts over semidirect products Z_m x| Z_k2 with K base
vertices per side (K <= 5), voltage darts and layer permutations. Each layer is a
perfect matching between base blocks, so every vertex has degree d and the graph is
bipartite and simple. Simulated annealing minimises unreached (vertex, block) pairs at
distance > D. Vertex-transitivity within each block makes that count an exact diameter
test. A ratcheting order goal and a bandit over K steer the search. Exact projective-plane
and Araujo-Lopez constructions still serve as calibration and as the starting order.

The fallback is K_{d,d}, and every returned graph is checked with lib.is_valid.
"""
import itertools
import math
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

#define MAXN 20000
#define MAXD 32
#define MAXK 6
#define KMAX 5
#define PEN 1000L
#define MAXE (MAXN * MAXD / 2)
#define NK2 21

static const int K2OPTS[NK2] = {1,1,2,2,3,4,4,5,6,8,9,10,12,16,18,20,24,30,36,48,60};

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* ---- semidirect group Z_gm x| Z_gk with r^gk = 1 mod gm; element (a,b) coded a*gk+b ---- */
static int gm = 1, gk = 1;
static long gpw[64];

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk;
    int c = y / gk, e = y % gk;
    long t = ((long)a + gpw[b] * (long)c) % gm;
    return (int)(t * gk + (b + e) % gk);
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    long t = (-(gpw[nb] * (long)a)) % gm;
    if (t < 0) t += gm;
    return (int)(t * gk + nb);
}

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Sample (m, k2, r) with m*k2 about target. Returns 1 on success. */
static int sample_group(long target, long *om, long *ok2, long *orr) {
    for (int att = 0; att < 400; att++) {
        long k2 = K2OPTS[rndint(NK2)];
        long m = (target + k2 - 1) / k2 + rndint(3);
        if (m < 2) m = 2;
        if (k2 == 1) {
            *om = m;
            *ok2 = 1;
            *orr = 1;
            return 1;
        }
        for (int t = 0; t < 300; t++) {
            long c = (t == 0) ? m - 1 : 1 + rndint((int)(m - 1));
            if (gcdl(c, m) == 1 && powmodl(c, k2, m) == 1 % m) {
                *om = m;
                *ok2 = k2;
                *orr = c;
                return 1;
            }
        }
    }
    return 0;
}

/* ---- bi-Cayley lift state ---- */
static int K, G, N;
static int layer[MAXD][MAXK];
static int Sv[MAXD][MAXK], Si[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t RA[MAXN], RB[MAXN], ACC[MAXN];
static int badlist[MAXN];
static int bu[MAXE], bv[MAXE];
static int bestN = 0;
static long bestM = 0;

/* A-block i (vertices i*G+g) joined to B-block j ((K+j)*G+h) by dart voltage s:
 * A_g ~ B_{g*s}. Each B_h gets exactly one neighbour per layer: A_{h*s^-1}. */
static void set_dart(int l, int i) {
    int j = layer[l][i], s = Sv[l][i], si = Si[l][i];
    int ab = i * G, bb = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ab + g] = bb + gmul(g, s);
        nbr[l][bb + g] = ab + gmul(g, si);
    }
}

static void init_state(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[r];
            perm[r] = t;
        }
        for (int i = 0; i < K; i++) layer[l][i] = perm[i];
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            Sv[l][i] = rndint(G);
            Si[l][i] = ginv(Sv[l][i]);
            set_dart(l, i);
        }
}

/* Sum over vertices v of the number of blocks whose representative is farther than D from v.
 * By left-translation symmetry this is zero iff the lift has diameter <= D.
 * Leaves the final bitmask in RA. */
static long reach_cost(void) {
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(long)b * G] |= 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    if (cur != RA) memcpy(RA, cur, sizeof(uint64_t) * (size_t)N);
    long unr = 0;
    int full = 2 * K;
    for (int v = 0; v < N; v++) unr += full - __builtin_popcountll(RA[v]);
    return unr;
}

/* Duplicate darts: same base vertex i, same B block j and same voltage. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (layer[l1][i] == layer[l2][i] && Sv[l1][i] == Sv[l2][i]) c++;
    return c;
}

/* Choose a dart, biased toward a random unreached vertex with probability 0.4. */
static void pick_dart(int *pl, int *pi) {
    if (rnd01() < 0.4) {
        uint64_t full = (1ULL << (2 * K)) - 1;
        int nb = 0;
        for (int v = 0; v < N; v++)
            if (ACC[v] != full) badlist[nb++] = v;
        if (nb > 0) {
            int u = badlist[rndint(nb)];
            int block = u / G;
            int l = rndint(d);
            int i = 0;
            if (block < K) {
                i = block;
            } else {
                int j = block - K;
                i = rndint(K);
                for (int ii = 0; ii < K; ii++)
                    if (layer[l][ii] == j) {
                        i = ii;
                        break;
                    }
            }
            *pl = l;
            *pi = i;
            return;
        }
    }
    *pl = rndint(d);
    *pi = rndint(K);
}

static int run_sa(long iters, long patience, double deadline) {
    init_state();
    long cost = reach_cost() + PEN * dupcount();
    memcpy(ACC, RA, sizeof(uint64_t) * (size_t)N);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long bestc = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        long c2;
        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layer[l][i1];
            layer[l][i1] = layer[l][i2];
            layer[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            c2 = reach_cost() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(ACC, RA, sizeof(uint64_t) * (size_t)N);
            } else {
                tmp = layer[l][i1];
                layer[l][i1] = layer[l][i2];
                layer[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
                continue;
            }
        } else {
            int l, i;
            pick_dart(&l, &i);
            int old = Sv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            Sv[l][i] = nw;
            Si[l][i] = ginv(nw);
            set_dart(l, i);
            c2 = reach_cost() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(ACC, RA, sizeof(uint64_t) * (size_t)N);
            } else {
                Sv[l][i] = old;
                Si[l][i] = ginv(old);
                set_dart(l, i);
                continue;
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = t;
        }
    }
    return cost == 0;
}

static void record(void) {
    long M = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++) {
            bu[M] = u;
            bv[M] = nbr[l][u];
            M++;
        }
    bestN = N;
    bestM = M;
}

static int pick_K(const long *trials, const long *wins) {
    if (rnd01() < 0.2) return 1 + rndint(KMAX);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= KMAX; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) {
            bs = s;
            bk = k;
        }
    }
    return bk;
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
    long start_n = argc > 5 ? atol(argv[5]) : 0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double deadline = t0 + limit;
    long moore = moore_bound();
    double cap = (double)(moore < MAXN ? moore : MAXN);
    double goal = fmax((double)start_n * 1.02, 0.2 * cap);
    if (goal > cap) goal = cap;
    if (goal < 2.0 * d) goal = 2.0 * d;

    long trials[MAXK + 1], wins[MAXK + 1];
    memset(trials, 0, sizeof(trials));
    memset(wins, 0, sizeof(wins));

    while (now() < deadline - 0.2) {
        int Kc = pick_K(trials, wins);
        if (goal > cap) goal = cap;
        long Gt = (long)(goal / (2.0 * Kc)) + rndint(3);
        if (Gt < 2) Gt = 2;
        if (2L * Kc * Gt > MAXN) Gt = MAXN / (2L * Kc);
        long m, k2, r;
        if (!sample_group(Gt, &m, &k2, &r)) {
            goal = fmax((double)bestN * 1.01, goal * 0.99);
            continue;
        }
        long Gn = m * k2;
        long Nn = 2L * Kc * Gn;
        if (Nn > moore || Nn > MAXN) {
            goal = fmax((double)bestN * 1.01, goal * 0.99);
            continue;
        }
        if (Nn <= bestN) {
            goal = (double)bestN * 1.01 + 2.0;
            continue;
        }
        gm = (int)m;
        gk = (int)k2;
        for (int b = 0; b < (int)k2; b++) gpw[b] = powmodl(r, b, m);
        G = (int)Gn;
        K = Kc;
        N = (int)Nn;
        trials[Kc]++;
        double rem = deadline - now();
        double slice = rem > 12.0 ? rem / 4.0 : rem;
        int ok = run_sa(20000, 4000, now() + slice);
        if (ok) {
            wins[Kc]++;
            record();
            goal = (double)N * 1.03;
        } else {
            goal = fmax((double)bestN * 1.01, goal * 0.99);
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", bestN, bestM);
    for (long e = 0; e < bestM; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions used as calibration and as starting orders.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

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

    if D == 2 or d < 2:
        return best

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

    # Main search: the whole bi-Cayley lift search runs in C with most of the budget.
    elapsed = time.monotonic() - t0
    budget = 0.8 * time_limit - 3.0 - elapsed
    if budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                             timeout=budget + 15.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
