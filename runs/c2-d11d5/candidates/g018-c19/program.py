"""Bi-Cayley voltage-lift search with an exact block-invariant diameter test, run in C.

New idea: left multiplication by the group G is an automorphism of a bi-Cayley lift
A_{i,g} ~ B_{p,gs}. So all vertices of one block share an eccentricity, and the diameter
is at most D iff a BFS from each of the 2K block identities reaches every vertex within D
steps. The annealer therefore pays 2K BFS runs per move, not a full all-pairs computation.

Python builds the exact fallbacks (K_{d,d}, PG(2,q) for D >= 3), runs the C search, and
checks everything with lib.is_valid before returning.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift search with a block-invariant diameter test.
 * usage:  prog d D seed time_limit
 * stdout: "n m" + edges of the best valid graph found, or "0 0".
 *
 * Graph: K blocks A_i and K blocks B_p, each a copy of G = Z_m x| Z_k2 (element a*k2+b).
 * Layer l joins A_i to B_{lay[l][i]} through voltage sv[l][i]: A_{i,g} ~ B_{p,g*s}.
 * Each layer is a perfect matching between the block pairs, so the graph is d-regular.
 * Left multiplication by G is an automorphism, so the diameter is the maximum over the
 * 2K block identities of their eccentricity.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 24
#define MAXK 6
#define MAXN 16384
#define ITERS 5000
#define PATIENCE 1200

static int d, D;
static uint64_t rs = 88172645463325252ULL;

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

/* ---- group Z_m x| Z_k2, (a,b)(c,e) = (a + r^b c, b + e), element a*k2 + b ---- */
static int gm, gk2, gG;
static long long pw[64];

static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    gG = m * k2;
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = pw[t - 1] * r % m;
}
static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long long aa = (a + pw[b] * c) % gm;
    return (int)(aa * gk2 + (b + e) % gk2);
}
static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long long aa = (gm - pw[nb] * a % gm) % gm;
    return (int)(aa * gk2 + nb);
}
static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

/* ---- lift state ---- */
static int K, NN;
static int lay[MAXD][MAXK], sv[MAXD][MAXK];
static int nb[MAXD][MAXN];
static int dist[MAXN], qu[MAXN];

static void fill_layer(int l) {
    for (int i = 0; i < K; i++) {
        int p = lay[l][i], s = sv[l][i], si = ginv(s);
        for (int g = 0; g < gG; g++) {
            int h = gmul(g, s);
            int A = i * gG + g;
            int B = (K + p) * gG + h;
            nb[l][A] = B;
            nb[l][B] = i * gG + gmul(h, si);
        }
    }
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) sv[l][i] = rndint(gG);
        fill_layer(l);
    }
}

/* Vertices at distance > D from src (unreached counts as bad). */
static long bfs_unreached(int src) {
    for (int v = 0; v < NN; v++) dist[v] = -1;
    int head = 0, tail = 0, reached = 1;
    dist[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        if (dist[v] >= D) continue;
        for (int l = 0; l < d; l++) {
            int u = nb[l][v];
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                qu[tail++] = u;
                reached++;
            }
        }
    }
    return NN - reached;
}

/* Parallel edges arise only from equal (block pair, voltage) keys. */
static long dupcount(void) {
    long c = 0;
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            for (int i = 0; i < K; i++)
                if (lay[l1][i] == lay[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    long c = 0;
    for (int i = 0; i < 2 * K; i++) c += bfs_unreached(i * gG);
    return c + 1000L * dupcount();
}

static int anneal(double deadline) {
    random_init();
    long cost = full_cost();
    long c0 = cost > 0 ? cost : 1;
    long best = cost;
    int last = 0;
    for (int t = 0; t < ITERS && cost > 0; t++) {
        if ((t & 31) == 0 && now() > deadline) break;
        if (t - last > PATIENCE) break;
        double temp = 0.5 + 0.02 * (double)c0 * (1.0 - (double)t / ITERS);
        int l = rndint(d);
        int olay[MAXK], osv[MAXK];
        memcpy(olay, lay[l], sizeof(int) * K);
        memcpy(osv, sv[l], sizeof(int) * K);
        if (K >= 2 && rnd01() < 0.3) {
            int i = rndint(K), j = rndint(K);
            if (i == j) continue;
            int tmp = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = tmp;
        } else {
            int i = rndint(K), ns = rndint(gG);
            if (ns == sv[l][i]) continue;
            sv[l][i] = ns;
        }
        fill_layer(l);
        long nc = full_cost();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
            cost = nc;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            memcpy(lay[l], olay, sizeof(int) * K);
            memcpy(sv[l], osv, sizeof(int) * K);
            fill_layer(l);
        }
    }
    return cost == 0;
}

static int sample_group(int target, int *m, int *k2, int *r) {
    static const int ks[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12};
    for (int tries = 0; tries < 200; tries++) {
        int k = ks[rndint(12)];
        int mm = (target + k - 1) / k;
        if (mm < 2) mm = 2;
        int rr = 1;
        if (k > 1 && mm > 2) {
            int ok = 0;
            for (int t = 0; t < 80; t++) {
                int c = 2 + rndint(mm - 2);
                if (gcd_i(c, mm) == 1 && powmod(c, k, mm) == 1 % mm) {
                    rr = c;
                    ok = 1;
                    break;
                }
            }
            if (!ok) continue;
        }
        *m = mm;
        *k2 = k;
        *r = rr;
        return 1;
    }
    return 0;
}

static void print_best(int bK, int bm, int bk2, int br, const int blay[MAXD][MAXK],
                       const int bsv[MAXD][MAXK]) {
    K = bK;
    set_group(bm, bk2, br);
    NN = 2 * K * gG;
    memcpy(lay, blay, sizeof(lay));
    memcpy(sv, bsv, sizeof(sv));
    for (int l = 0; l < d; l++) fill_layer(l);
    long m = (long)K * gG * d;
    printf("%d %ld\n", NN, m);
    for (int u = 0; u < K * gG; u++)
        for (int l = 0; l < d; l++) printf("%d %d\n", u, nb[l][u]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double deadline = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    /* Moore bound for bipartite graphs: 2 * sum_{i<D} (d-1)^i (2D when d = 2). */
    long mb;
    if (d == 2) {
        mb = 2L * D;
    } else {
        long s = 0, p = 1;
        for (int i = 0; i < D; i++) {
            s += p;
            p *= (d - 1);
            if (s > MAXN) break;
        }
        mb = 2 * s;
    }
    if (mb > MAXN) mb = MAXN;

    long bestN = 2L * d;
    int have = 0;
    int bK = 0, bm = 0, bk2 = 0, br = 0;
    static int blay[MAXD][MAXK], bsv[MAXD][MAXK];
    long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    long goal = bestN + 2;

    while (now() < deadline) {
        if (goal > mb) goal = mb;
        if (goal < bestN + 2) goal = bestN + 2;

        int Kc;
        if (rnd01() < 0.2) {
            Kc = 1 + rndint(MAXK - 1);
        } else {
            double bv = -1.0;
            Kc = 1;
            for (int k = 1; k < MAXK; k++) {
                double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
                if (v > bv) {
                    bv = v;
                    Kc = k;
                }
            }
        }

        long target = goal / (2L * Kc) + rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group((int)target, &m, &k2, &r)) {
            goal = goal * 99 / 100;
            continue;
        }
        set_group(m, k2, r);
        long N = 2L * Kc * gG;
        if (N > mb || N <= bestN) {
            goal = goal * 99 / 100;
            continue;
        }

        K = Kc;
        NN = (int)N;
        trials[Kc]++;
        if (anneal(deadline)) {
            wins[Kc]++;
            bestN = N;
            have = 1;
            bK = K;
            bm = m;
            bk2 = k2;
            br = r;
            memcpy(blay, lay, sizeof(lay));
            memcpy(bsv, sv, sizeof(sv));
            goal = N * 104 / 100 + 1;
        } else {
            goal = goal * 99 / 100;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    print_best(bK, bm, bk2, br, blay, bsv);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions used as fallbacks.
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

    # K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
                best = pg
                best_n = pg[0]
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass

    # Bi-Cayley lift search in C, using the remaining budget (C stops at ~0.95 of it).
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 0.5
    if budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             timeout=0.93 * time_limit)
            n, edges = lib.parse_graph_text(text)
            consider(n, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
