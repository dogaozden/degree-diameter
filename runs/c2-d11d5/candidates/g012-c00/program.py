"""Bi-Cayley voltage-lift annealing in C, with a ratcheted group-order goal.

The C engine searches over semidirect products Z_m x| Z_k2 with k blocks per side and d layers.
Each layer is a perfect matching between A-blocks and B-blocks, with a group voltage per dart.
Left multiplication by the group is an automorphism, so reachability only needs BFS from the
2k block representatives. Every returned graph is checked with lib.is_valid, and K_{d,d}
(or a known construction) is the fallback.
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

/* Usage: prog d D seed time_limit [min_n]
 * stdout: "n m" + edges of the best valid lift with n > min_n, or "0 0".
 */

#define MAXN 65536
#define MAXD 32
#define MAXK 8
#define KMAX 5
#define PATIENCE 2000

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

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
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

/* Group Z_M x| Z_K2 with r^K2 = 1 mod M; element (a,b) is coded a*K2+b. */
static int K, G, M, K2, R;
static long long PW[64];

/* Lift state: layer l, A-block i -> B-block P[l][i] with voltage S[l][i]. */
static int P[MAXD][MAXK], S[MAXD][MAXK], IS[MAXD][MAXK];
static int NB[MAXD][MAXN];
static int NV;

static void set_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    R = r;
    G = m * k2;
    for (int b = 0; b < K2; b++) PW[b] = pmod(R, b, M);
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = (a + PW[b] * c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long na = (M - (PW[nb] * a) % M) % M;
    return (int)(na * K2 + nb);
}

/* Rewrite neighbours of A-block i and of its partner B-block in layer l. */
static void refresh_dart(int l, int i) {
    int j = P[l][i], s = S[l][i], is = IS[l][i];
    int Ao = i * G, Bo = (K + j) * G;
    for (int g = 0; g < G; g++) {
        NB[l][Ao + g] = Bo + gmul(g, s);
        NB[l][Bo + g] = Ao + gmul(g, is);
    }
}

static void init_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            S[l][i] = rndint(G);
            IS[l][i] = ginv(S[l][i]);
            refresh_dart(l, i);
        }
    }
}

static int vis[MAXN];
static int qu[MAXN];
static int stamp_ = 0;

/* Number of vertices within distance D of src. */
static int reach_count(int src) {
    int head = 0, tail = 0;
    stamp_++;
    qu[tail++] = src;
    vis[src] = stamp_;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qu[head];
            for (int l = 0; l < d; l++) {
                int u = NB[l][v];
                if (vis[u] != stamp_) {
                    vis[u] = stamp_;
                    qu[tail++] = u;
                }
            }
        }
    }
    return tail;
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (P[l][i] == P[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Cost is 0 iff the lift is valid. Vertex-transitivity lets us test only the 2K representatives. */
static long eval_cost(void) {
    long unreached = 0;
    for (int b = 0; b < 2 * K; b++) {
        long c = reach_count(b * G);
        unreached += NV - c;
    }
    return unreached + (long)NV * dup_count();
}

static int anneal(double deadline) {
    long cost = eval_cost();
    long best = cost, last_imp = 0;
    double T0 = 1.0 + 0.05 * (double)cost;
    for (long t = 0;; t++) {
        if (cost == 0) return 1;
        if ((t & 15) == 0 && now() > deadline) return 0;
        if (t - last_imp > PATIENCE) return 0;
        double T = T0 * pow(0.999, (double)t) + 0.05;
        if (K >= 2 && rnd01() < 0.3) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int tmp = P[l][i1];
            P[l][i1] = P[l][i2];
            P[l][i2] = tmp;
            refresh_dart(l, i1);
            refresh_dart(l, i2);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last_imp = t;
                }
            } else {
                tmp = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = tmp;
                refresh_dart(l, i1);
                refresh_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i], nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            IS[l][i] = ginv(nw);
            refresh_dart(l, i);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last_imp = t;
                }
            } else {
                S[l][i] = old;
                IS[l][i] = ginv(old);
                refresh_dart(l, i);
            }
        }
    }
}

static const int K2CH[16] = {1, 1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12, 16};

/* Sets the group for a target order >= target. */
static void sample_group(long target) {
    for (int tries = 0; tries < 100; tries++) {
        int k2 = K2CH[rndint(16)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (k2 == 1) {
            set_group((int)m, 1, 1);
            return;
        }
        int cand = -1, found = 0;
        if (rnd01() < 0.3) {
            cand = (int)(m - 1);
            if (pmod(cand, k2, m) == 1 % m && gcdll(cand, m) == 1) found = 1;
        }
        for (int t = 0; !found && t < 60; t++) {
            cand = 1 + rndint((int)(m - 1));
            if (gcdll(cand, m) == 1 && pmod(cand, k2, m) == 1 % m) found = 1;
        }
        if (found) {
            set_group((int)m, k2, cand);
            return;
        }
    }
    long m = target < 2 ? 2 : target;
    set_group((int)m, 1, 1);
}

static int bestN = 0, bestK = 0, bestM = 0, bestK2 = 0, bestR = 0;
static int bestP[MAXD][MAXK], bestS[MAXD][MAXK];

static void save_best(void) {
    bestN = NV;
    bestK = K;
    bestM = M;
    bestK2 = K2;
    bestR = R;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            bestP[l][i] = P[l][i];
            bestS[l][i] = S[l][i];
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int base_n = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    bestN = base_n;
    double goal = bestN * 1.03 + 4.0;
    long trials[KMAX + 1] = {0}, wins[KMAX + 1] = {0};

    while (now() < end) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(KMAX);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= KMAX; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    k = c;
                }
            }
        }
        K = k;
        long target = (long)(goal / (2.0 * K)) + rndint(3);
        if (target < 2) target = 2;
        sample_group(target);
        NV = 2 * K * G;
        if (NV > MAXN || NV <= bestN) {
            goal = fmax(goal, bestN * 1.01 + 2.0);
            continue;
        }
        trials[K]++;
        init_state();
        double remaining = end - now();
        double slice_end = now() + fmax(1.5, 0.25 * remaining);
        if (slice_end > end) slice_end = end;
        if (anneal(slice_end)) {
            wins[K]++;
            save_best();
            goal = bestN * 1.03 + 4.0;
        } else {
            goal = fmax(bestN * 1.01 + 2.0, goal * 0.99);
        }
    }

    if (bestK == 0 || bestN <= base_n) {
        printf("0 0\n");
        return 0;
    }
    K = bestK;
    set_group(bestM, bestK2, bestR);
    printf("%d %ld\n", 2 * K * G, (long)d * K * G);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++)
            for (int g = 0; g < G; g++) {
                int u = i * G + g;
                int v = (K + bestP[l][i]) * G + gmul(g, bestS[l][i]);
                printf("%d %d\n", u, v);
            }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

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
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 3 and lib.is_prime_power(d - 1):
        return best
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C voltage-lift annealing over semidirect products, seeded with the best
    # graph so far as the baseline order to beat.
    budget = 0.8 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget >= 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                             timeout=budget + 15.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
