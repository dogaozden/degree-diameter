"""Bi-Cayley lift search in C over semidirect groups Z_m x| Z_k2, with an exact cost.

Construction: vertices are blocks A_0..A_{K-1}, B_0..B_{K-1}, each a copy of a group G.
Layer l joins A_i to B_{sig[l][i]} by A_{i,g} ~ B_{j,g*s[l][i]}. Left translation by any
element of G is an automorphism, so the diameter test only needs BFS from the 2K block
identities. A zero cost means every block identity reaches every vertex within D, which
is exact. Duplicate darts are penalised so the output is a simple d-regular bipartite graph.

Safe fallback: exact PG(2,q) / Araujo-Lopez / GQ constructions when they apply, otherwise K_{d,d}.
Every returned graph passes lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Usage: prog d D seed time_limit goal
 * Searches bi-Cayley lifts over Z_m x| Z_k2 with simulated annealing, ratcheting the order goal.
 * Prints the largest valid graph found as "n m" + edges, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXD 32
#define MAXK 8

static int d, D, K, G, M_, K2;
static int pw[MAXD];
static int sig[MAXD][MAXK], sv[MAXD][MAXK], isv[MAXD][MAXK];
static int nbr[MAXN * MAXD];
static int bestnbr[MAXN * MAXD];
static int best_n = 0, best_k = 0, best_g = 0;
static int stampv[MAXN];
static int curstamp = 0;
static int qbuf[MAXN];
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

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a < 0 ? -a : a;
}

/* Group Z_M_ x| Z_K2, element (a,b) coded as a*K2+b, product (a,b)(c,e) = (a + r^b c, b+e). */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M_) * K2 + (b + e) % K2;
}
static inline int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long t = ((long)(M_ - pw[nb]) % M_) * a % M_;
    return (int)t * K2 + nb;
}

/* Sample a group with order about target; sets M_, K2, G, pw. */
static int sample_group(int target) {
    static const int K2s[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2s[rndint(11)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1 && m >= 3 && rnd01() < 0.75) {
            int found = 0;
            for (int t = 0; t < 100; t++) {
                int c = 2 + rndint(m - 2);
                if (gcdl(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        M_ = m;
        K2 = k2;
        G = m * k2;
        pw[0] = 1 % m;
        for (int b = 1; b < K2; b++) pw[b] = (int)(((long)pw[b - 1] * r) % m);
        return G;
    }
    M_ = target < 2 ? 2 : target;
    K2 = 1;
    G = M_;
    pw[0] = 1 % M_;
    return G;
}

/* Rewrite all neighbour entries touched by dart (layer l, A-block i). */
static void set_dart(int l, int i) {
    int j = sig[l][i];
    int s = sv[l][i];
    int is = ginv(s);
    isv[l][i] = is;
    for (int g = 0; g < G; g++)
        nbr[(i * G + g) * MAXD + l] = (K + j) * G + gmul(g, s);
    for (int h = 0; h < G; h++)
        nbr[((K + j) * G + h) * MAXD + l] = i * G + gmul(h, is);
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            sig[l][i] = perm[i];
            sv[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Total unreached (block identity, vertex) pairs over the 2K block identities. */
static long eval_unreached(void) {
    int N = 2 * K * G;
    long tot = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        curstamp++;
        int head = 0, tail = 0, reached = 1;
        qbuf[tail++] = src;
        stampv[src] = curstamp;
        for (int depth = 0; depth < D && head < tail && reached < N; depth++) {
            int end = tail;
            while (head < end) {
                int v = qbuf[head++];
                const int *nv = nbr + v * MAXD;
                for (int l = 0; l < d; l++) {
                    int u = nv[l];
                    if (stampv[u] != curstamp) {
                        stampv[u] = curstamp;
                        qbuf[tail++] = u;
                        reached++;
                    }
                }
            }
        }
        tot += N - reached;
    }
    return tot;
}

/* Number of repeated (block, voltage) darts; repeats would create multi-edges. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (sig[l1][i] == sig[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static long total_cost(void) {
    long N = 2L * K * G;
    return eval_unreached() + 2L * N * dupcount();
}

static long anneal(double deadline, long maxit, long patience) {
    long cost = total_cost();
    long best = cost, last = 0;
    for (long t = 0; t < maxit && cost > 0; t++) {
        if ((t & 15) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double T = 0.3 + 0.01 * (double)cost;
        if (K >= 2 && rndint(10) < 3) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = sig[l][i1];
            sig[l][i1] = sig[l][i2];
            sig[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long nc = total_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = sig[l][i1];
                sig[l][i1] = sig[l][i2];
                sig[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = sv[l][i];
            int ns = rndint(G);
            if (ns == old) continue;
            sv[l][i] = ns;
            set_dart(l, i);
            long nc = total_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                sv[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < best) {
            best = cost;
            last = t;
        }
    }
    return cost;
}

static void save_best(int N) {
    best_n = N;
    best_k = K;
    best_g = G;
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++) bestnbr[v * MAXD + l] = nbr[v * MAXD + l];
}

static void print_best(void) {
    if (best_n == 0) {
        printf("0 0\n");
        return;
    }
    int rows = best_k * best_g;
    long m = (long)rows * d;
    printf("%d %ld\n", best_n, m);
    for (int v = 0; v < rows; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, bestnbr[v * MAXD + l]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit goal\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long goal = atol(argv[5]);
    double t0 = now();
    double t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    double g = (double)goal;
    while (now() < t_end) {
        int want = (int)g;
        if (want < best_n + 2) want = best_n + 2;
        int k = (rndint(10) == 0) ? 1 : 2 + rndint(5);
        int maxG = MAXN / (2 * k);
        int gt = (want + 2 * k - 1) / (2 * k) + rndint(3);
        if (gt > maxG) gt = maxG;
        if (gt < 2) gt = 2;
        K = k;
        sample_group(gt);
        int N = 2 * K * G;
        if (N > MAXN) {
            g *= 0.99;
            continue;
        }
        if (N <= best_n) {
            g = best_n * 1.02 + 2.0;
            continue;
        }
        random_init();
        double rem = t_end - now();
        double slice = rem / 6.0;
        if (slice < 2.0) slice = 2.0;
        if (slice > rem) slice = rem;
        long c = anneal(now() + slice, 200000, 2500);
        if (c == 0) {
            save_best(N);
            g = N * 1.03 + 1.0;
        } else {
            double floor_goal = best_n * 1.01 + 2.0;
            double nxt = g * 0.97;
            g = nxt > floor_goal ? nxt : floor_goal;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept as the first fallback).
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

    total = max(1.0, 0.88 * time_limit - 2.0)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main phase: C bi-Cayley lift search with exact block-identity BFS cost.
    remaining = final - time.monotonic() - 1.0
    if remaining > 2.0 and d >= 2 and D >= 3:
        moore = lib.moore_bound(d, D)
        goal = max(best_n + 2, int(0.2 * moore))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), goal],
                             timeout=remaining + 5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
