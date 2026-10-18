"""Bi-Cayley voltage-lift search with a C annealer.

New in this version:
  * The lift search runs entirely in C. Each layer is a permutation of the k base blocks
    plus one group voltage per dart, so every vertex gets degree d exactly.
  * Exact diameter cost using left-translation symmetry: the lift is invariant under
    left multiplication by the group, so it suffices to BFS from one identity vertex per
    block (2k BFS runs). The cost is the number of unreached pairs, which is zero iff the
    diameter is at most D. The parent's representative-only check was incomplete.
  * Each group sample is an arbitrary semidirect product Z_m x| Z_k2 (or abelian, r = 1).

Every returned graph is checked with lib.is_valid. K_{d,d} is the fallback.
"""
import itertools
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

#define MAXK 4
#define MAXD 32
#define MAXK2 64
#define MAXG 16000
#define MAXN (2 * MAXK * MAXG)
#define ITERS 6000
#define PATIENCE 2000

static const int K2_CHOICES[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int d, D, K, G, M, K2, R, N;
static int P[MAXD][MAXK];      /* layer l: A-block i goes to B-block P[l][i] */
static int S[MAXD][MAXK];      /* voltage of dart (l, i) */
static int powr[MAXK2];
static int nbr[MAXN * MAXD];   /* nbr[v * MAXD + l] */
static unsigned int vis[MAXN];
static unsigned int stamp_ = 0;
static int dep[MAXN];
static int que[MAXN];
static long PEN;
static uint64_t rs = 88172645463325252ULL;

static int bK, bG, bM, bK2, bR;
static int bP[MAXD][MAXK], bS[MAXD][MAXK];

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Multiplication in Z_M x| Z_K2: (a,b)(c,e) = (a + r^b c, b + e). Element index = a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)powr[b] * c) % M;
    int bb = (b + e) % K2;
    return (int)t * K2 + bb;
}

static void set_powers(void) {
    powr[0] = 1 % M;
    for (int b = 1; b < K2; b++) powr[b] = (int)((long long)powr[b - 1] * R % M);
}

/* Write the neighbours of layer l for A-block i (and their B-side partners). */
static void write_dart(int l, int i) {
    int j = P[l][i], s = S[l][i];
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        int a = i * G + g;
        int b = (K + j) * G + h;
        nbr[(size_t)a * MAXD + l] = b;
        nbr[(size_t)b * MAXD + l] = a;
    }
}

static void write_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) write_dart(l, i);
}

/* Number of pairs of layers that repeat the same (block, voltage) dart. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

/* BFS from src; returns the number of vertices not within distance D. */
static long bfs_bad(int src) {
    int head = 0, tail = 0, cnt = 0;
    stamp_++;
    if (stamp_ == 0) {
        memset(vis, 0, sizeof(vis));
        stamp_ = 1;
    }
    que[tail++] = src;
    vis[src] = stamp_;
    dep[src] = 0;
    while (head < tail) {
        int v = que[head++];
        cnt++;
        if (dep[v] >= D) continue;
        const int *row = &nbr[(size_t)v * MAXD];
        for (int l = 0; l < d; l++) {
            int u = row[l];
            if (vis[u] != stamp_) {
                vis[u] = stamp_;
                dep[u] = dep[v] + 1;
                que[tail++] = u;
            }
        }
    }
    return (long)(N - cnt);
}

/* Zero iff the lift is simple, degree d, and has diameter <= D.
 * Left-translation is an automorphism, so one source per block suffices. */
static long cost_eval(void) {
    long total = 0;
    for (int b = 0; b < 2 * K; b++) total += bfs_bad(b * G);
    return total + PEN * dup_count();
}

static void rand_perm(int *a, int n) {
    for (int i = 0; i < n; i++) a[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int anneal(int iters, int patience, double deadline) {
    int tmp[MAXK];
    for (int l = 0; l < d; l++) {
        rand_perm(tmp, K);
        for (int i = 0; i < K; i++) {
            P[l][i] = tmp[i];
            S[l][i] = rndint(G);
        }
    }
    write_all();
    PEN = 2L * N + 10;
    long cur = cost_eval();
    double c0 = (double)(cur > 1 ? cur : 1);
    int last = 0;
    for (int t = 0; t < iters && cur > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double T = 0.05 * c0 * (1.0 - (double)t / iters) + 0.3;
        if (K >= 2 && rnd01() < 0.3) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int p1 = P[l][i1], p2 = P[l][i2];
            P[l][i1] = p2;
            P[l][i2] = p1;
            write_dart(l, i1);
            write_dart(l, i2);
            long c2 = cost_eval();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                if (c2 < cur) last = t;
                cur = c2;
            } else {
                P[l][i1] = p1;
                P[l][i2] = p2;
                write_dart(l, i1);
                write_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            write_dart(l, i);
            long c2 = cost_eval();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                if (c2 < cur) last = t;
                cur = c2;
            } else {
                S[l][i] = old;
                write_dart(l, i);
            }
        }
    }
    return cur == 0;
}

static int sample_group(long target) {
    K2 = K2_CHOICES[rndint(20)];
    long m = (target + K2 - 1) / K2;
    if (m < 2) m = 2;
    if (m * K2 > MAXG) return 0;
    M = (int)m;
    R = 1;
    if (K2 > 1 && M > 2 && rnd01() < 0.7) {
        for (int tries = 0; tries < 80; tries++) {
            int c = 2 + rndint(M - 2);
            if (gcd_i(c, M) == 1 && powmod(c, K2, M) == 1 % M) {
                R = c;
                break;
            }
        }
    }
    G = M * K2;
    set_powers();
    return 1;
}

static void print_best(void) {
    K = bK;
    G = bG;
    M = bM;
    K2 = bK2;
    R = bR;
    N = 2 * K * G;
    set_powers();
    memcpy(P, bP, sizeof(P));
    memcpy(S, bS, sizeof(S));
    write_all();
    PEN = 2L * N + 10;
    if (cost_eval() != 0) {
        printf("0 0\n");
        return;
    }
    long m = (long)K * G * d;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++)
            for (int g = 0; g < G; g++) {
                int h = gmul(g, S[l][i]);
                printf("%d %d\n", i * G + g, (K + P[l][i]) * G + h);
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
    long goal = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    double deadline = t0 + limit * 0.95 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    if (goal <= 0) goal = 2L * d;

    long bestN = 0;
    int trials[MAXK + 1] = {0};
    int wins[MAXK + 1] = {0};

    while (now() < deadline) {
        int k = 1;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        long target = goal / (2L * k) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target)) {
            goal = goal * 99 / 100;
            if (goal < 2) goal = 2;
            continue;
        }
        K = k;
        N = 2 * K * G;
        if (N > MAXN) continue;
        trials[k]++;
        int ok = anneal(ITERS, PATIENCE, deadline);
        if (ok) {
            wins[k]++;
            if (N > bestN) {
                bestN = N;
                bK = K;
                bG = G;
                bM = M;
                bK2 = K2;
                bR = R;
                memcpy(bP, P, sizeof(P));
                memcpy(bS, S, sizeof(S));
            }
            goal = (long)(N * 1.04) + 1;
        } else {
            long lo = (long)(bestN * 1.01) + 1;
            goal = goal * 99 / 100;
            if (goal < lo) goal = lo;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    print_best();
    return 0;
}
'''


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # C lift search, starting its goal just above the best exact graph found.
    if d >= 2 and D >= 3 and not (D == 3 and best_n > 2 * d):
        total = max(1.0, 0.85 * time_limit - 2.0)
        budget = max(1.0, total - 1.0)
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
