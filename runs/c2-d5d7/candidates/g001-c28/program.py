"""Bi-Cayley (group-lift) search, a different construction from the parent's hill-climb.

Each graph is a voltage lift of a d-regular base multigraph with p vertices per side over a
group G = Z_m x| Z_k of order N. Left multiplication by G is an automorphism, so a pair of
vertices is within distance D iff a BFS from one root in each of the 2p orbits reaches
everything within D steps. The C engine hill-climbs the voltages to zero bad pairs, then
grows N one step at a time. Python keeps a valid fallback and validates the C output.
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

#define MAXD 16
#define MAXP 3
#define MAXN 6000
#define MAXV 12000
#define STEPS 4000

typedef struct { int i, j, g; } Dart;
typedef struct { int m, k, r; int rp[MAXN]; } Grp;

static int d, D;
static double t_end;
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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
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

/* Largest order of a bipartite graph with max degree d and diameter D. */
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

/* ---------------------------------------------------------------- groups */

/* Z_m x|_r Z_k; element (a, b) coded as a*k + b; identity is 0. */
static Grp G;

static int gmul(int x, int y) {
    int k = G.k, m = G.m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    int a2 = (int)(((long)a + (long)G.rp[b] * c) % m);
    return a2 * k + (b + e) % k;
}

static int random_group(int N, Grp *Gr) {
    long cnt = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!cnt) return 0;
    Gr->m = bm;
    Gr->k = bk;
    Gr->r = br;
    Gr->rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) Gr->rp[b] = (int)((long)Gr->rp[b - 1] * br % bm);
    return 1;
}

/* ---------------------------------------------------------------- lifts */

static int P_, N_, V, nd;
static Dart dt[MAXD * MAXP];
static int adjv[MAXV][MAXD];
static int degv[MAXV];
static int distv[MAXV], qv[MAXV];

/* A side: i*N + x; B side: P*N + j*N + y. Dart (i,j,g) joins A(i,x) to B(j, x*g). */
static void build(void) {
    for (int v = 0; v < V; v++) degv[v] = 0;
    int B0 = P_ * N_;
    for (int t = 0; t < nd; t++) {
        int i = dt[t].i, j = dt[t].j, g = dt[t].g;
        for (int x = 0; x < N_; x++) {
            int a = i * N_ + x;
            int b = B0 + j * N_ + gmul(x, g);
            adjv[a][degv[a]++] = b;
            adjv[b][degv[b]++] = a;
        }
    }
}

/* Number of ordered (root, vertex) pairs at distance > D, roots = identity of every orbit. */
static long cost(void) {
    long bad = 0;
    for (int rt = 0; rt < 2 * P_; rt++) {
        int s = rt < P_ ? rt * N_ : P_ * N_ + (rt - P_) * N_;
        for (int v = 0; v < V; v++) distv[v] = -1;
        int h = 0, tl = 0;
        distv[s] = 0;
        qv[tl++] = s;
        while (h < tl) {
            int v = qv[h++];
            if (distv[v] >= D) continue;
            for (int q = 0; q < degv[v]; q++) {
                int u = adjv[v][q];
                if (distv[u] < 0) {
                    distv[u] = distv[v] + 1;
                    qv[tl++] = u;
                }
            }
        }
        bad += V - tl;
    }
    return bad;
}

/* Voltage for a new dart on pair (i,j) not used by another dart with the same pair. */
static int fresh(int skip, int i, int j) {
    for (;;) {
        int g = rndint(N_), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void make_base(int p, int M[MAXP][MAXP]) {
    memset(M, 0, sizeof(int) * MAXP * MAXP);
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < p; i++) M[i][perm[i]]++;
    }
}

/* Random lift with p base vertices per side over a random group of order N, then hill-climb. */
static int attempt(int p, int N, double until) {
    if (!random_group(N, &G)) return 0;
    P_ = p;
    N_ = N;
    V = 2 * p * N;
    int M[MAXP][MAXP];
    make_base(p, M);
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh(-1, i, j);
                nd++;
            }
    build();
    long bad = cost();
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh(t, dt[t].i, dt[t].j);
        build();
        long nb = cost();
        long delta = nb - bad;
        if (delta <= 0 || rnd01() < exp(-(double)delta / 0.5)) {
            bad = nb;
        } else {
            dt[t].g = old;
            build();
        }
    }
    return bad == 0;
}

/* ---------------------------------------------------------------- best + output */

static long bestV = 0;
static int bestP = 0, bestN = 0, bestNd = 0;
static Dart bestDt[MAXD * MAXP];
static Grp bestG;

static void store_best(void) {
    bestV = V;
    bestP = P_;
    bestN = N_;
    bestNd = nd;
    memcpy(bestDt, dt, sizeof(Dart) * nd);
    bestG = G;
}

static void output_best(void) {
    if (bestV == 0) {
        printf("2 1\n0 1\n");
        return;
    }
    V = (int)bestV;
    P_ = bestP;
    N_ = bestN;
    nd = bestNd;
    memcpy(dt, bestDt, sizeof(Dart) * nd);
    G = bestG;
    build();
    long m = 0;
    int A = P_ * N_;
    for (int v = 0; v < A; v++) m += degv[v];
    printf("%d %ld\n", V, m);
    for (int v = 0; v < A; v++)
        for (int q = 0; q < degv[v]; q++) printf("%d %d\n", v, adjv[v][q]);
}

/* ---------------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD - 1 || D < 2) {
        printf("2 1\n0 1\n");
        return 0;
    }
    long moore = moore_bound();
    long fails = 0;
    while (now() < t_end && bestV < moore && fails < 200000) {
        int p = 1 + rndint(MAXP);
        long N;
        if (bestV == 0) N = d + rndint(3);
        else N = (bestV + 2L * p) / (2L * p) + rndint(2);
        if (N < d) N = d;
        if (2L * p * N > moore || 2L * p * N > MAXV || N > MAXN) {
            fails++;
            continue;
        }
        if (attempt(p, (int)N, t_end)) {
            store_best();
            fails = 0;
        } else {
            fails++;
        }
    }
    output_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _valid(g, d, D):
    try:
        return lib.is_valid(g[0], g[1], d, D)
    except Exception:
        return False


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = (2, [(0, 1)])          # valid for any d >= 1, D >= 1
    cands = []
    start = known_start(d, D)
    if start is not None:
        cands.append(start)
    if D >= 2:
        cands.append(lib.haar_graph(d, range(d)))   # K_{d,d}
    for g in cands:
        if g[0] > best[0] and _valid(g, d, D):
            best = g
    if best[0] >= lib.moore_bound(d, D):
        return best
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 5.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and _valid((n, edges), d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
