"""Bi-Cayley lift search with fast BFS evaluation, plus the old constructions as fallback.

Main idea for the target cases (any d, D): a bipartite graph with 2pN vertices, built as a
voltage lift of a d-regular base multigraph (p vertices per side) over a metacyclic group
G = Z_m x| Z_k of order N. Left multiplication is an automorphism, so each orbit is vertex
transitive, and the diameter is exact after 2p BFS runs from the identity of each orbit.
Simulated annealing on the voltages minimises the number of far pairs seen from those roots.
This replaces the full bitset diameter check in the inner loop, which makes each step much
cheaper. Every improvement is confirmed by a full all-pairs BFS before it is kept.

Python keeps a validated fallback (K_{d,d}, or the known construction when one exists)
and only accepts C output that passes lib.is_valid.
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

#define MAXV 16384
#define MAXG 8192
#define MAXD 16
#define MAXP 3
#define MAXDART (MAXD * MAXP)

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b; identity is index 0. */
typedef struct {
    int m, k, r, N;
    int rp[MAXG]; /* rp[b] = r^b mod m */
} Grp;

static Grp G;

static int gmul(int x, int y) {
    int a = x / G.k, b = x % G.k, c = y / G.k, e = y % G.k;
    return (int)((a + (long)G.rp[b] * c) % G.m) * G.k + (b + e) % G.k;
}

/* Uniformly random (m, r, k) with m*k = N, gcd(r,m) = 1, r^k = 1 mod m. */
static void random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 1; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    G.m = bm;
    G.k = bk;
    G.r = br;
    G.N = N;
    G.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G.rp[b] = (int)((long)G.rp[b - 1] * br % bm);
}

/* ------------------------------------------------------------ lift state */

/* Darts: base A-vertex dI -> base B-vertex dJ with voltage dG. */
static int P_, N_, V_;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART], ND;
static int nbr[MAXV][MAXD];
static int dg[MAXV];

/* A(i,x) = i*N + x, B(j,y) = P*N + j*N + y; dart (i,j,g) joins A(i,x) to B(j, x*g). */
static void build_graph(void) {
    int p = P_, N = N_;
    V_ = 2 * p * N;
    for (int v = 0; v < V_; v++) dg[v] = 0;
    for (int t = 0; t < ND; t++) {
        int i = dI[t], j = dJ[t], g = dG[t];
        for (int x = 0; x < N; x++) {
            int a = i * N + x;
            int b = p * N + j * N + gmul(x, g);
            nbr[a][dg[a]++] = b;
            nbr[b][dg[b]++] = a;
        }
    }
}

/* Random d-regular bipartite base multigraph on p+p vertices (sum of d permutations),
 * connected. Sets ND and dI, dJ. */
static void make_base(int p) {
    for (;;) {
        int M[MAXP][MAXP];
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP], st[2 * MAXP], top = 0, ns = 1;
        memset(seen, 0, sizeof seen);
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns != 2 * p) continue;
        ND = 0;
        for (int i = 0; i < p; i++)
            for (int j = 0; j < p; j++)
                for (int c = 0; c < M[i][j]; c++) { dI[ND] = i; dJ[ND] = j; ND++; }
        return;
    }
}

/* A voltage not equal to any of darts [0, lim) except skip, among the same (i,j) pair. */
static int fresh_g(int skip, int lim, int i, int j) {
    for (;;) {
        int g = rndint(N_), clash = 0;
        for (int t = 0; t < lim; t++)
            if (t != skip && dI[t] == i && dJ[t] == j && dG[t] == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void init_state(int p, int N) {
    P_ = p;
    N_ = N;
    make_base(p);
    for (int t = 0; t < ND; t++) dG[t] = fresh_g(-1, t, dI[t], dJ[t]);
}

/* ------------------------------------------------------------ evaluation */

static int dist_[MAXV], que_[MAXV], vis_[MAXV];
static int vst = 0;

/* Number of vertices not reached within D steps from root. */
static long bfs_bad(int root) {
    vst++;
    int head = 0, tail = 0;
    que_[tail++] = root;
    vis_[root] = vst;
    dist_[root] = 0;
    while (head < tail) {
        int v = que_[head++];
        if (dist_[v] >= D) continue;
        for (int i = 0; i < dg[v]; i++) {
            int u = nbr[v][i];
            if (vis_[u] != vst) {
                vis_[u] = vst;
                dist_[u] = dist_[v] + 1;
                que_[tail++] = u;
            }
        }
    }
    return (long)V_ - tail;
}

/* Vertex-transitivity on each side: the 2P orbit representatives suffice. */
static long cost_all(void) {
    long c = 0;
    for (int i = 0; i < P_; i++) c += bfs_bad(i * N_);
    for (int j = 0; j < P_; j++) c += bfs_bad(P_ * N_ + j * N_);
    return c;
}

/* Exact check from every vertex. */
static int full_check(void) {
    int V = V_, half = P_ * N_;
    for (int v = 0; v < V; v++) {
        if (dg[v] != d) return 0;
        for (int i = 0; i < dg[v]; i++) {
            int u = nbr[v][i];
            if (u < 0 || u >= V || u == v) return 0;
            if ((u < half) == (v < half)) return 0;
            for (int j = 0; j < i; j++)
                if (nbr[v][j] == u) return 0;
        }
    }
    for (int v = 0; v < V; v++)
        if (bfs_bad(v) != 0) return 0;
    return 1;
}

/* ------------------------------------------------------------ best store */

static Grp bestG;
static int bestP, bestN, bestND;
static int bestdI[MAXDART], bestdJ[MAXDART], bestdG[MAXDART];
static int best_V = 0, have_best = 0;

static void save_best(void) {
    bestG = G;
    bestP = P_;
    bestN = N_;
    bestND = ND;
    memcpy(bestdI, dI, sizeof dI);
    memcpy(bestdJ, dJ, sizeof dJ);
    memcpy(bestdG, dG, sizeof dG);
    best_V = V_;
    have_best = 1;
}

static void print_complete(void) {
    int n = 2 * d;
    printf("%d %ld\n", n, (long)d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            printf("%d %d\n", a, d + b);
}

static void print_k11(void) {
    printf("2 1\n0 1\n");
}

static void print_best(void) {
    if (!have_best) { print_complete(); return; }
    G = bestG;
    P_ = bestP;
    N_ = bestN;
    ND = bestND;
    memcpy(dI, bestdI, sizeof dI);
    memcpy(dJ, bestdJ, sizeof dJ);
    memcpy(dG, bestdG, sizeof dG);
    build_graph();
    if (!full_check()) { print_complete(); return; }
    long m = 0;
    for (int v = 0; v < V_; v++)
        for (int i = 0; i < dg[v]; i++)
            if (v < nbr[v][i]) m++;
    printf("%d %ld\n", V_, m);
    for (int v = 0; v < V_; v++)
        for (int i = 0; i < dg[v]; i++)
            if (v < nbr[v][i]) printf("%d %d\n", v, nbr[v][i]);
}

/* ------------------------------------------------------------ search */

static void search(void) {
    long moore = moore_bound();
    long lim = moore < MAXV ? moore : MAXV;
    const int STEPS = 8000;

    while (now() < t_end) {
        int p = rndint(10);
        p = p < 3 ? 1 : p < 7 ? 2 : 3;
        long base_V = have_best ? best_V : 2L * d;
        long N = base_V / (2 * p) + 1 + rndint(3);
        while (2L * p * N > lim && p > 1) {
            p--;
            N = base_V / (2 * p) + 1 + rndint(3);
        }
        if (2L * p * N > lim) {
            N = lim / (2 * p);
            if (N <= base_V / (2 * p)) break; /* nothing larger fits */
        }
        if (N < d) N = d;
        if (N > MAXG) N = MAXG;

        random_group((int)N);
        init_state(p, (int)N);
        build_graph();
        long c = cost_all();

        for (int s = 0; s < STEPS && c > 0; s++) {
            if ((s & 63) == 0 && now() > t_end) break;
            double T = 1.5 * (1.0 - (double)s / STEPS) + 0.08;
            int t = rndint(ND);
            int old = dG[t];
            dG[t] = fresh_g(t, ND, dI[t], dJ[t]);
            build_graph();
            long nc = cost_all();
            if (nc <= c || rnd01() < exp((double)(c - nc) / T)) c = nc;
            else dG[t] = old;
        }
        if (c == 0) {
            build_graph();
            if (V_ > best_V && full_check()) save_best();
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_k11(); return 0; }
    search();
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _ok(g, d, D):
    try:
        return g is not None and lib.is_valid(g[0], g[1], d, D)
    except Exception:
        return False


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    # Safe fallback: K_{d,d} for D >= 2, otherwise a single edge (valid for d >= 1, D >= 1).
    best = (2, [(0, 1)])
    if D >= 2 and d >= 1:
        kdd = lib.haar_graph(d, range(d))
        if _ok(kdd, d, D):
            best = kdd
    if not _ok(best, d, D):
        best = (1, [])

    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and _ok(start, d, D) and start[0] > best[0]:
        best = start

    moore = lib.moore_bound(d, D)
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= moore or D < 2 or d < 1 or d > 16 or budget < 0.5:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 3)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and _ok(out, d, D):
            best = out
    except Exception:
        pass
    return best
