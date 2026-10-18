"""Bold variant: voltage lifts of small bipartite base graphs over metacyclic groups.

Parent family: bi-Cayley graphs (one vertex per side in the base graph).
This variant: base graphs with k vertices per side (k = 1, 2, 3), every base
vertex of degree d, and voltages in a metacyclic group G = Z_a x| Z_b with |G| = m.
The lift has 2*k*m vertices and is d-regular and bipartite.

Facts used:
  * Left multiplication by h in G is an automorphism of the lift, so each fiber
    is one orbit. Eccentricity checks need only one BFS per fiber (2k BFS runs).
  * A spanning tree of the base graph can be given identity voltages, so only
    the non-tree darts are random. Parallel darts get distinct voltages, so the
    lift is simple.

The C engine scans m upward. For each m it tries random base matrices, random
groups of order m and random voltages. The first success for m is verified by a
full BFS from every vertex before it is recorded. If nothing is found it prints
K_{d,d}. Python runs two C searches (k = 1 and k = 2, 3) and keeps the largest
graph that passes lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 512
#define MAXV 1024
#define MAXD 16
#define MAXE 9000
#define MAXGRP 512

static int d, D, cap, kmask;
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
static int moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2 * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return (int)(2 * s);
}

/* ---------------------------------------------------------- metacyclic groups */

/* Z_a x| Z_b with r^b = 1 mod a. Element (x1, x2) is coded x1*b + x2. */
typedef struct { int a, b, r; } Grp;
static Grp grp[MAXGRP];
static int ngrp;

static void enum_groups(int m) {
    ngrp = 0;
    for (int a = 1; a <= m; a++) {
        if (m % a) continue;
        int b = m / a;
        if (a == 1) {
            if (ngrp < MAXGRP) {
                grp[ngrp].a = 1; grp[ngrp].b = b; grp[ngrp].r = 0; ngrp++;
            }
            continue;
        }
        for (int r = 1; r < a; r++) {
            if (gcd(r, a) != 1) continue;
            if (powmod(r, b, a) != 1 % a) continue;
            if (ngrp < MAXGRP) {
                grp[ngrp].a = a; grp[ngrp].b = b; grp[ngrp].r = r; ngrp++;
            }
        }
    }
}

static int MT[MAXM * MAXM]; /* multiplication table of the current group */
static int INV[MAXM];

static void build_group(Grp G) {
    int a = G.a, b = G.b, m = a * b;
    static int rp[MAXM];
    rp[0] = 1 % a;
    for (int t = 1; t < b; t++) rp[t] = (int)((long)rp[t - 1] * G.r % a);
    for (int x = 0; x < m; x++) {
        int x1 = x / b, x2 = x % b;
        for (int y = 0; y < m; y++) {
            int y1 = y / b, y2 = y % b;
            int p1 = (int)(((long)x1 + (long)rp[x2] * y1) % a);
            MT[x * m + y] = p1 * b + (x2 + y2) % b;
        }
    }
    for (int x = 0; x < m; x++)
        for (int y = 0; y < m; y++)
            if (MT[x * m + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- lifts */

static int cell[3][3];          /* base multigraph: cell[i][j] darts between U_i and W_j */
static int volt[3][3][MAXD];    /* voltages of those darts */
static int adj[MAXV][MAXD];
static int vis[MAXV], dep[MAXV], qu[MAXV], stamp = 0;

static int bestV = 0, bestEc = 0;
static int bestE[MAXE][2];

/* Random base matrix: k x k nonnegative integers, all row and column sums d. */
static void random_base(int k) {
    int rr[3], cc[3];
    for (int i = 0; i < k; i++) { rr[i] = d; cc[i] = d; }
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) cell[i][j] = 0;
    int left = k * d;
    while (left > 0) {
        int i, j;
        do { i = rndint(k); } while (rr[i] == 0);
        do { j = rndint(k); } while (cc[j] == 0);
        cell[i][j]++;
        rr[i]--;
        cc[j]--;
        left--;
    }
}

/* BFS over the explicit adjacency; 1 iff everything is within D of s. */
static int bfs_full(int s, int V) {
    stamp++;
    int h = 0, t = 0;
    qu[t++] = s;
    vis[s] = stamp;
    dep[s] = 0;
    while (h < t) {
        int v = qu[h++];
        if (dep[v] >= D) continue;
        for (int e = 0; e < d; e++) {
            int u = adj[v][e];
            if (vis[u] != stamp) {
                vis[u] = stamp;
                dep[u] = dep[v] + 1;
                qu[t++] = u;
            }
        }
    }
    return t == V;
}

/* Full verification from every vertex, then store the graph if it beats the best. */
static int verify_and_record(int k, int m) {
    int V = 2 * k * m;
    if (V <= bestV) return 0;
    for (int s = 0; s < V; s++)
        if (!bfs_full(s, V)) return 0;
    int U = k * m, E = 0;
    for (int v = 0; v < U; v++)
        for (int e = 0; e < d; e++) {
            bestE[E][0] = v;
            bestE[E][1] = adj[v][e];
            E++;
        }
    bestV = V;
    bestEc = E;
    return 1;
}

/* One random lift with k base vertices per side over the current group (order m). */
static int tryK(int k, int m) {
    if (m <= d) return 0;
    random_base(k);

    /* Spanning tree of the base support (nodes: U_i = i, W_j = k + j). */
    int seen[6] = {0, 0, 0, 0, 0, 0}, q[6], tree[3][3];
    memset(tree, 0, sizeof tree);
    int h = 0, t = 0;
    q[t++] = 0;
    seen[0] = 1;
    while (h < t) {
        int v = q[h++];
        if (v < k) {
            for (int j = 0; j < k; j++)
                if (cell[v][j] > 0 && !seen[k + j]) {
                    seen[k + j] = 1;
                    tree[v][j] = 1;
                    q[t++] = k + j;
                }
        } else {
            int j = v - k;
            for (int i = 0; i < k; i++)
                if (cell[i][j] > 0 && !seen[i]) {
                    seen[i] = 1;
                    tree[i][j] = 1;
                    q[t++] = i;
                }
        }
    }
    if (t != 2 * k) return 0;

    /* Voltages: tree darts get identity, the rest are random and distinct per pair. */
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) {
            int c = cell[i][j];
            if (c == 0) continue;
            int used[MAXD], nu = 0, start = 0;
            if (tree[i][j]) {
                volt[i][j][0] = 0;
                used[nu++] = 0;
                start = 1;
            }
            for (int s = start; s < c; s++) {
                int g, ok;
                do {
                    g = rndint(m);
                    ok = 1;
                    for (int u = 0; u < nu; u++)
                        if (used[u] == g) { ok = 0; break; }
                } while (!ok);
                used[nu++] = g;
                volt[i][j][s] = g;
            }
        }

    /* Dart lists per fiber. */
    int UJ[3][MAXD], UG[3][MAXD], WI[3][MAXD], WG[3][MAXD];
    int UC[3] = {0, 0, 0}, WC[3] = {0, 0, 0};
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            for (int s = 0; s < cell[i][j]; s++) {
                int g = volt[i][j][s];
                UJ[i][UC[i]] = j;
                UG[i][UC[i]] = g;
                UC[i]++;
                WI[j][WC[j]] = i;
                WG[j][WC[j]] = INV[g];
                WC[j]++;
            }

    /* Explicit adjacency. U(i,x) = i*m + x; W(j,y) = U + j*m + y, with U = k*m. */
    int U = k * m, V = 2 * k * m;
    for (int x = 0; x < U; x++) {
        int i = x / m, xx = x % m;
        for (int e = 0; e < d; e++)
            adj[x][e] = U + UJ[i][e] * m + MT[xx * m + UG[i][e]];
    }
    for (int y = 0; y < U; y++) {
        int j = y / m, yy = y % m;
        for (int e = 0; e < d; e++)
            adj[U + y][e] = WI[j][e] * m + MT[yy * m + WG[j][e]];
    }

    /* Fiber transitivity: one source per fiber suffices for the quick test. */
    for (int i = 0; i < k; i++)
        if (!bfs_full(i * m, V)) return 0;
    for (int j = 0; j < k; j++)
        if (!bfs_full(U + j * m, V)) return 0;

    verify_and_record(k, m);
    return 1;
}

/* Tries for a fixed order m until success or until the deadline. */
static int search_m(int m, double until) {
    int ks[3], nk = 0;
    for (int k = 1; k <= 3; k++)
        if (((kmask >> k) & 1) && 2 * k * m <= cap) ks[nk++] = k;
    if (nk == 0) return 0;
    enum_groups(m);
    if (ngrp == 0) return 0;
    while (now() < until) {
        Grp G = grp[rndint(ngrp)];
        build_group(G);
        for (int t = 0; t < 300 && now() < until; t++) {
            int k = ks[rndint(nk)];
            if (tryK(k, m)) return 1;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: %s d D seed budget mlo mmax kmask\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int mlo = atoi(argv[5]);
    int mmax = atoi(argv[6]);
    kmask = atoi(argv[7]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    long mb = moore_bound();
    cap = mb < MAXV ? (int)mb : MAXV;
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    if (mlo < d + 1) mlo = d + 1;

    if (d >= 2 && D >= 2) {
        for (int m = mlo; m <= mmax && now() < t_end; m++) {
            double until = now() + (t_end - now()) / (double)(mmax - m + 1);
            if (until > t_end) until = t_end;
            search_m(m, until);
        }
    }

    if (bestV > 0) {
        printf("%d %d\n", bestV, bestEc);
        for (int e = 0; e < bestEc; e++)
            printf("%d %d\n", bestE[e][0], bestE[e][1]);
    } else {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++)
                printf("%d %d\n", a, d + b);
    }
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    def remaining():
        return 0.8 * time_limit - (time.monotonic() - t0) - 1.5

    def run(budget, mlo, mmax, mask, sd):
        nonlocal best
        if budget < 1.0 or mlo > mmax:
            return
        try:
            text = lib.run_c(C_SOURCE, [d, D, sd, round(budget, 2), mlo, mmax, mask],
                             stdin_graph=None, timeout=budget + 15)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback

    # Run A: one base vertex per side (bi-Cayley), scanning near the record scale.
    half = moore // 2
    mlo1 = max(d + 1, int(0.45 * moore) // 2)
    mmax1 = min(half, 511, mlo1 + 40)
    run(0.5 * remaining(), mlo1, mmax1, 1 << 1, seed)

    # Run B: lifts with 2 or 3 base vertices per side.
    mlo2 = max(d + 1, moore // 12)
    mmax2 = min(moore // 4, 255)
    run(remaining(), mlo2, mmax2, (1 << 2) | (1 << 3), seed + 7919)

    return best
