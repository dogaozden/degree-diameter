"""Exhaustive bi-Cayley search over metacyclic and direct-product groups.

Construction: for a group G of order n and a connection set S of size d containing the identity,
the bipartite graph has parts A_x, B_x (x in G) and edges A_x ~ B_{x s} for s in S. Left
multiplication is an automorphism, so only two BFS runs (from A_1 and B_1) are needed to check
the diameter.

New in this version:
  * Group family: nonabelian metacyclic Z_m x|_r Z_k, then abelian Z_m x Z_k, then direct
    products H x Z_t with H metacyclic. The direct products add groups the earlier version
    never tried.
  * Symmetry reduction for d = 3: the six maps (right translation by an element of S, and
    inversion of S) preserve isomorphism class, so only the canonical pair (a, b) of each
    class is tested. Exhaustive search over all connection sets then costs about n^2/12
    BFS pairs per group.
  * Orders are scanned upward from a lower bound. Each order stops at its first success.

Python keeps the best of the known start and the C result, and checks everything with lib.is_valid.
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

#define MAXG 512
#define MAXV (2 * MAXG)
#define MAXDEG 16
#define MAXGRP 512

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

/* ------------------------------------------------------------ group family */

typedef struct { int kind, m, k, r, t; } Grp;
/* kind 0: Z_m x|_r Z_k.  kind 1: (Z_m x|_r Z_k) x Z_t. */
static Grp groups[MAXGRP];
static int ngroups;

static void add_group(int kind, int m, int k, int r, int t) {
    if (ngroups < MAXGRP) {
        groups[ngroups].kind = kind;
        groups[ngroups].m = m;
        groups[ngroups].k = k;
        groups[ngroups].r = r;
        groups[ngroups].t = t;
        ngroups++;
    }
}

static void enum_groups(int n) {
    ngroups = 0;
    /* pass 0: nonabelian metacyclic (r != 1) */
    for (int m = 2; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 2; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            add_group(0, m, k, r, 1);
        }
    }
    /* pass 1: abelian Z_m x Z_k (includes cyclic Z_n) */
    for (int m = 2; m <= n; m++)
        if (n % m == 0) add_group(0, m, n / m, 1, 1);
    /* pass 2: direct products H x Z_t, H metacyclic of order n/t */
    for (int t = 2; t <= n / 2; t++) {
        if (n % t) continue;
        int nh = n / t;
        for (int m = 1; m <= nh; m++) {
            if (nh % m) continue;
            int k = nh / m;
            if (m == 1) { add_group(1, 1, k, 0, t); continue; }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                add_group(1, m, k, r, t);
            }
        }
    }
}

static int MT[MAXG * MAXG];   /* multiplication table of the current group */
static int MTH[MAXG * MAXG];  /* scratch table for the metacyclic factor */
static int INV[MAXG];         /* inverses */
static int NN;                /* current group order */
static int rp_[MAXG];

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void meta_table(int m, int k, int r, int *tab) {
    int n = m * k;
    rp_[0] = 1 % m;
    for (int b = 1; b < k; b++) rp_[b] = (int)((long)rp_[b - 1] * r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            tab[x * n + y] = (int)(((long)a + (long)rp_[b] * c) % m) * k + (b + e) % k;
        }
    }
}

/* Load group G into MT/INV. Identity is element 0. Returns the order. */
static int build_group(Grp G) {
    int n;
    if (G.kind == 0) {
        n = G.m * G.k;
        meta_table(G.m, G.k, G.r, MT);
    } else {
        int nh = G.m * G.k;
        n = nh * G.t;
        meta_table(G.m, G.k, G.r, MTH);
        for (int x = 0; x < n; x++) {
            int h1 = x / G.t, c1 = x % G.t;
            for (int y = 0; y < n; y++) {
                int h2 = y / G.t, c2 = y % G.t;
                MT[x * n + y] = MTH[h1 * nh + h2] * G.t + (c1 + c2) % G.t;
            }
        }
    }
    NN = n;
    for (int x = 0; x < n; x++) {
        INV[x] = -1;
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
    }
    return n;
}

/* ------------------------------------------------------- bi-Cayley checks */

static int dist_[MAXV], queue_[MAXV];

/* 1 iff every vertex of B(G,S) is within D of src.
 * A_x = x, B_h = NN + h. A_x ~ B_{x s}; B_h ~ A_{h s^-1}. */
static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

/* Canonical test for S = {0, a, b} (a < b, nonzero). The six images
 *   T -> {x t^-1 : x in T}  and its inverse-set, for t in T,
 * give isomorphic bi-Cayley graphs. Return 1 iff (a, b) is the smallest image. */
static int is_canon(int a, int b) {
    int n = NN;
    int T[3] = {0, a, b};
    for (int ti = 0; ti < 3; ti++) {
        int tinv = INV[T[ti]];
        for (int inv = 0; inv < 2; inv++) {
            int p = -1, q = -1;
            for (int j = 0; j < 3; j++) {
                if (j == ti) continue;
                int u = MT[T[j] * n + tinv];
                if (inv) u = INV[u];
                if (p < 0) p = u; else q = u;
            }
            if (p > q) { int tmp = p; p = q; q = tmp; }
            if (p < a || (p == a && q < b)) return 0;
        }
    }
    return 1;
}

/* Random connection set S = {0, s_1, ..., s_{d-1}} of distinct group elements. */
static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

/* ------------------------------------------------------------ search state */

static int bestN = 0;
static Grp bestG;
static int bestS[MAXDEG];

static void record_best(int n, const Grp *G, const int *S) {
    bestN = n;
    bestG = *G;
    for (int i = 0; i < d; i++) bestS[i] = S[i];
}

/* Find a valid connection set for order n. Returns 1 on success (stored in best*). */
static int search_n(int n) {
    enum_groups(n);
    int S[MAXDEG];
    for (int gi = 0; gi < ngroups; gi++) {
        if (now() >= t_end) return 0;
        int nn = build_group(groups[gi]);
        if (nn != n) continue;
        if (d == 2) {
            for (int a = 1; a < n; a++) {
                S[0] = 0; S[1] = a;
                if (reach_all(S, 0) && reach_all(S, n)) {
                    record_best(n, &groups[gi], S);
                    return 1;
                }
            }
        } else if (d == 3) {
            for (int a = 1; a < n; a++) {
                if (now() >= t_end) return 0;
                for (int b = a + 1; b < n; b++) {
                    if (!is_canon(a, b)) continue;
                    S[0] = 0; S[1] = a; S[2] = b;
                    if (reach_all(S, 0) && reach_all(S, n)) {
                        record_best(n, &groups[gi], S);
                        return 1;
                    }
                }
            }
        } else {
            for (int t = 0; t < 400; t++) {
                pick_set(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) {
                    record_best(n, &groups[gi], S);
                    return 1;
                }
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ explicit graph */

static int adjl[MAXV][MAXDEG], degl[MAXV];

static void add_e(int u, int v) {
    adjl[u][degl[u]++] = v;
    adjl[v][degl[v]++] = u;
}

/* Full BFS from every vertex with explicit adjacency. */
static int verify_explicit(int V) {
    static int dd[MAXV], qq[MAXV];
    for (int v = 0; v < V; v++)
        if (degl[v] > d || degl[v] < 1) return 0;
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int i = 0; i < degl[v]; i++) {
                int u = adjl[v][i];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void set_complete(void) {
    int V = 2 * d;
    for (int v = 0; v < V; v++) degl[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_e(a, d + b);
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_explicit(int V) {
    long m = 0;
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) m++;
    printf("%d %ld\n", V, m);
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) printf("%d %d\n", u, adjl[u][i]);
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget nlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long moore = moore_bound();
    long nmaxl = moore / 2;
    if (nmaxl > MAXG - 1) nmaxl = MAXG - 1;
    int nmax = (int)nmaxl;
    int nstart = nlo;
    if (nstart < d + 1) nstart = d + 1;

    if (d >= 2 && D >= 2) {
        for (int n = nstart; n <= nmax && now() < t_end; n++)
            search_n(n);
    }

    int ok = 0;
    if (bestN > 0) {
        int n = bestN, V = 2 * n;
        build_group(bestG);
        for (int v = 0; v < V; v++) degl[v] = 0;
        for (int x = 0; x < n; x++)
            for (int i = 0; i < d; i++) {
                int y = MT[x * n + bestS[i]];
                add_e(x, n + y);
            }
        ok = verify_explicit(V);
        if (ok) print_explicit(V);
    }
    if (!ok) set_complete();
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    half = moore // 2
    # Lower bound for the scan in half-order units: never below what we already have,
    # and about 0.49 of the Moore bound per side.
    nlo = max(d + 1, best[0] // 2 + 1, (half * 49) // 100)
    if nlo > half:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
