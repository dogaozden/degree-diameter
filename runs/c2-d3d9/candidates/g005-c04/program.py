"""Multi-orbit bi-Cayley voltage lifts with local search.

Idea (new relative to the single-orbit bi-Cayley parent): take a base bipartite
multigraph with T vertices per side and degree d, where each base dart (i, j, g)
carries a voltage g in a metacyclic group G of order n. The lift has vertices
A_{i,x}, B_{j,h} (x, h in G) and edges A_{i,x} ~ B_{j,xg}. Order = 2*T*n.

Left multiplication by G is an automorphism, so the diameter test needs only
2T BFS runs, one from A_{i,e} and one from B_{j,e} per orbit.

Search: for each even order V (scanned upward from a lower bound), choose T and
the group at random, build a random connected base (d random permutations of
T), then run a local search that mutates one voltage at a time. The cost is the
total number of pairs not reached within D from the 2T representatives, and
moves that do not increase the cost are accepted. A cost of 0 gives a
d-regular bipartite graph of diameter at most D. The C program verifies the
explicit graph before printing it, and falls back to K_{d,d} otherwise.
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

#define MAXV 2048
#define MAXDEG 16
#define TMAX 8
#define MAXGRP 16384
#define LS_STEPS 200

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

/* ---------------------------------------------------------- metacyclic groups */

typedef struct { int m, k, r; } Grp;
static Grp glist[MAXGRP];
static int ng_list;

/* All groups Z_m x| Z_k with m*k = n, element (a,b) coded a*k+b. */
static void enum_groups(int n) {
    ng_list = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ng_list < MAXGRP) {
                glist[ng_list].m = m;
                glist[ng_list].k = k;
                glist[ng_list].r = r;
                ng_list++;
            }
        }
    }
}

static int gm, gk, gr, NG, T, ND;
static int rp[MAXV];

static void set_group(Grp G, int n) {
    gm = G.m; gk = G.k; gr = G.r; NG = n;
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
}

/* (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / gk, b = x % gk;
    int c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

/* (a,b)^-1 = (-r^(-b) a, -b), with r^k = 1 so r^(-b) = r^(k-b). */
static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    return (int)(((long)gm - ((long)rp[nb] * a) % gm) % gm) * gk + nb;
}

/* ---------------------------------------------------------- voltage lift state */

/* Dart index dart = i*d + s is the s-th edge out of A-orbit i. */
static int dA[TMAX * MAXDEG], dB[TMAX * MAXDEG], dG[TMAX * MAXDEG], dGi[TMAX * MAXDEG];
static int adjB[TMAX][MAXDEG];   /* darts incident to B-orbit j */

static int base_connected(void) {
    int visA[TMAX], visB[TMAX];
    for (int i = 0; i < T; i++) { visA[i] = 0; visB[i] = 0; }
    visA[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int s = 0; s < ND; s++) {
            int i = dA[s], j = dB[s];
            if (visA[i] && !visB[j]) { visB[j] = 1; changed = 1; }
            if (visB[j] && !visA[i]) { visA[i] = 1; changed = 1; }
        }
    }
    for (int i = 0; i < T; i++)
        if (!visA[i] || !visB[i]) return 0;
    return 1;
}

/* d random permutations of the T orbits give a d-regular base multigraph. */
static int random_base(void) {
    int perm[TMAX];
    for (int attempt = 0; attempt < 200; attempt++) {
        for (int s = 0; s < d; s++) {
            for (int i = 0; i < T; i++) perm[i] = i;
            for (int i = T - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = perm[i]; perm[i] = perm[r]; perm[r] = tmp;
            }
            for (int i = 0; i < T; i++) { dA[i * d + s] = i; dB[i * d + s] = perm[i]; }
        }
        ND = T * d;
        if (base_connected()) return 1;
    }
    return 0;
}

static void build_adjB(void) {
    int cnt[TMAX];
    for (int j = 0; j < T; j++) cnt[j] = 0;
    for (int s = 0; s < ND; s++) {
        int j = dB[s];
        adjB[j][cnt[j]++] = s;
    }
}

/* 1 if dart carries voltage g and another dart with the same (i,j) already does. */
static int conflicts(int dart, int g) {
    for (int s = 0; s < ND; s++) {
        if (s == dart) continue;
        if (dA[s] == dA[dart] && dB[s] == dB[dart] && dG[s] == g) return 1;
    }
    return 0;
}

static int dup_earlier(int dart, int g) {
    for (int s = 0; s < dart; s++)
        if (dA[s] == dA[dart] && dB[s] == dB[dart] && dG[s] == g) return 1;
    return 0;
}

/* ---------------------------------------------------------- implicit graph */

/* A_{i,x} = i*n + x, B_{j,h} = T*n + j*n + h. A_{i,x} ~ B_{j, x g} for each dart (i,j,g). */
static int neighbors(int v, int *out) {
    int n = NG;
    if (v < T * n) {
        int i = v / n, x = v % n;
        for (int s = 0; s < d; s++) {
            int dart = i * d + s;
            out[s] = T * n + dB[dart] * n + gmul(x, dG[dart]);
        }
    } else {
        int w = v - T * n;
        int j = w / n, h = w % n;
        for (int c = 0; c < d; c++) {
            int dart = adjB[j][c];
            out[c] = dA[dart] * n + gmul(h, dGi[dart]);
        }
    }
    return d;
}

static int distb[MAXV], qb[MAXV];

static int bfs_reach(int src) {
    int V = 2 * T * NG;
    for (int i = 0; i < V; i++) distb[i] = -1;
    int head = 0, tail = 0;
    int out[MAXDEG];
    distb[src] = 0;
    qb[tail++] = src;
    while (head < tail) {
        int v = qb[head++];
        int dv = distb[v];
        if (dv >= D) continue;
        neighbors(v, out);
        for (int s = 0; s < d; s++) {
            int u = out[s];
            if (distb[u] < 0) { distb[u] = dv + 1; qb[tail++] = u; }
        }
    }
    return tail;
}

/* Number of (representative, vertex) pairs not reached within D. 0 iff diameter <= D. */
static int cost_fn(void) {
    int V = 2 * T * NG;
    long c = 0;
    for (int i = 0; i < T; i++) c += V - bfs_reach(i * NG);
    for (int j = 0; j < T; j++) c += V - bfs_reach(T * NG + j * NG);
    return (int)c;
}

/* ---------------------------------------------------------- explicit best */

static int bestFound = 0;
static int bestV = 0;
static int bestSide = 0;
static int bestAdj[MAXV][MAXDEG];

static void save_best(void) {
    int V = 2 * T * NG;
    int out[MAXDEG];
    for (int v = 0; v < V; v++) {
        neighbors(v, out);
        for (int s = 0; s < d; s++) bestAdj[v][s] = out[s];
    }
    bestV = V;
    bestSide = T * NG;
    bestFound = 1;
}

/* ---------------------------------------------------------- search */

static int try_restart(void) {
    if (!random_base()) return 0;
    for (int dart = 0; dart < ND; dart++) {
        int g;
        do { g = rndint(NG); } while (dup_earlier(dart, g));
        dG[dart] = g;
        dGi[dart] = ginv(g);
    }
    build_adjB();
    int c = cost_fn();
    for (int st = 0; st < LS_STEPS && c > 0; st++) {
        int dart = rndint(ND);
        int g = rndint(NG);
        if (g == dG[dart] || conflicts(dart, g)) continue;
        int old = dG[dart], oldi = dGi[dart];
        dG[dart] = g;
        dGi[dart] = ginv(g);
        int nc = cost_fn();
        if (nc <= c || (nc == c + 1 && rndint(16) == 0)) {
            c = nc;
        } else {
            dG[dart] = old;
            dGi[dart] = oldi;
        }
    }
    if (c == 0) {
        save_best();
        return 1;
    }
    return 0;
}

/* Try orders V = 2*T*n for every T that divides V/2 with n >= d+1. */
static int search_V(int V, double until) {
    int Ts[TMAX], nt = 0;
    for (int t = 1; t <= TMAX; t++) {
        if (V % (2 * t)) continue;
        int n = V / (2 * t);
        if (n < d + 1 || n > MAXV) continue;
        Ts[nt++] = t;
    }
    if (nt == 0) return 0;
    while (now() < until) {
        int t = Ts[rndint(nt)];
        int n = V / (2 * t);
        enum_groups(n);
        if (ng_list == 0) continue;
        Grp G = glist[rndint(ng_list)];
        set_group(G, n);
        T = t;
        ND = T * d;
        if (try_restart()) return 1;
    }
    return 0;
}

/* ---------------------------------------------------------- output */

static int verify_explicit(int V) {
    static int dd[MAXV], qq[MAXV];
    for (int u = 0; u < V; u++) {
        for (int s = 0; s < d; s++) {
            int w = bestAdj[u][s];
            if (w < 0 || w >= V || w == u) return 0;
            if ((u < bestSide) == (w < bestSide)) return 0;
            for (int s2 = 0; s2 < s; s2++)
                if (bestAdj[u][s2] == w) return 0;
            int back = 0;
            for (int t2 = 0; t2 < d; t2++)
                if (bestAdj[w][t2] == u) back = 1;
            if (!back) return 0;
        }
    }
    for (int src = 0; src < V; src++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[src] = 0;
        qq[tail++] = src;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int k = 0; k < d; k++) {
                int u = bestAdj[v][k];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void print_best(void) {
    int V = bestV;
    long m = 0;
    for (int u = 0; u < V; u++)
        for (int s = 0; s < d; s++)
            if (u < bestAdj[u][s]) m++;
    printf("%d %ld\n", V, m);
    for (int u = 0; u < V; u++)
        for (int s = 0; s < d; s++)
            if (u < bestAdj[u][s]) printf("%d %d\n", u, bestAdj[u][s]);
}

static void set_complete(void) {
    int V = 2 * d;
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget vstart\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int vstart = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long vmax = moore_bound();
    if (vmax > MAXV) vmax = MAXV;
    if (vmax & 1) vmax--;

    int V = vstart;
    if (V < 2 * (d + 1)) V = 2 * (d + 1);
    if (V & 1) V++;

    double chunk = budget / 40.0;
    if (chunk < 0.3) chunk = 0.3;
    if (chunk > 2.0) chunk = 2.0;

    for (; V <= vmax && now() < t_end; V += 2) {
        double until = now() + chunk;
        if (until > t_end) until = t_end;
        search_V(V, until);
    }

    if (bestFound && verify_explicit(bestV)) {
        print_best();
    } else {
        set_complete();
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    # First order to try: just above what we already have, and not far below the
    # Moore bound (the scan goes upward from here).
    vstart = max(best[0] + 2, int(0.45 * moore))
    if vstart % 2:
        vstart += 1

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vstart],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
