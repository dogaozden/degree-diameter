"""Bold variant: annealed non-Cayley lifts of small regular bipartite base graphs.

Instead of one bi-Cayley pair (a single A-vertex and a single B-vertex), this
version lifts a random d-regular bipartite multigraph on a + a base vertices
over a metacyclic group Z_m x| Z_k of order N. Each base dart (i, j) carries a
voltage g and joins A_i,x to B_j,x*g. The lift has 2aN vertices and is
left-multiplication invariant, so the diameter check only needs BFS from the
2a base identities.

For each base size a the C engine runs simulated-annealing style local search
over group choice, voltages, and base wiring. The objective is the number of
(source, vertex) pairs at distance more than D. Whenever a zero-objective lift
is found, the target order rises and the search continues. The C program
re-verifies its output with a full BFS before printing. Python keeps the known
start (or K_{d,d}) unless the engine returns a strictly larger graph that
passes lib.is_valid.
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

#define MAXN 1024
#define MAXA 8
#define MAXDEG 16
#define MAXDART (MAXA * MAXDEG)
#define MAXV (2 * MAXA * MAXN)
#define MAXGRP 4096
#define STALL 3000

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;
static long moore;
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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

static int GM, GK, GN;
static int RP[MAXN];
static Grp curG;

static void set_group(Grp G) {
    curG = G;
    GM = G.m;
    GK = G.k;
    GN = G.m * G.k;
    RP[0] = 1 % GM;
    for (int b = 1; b < GK; b++) RP[b] = (int)((long)RP[b - 1] * G.r % GM);
}

/* element (a,b) coded a*GK + b; (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int first = (int)(((long)a + (long)RP[b] * c) % GM);
    int second = (b + e) % GK;
    return first * GK + second;
}

static inline int ginv(int g) {
    int a = g / GK, b = g - a * GK;
    int nb = (GK - b) % GK;
    int c = (int)(((long)GM - ((long)RP[nb] * a) % GM) % GM);
    return c * GK + nb;
}

static int enum_groups(int n, Grp *out) {
    int c = 0;
    for (int m = 1; m <= n && c < MAXGRP; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            out[c].m = 1; out[c].k = k; out[c].r = 0;
            c++;
            continue;
        }
        for (int r = 1; r < m && c < MAXGRP; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            out[c].m = m; out[c].k = k; out[c].r = r;
            c++;
        }
    }
    return c;
}

/* ---------------------------------------------------------- base graph state */

static int CA;                  /* base vertices per side */
static int ND;                  /* darts = d * CA */
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART], dGI[MAXDART];
static int adjA[MAXA][MAXDEG], adjB[MAXA][MAXDEG];
static int sI[MAXDART], sJ[MAXDART], sG[MAXDART];

static void save_state(void) {
    memcpy(sI, dI, sizeof(int) * (size_t)ND);
    memcpy(sJ, dJ, sizeof(int) * (size_t)ND);
    memcpy(sG, dG, sizeof(int) * (size_t)ND);
}
static void restore_state(void) {
    memcpy(dI, sI, sizeof(int) * (size_t)ND);
    memcpy(dJ, sJ, sizeof(int) * (size_t)ND);
    memcpy(dG, sG, sizeof(int) * (size_t)ND);
}

/* Random d-regular bipartite base multigraph with a vertices per side. */
static void random_base(int a) {
    CA = a;
    ND = a * d;
    for (int p = 0; p < ND; p++) {
        dI[p] = p / d;
        dJ[p] = p / d;
    }
    for (int p = ND - 1; p > 0; p--) {
        int q = rndint(p + 1);
        int t = dJ[p]; dJ[p] = dJ[q]; dJ[q] = t;
    }
    for (int p = 0; p < ND; p++) dG[p] = rndint(GN);
}

/* No two darts with the same (i, j, voltage): otherwise lift has repeated edges. */
static int dupfree(void) {
    for (int p = 0; p < ND; p++)
        for (int q = p + 1; q < ND; q++)
            if (dI[p] == dI[q] && dJ[p] == dJ[q] && dG[p] == dG[q]) return 0;
    return 1;
}

static void build_adj(void) {
    int cA[MAXA], cB[MAXA];
    for (int i = 0; i < MAXA; i++) { cA[i] = 0; cB[i] = 0; }
    for (int p = 0; p < ND; p++) {
        int i = dI[p], j = dJ[p];
        adjA[i][cA[i]++] = p;
        adjB[j][cB[j]++] = p;
        dGI[p] = ginv(dG[p]);
    }
}

/* ---------------------------------------------------------- objective */

static int dist_[MAXV], qu[MAXV];

/* Number of vertices NOT within distance D of the source (BFS from base identity). */
static int bfs_bad(int src, int a) {
    int N = GN, V = 2 * a * N, AN = a * N;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < AN) {
            int i = v / N, x = v - i * N;
            for (int k = 0; k < d; k++) {
                int p = adjA[i][k];
                int u = AN + dJ[p] * N + gmul(x, dG[p]);
                if (dist_[u] < 0) { dist_[u] = dv + 1; qu[tail++] = u; }
            }
        } else {
            int w = v - AN, j = w / N, y = w - j * N;
            for (int k = 0; k < d; k++) {
                int p = adjB[j][k];
                int u = dI[p] * N + gmul(y, dGI[p]);
                if (dist_[u] < 0) { dist_[u] = dv + 1; qu[tail++] = u; }
            }
        }
    }
    return V - tail;
}

/* Zero iff the lift has diameter <= D (left multiplication is an automorphism,
 * so eccentricities are constant on each base orbit). */
static int score(void) {
    int a = CA, N = GN;
    build_adj();
    int bad = 0;
    for (int s = 0; s < 2 * a; s++) {
        int src = (s < a) ? s * N : a * N + (s - a) * N;
        bad += bfs_bad(src, a);
    }
    return bad;
}

/* ---------------------------------------------------------- best record */

static int bestV = 0, bestA = 0, bestN = 0, bestND = 0;
static Grp bestG;
static int bI[MAXDART], bJ[MAXDART], bG[MAXDART];

static void record(void) {
    bestV = 2 * CA * GN;
    bestA = CA;
    bestN = GN;
    bestG = curG;
    bestND = ND;
    memcpy(bI, dI, sizeof(int) * (size_t)ND);
    memcpy(bJ, dJ, sizeof(int) * (size_t)ND);
    memcpy(bG, dG, sizeof(int) * (size_t)ND);
}

/* Search for a valid lift of base size a and group order N until `until`.
 * Returns 1 and records the result on success. */
static int attempt(int a, int N, double until) {
    static Grp groups[MAXGRP];
    int ng = enum_groups(N, groups);
    if (ng == 0) return 0;
    while (now() < until) {
        set_group(groups[rndint(ng)]);
        random_base(a);
        int ok = 0;
        for (int t = 0; t < 100; t++) {
            if (dupfree()) { ok = 1; break; }
            for (int p = 0; p < ND; p++) dG[p] = rndint(GN);
        }
        if (!ok) continue;

        int cur = score();
        int stall = 0;
        while (cur > 0 && stall < STALL && now() < until) {
            save_state();
            if (rnd01() < 0.8) {
                int p = rndint(ND);
                dG[p] = rndint(GN);
            } else {
                int p = rndint(ND), q = rndint(ND);
                int t = dJ[p]; dJ[p] = dJ[q]; dJ[q] = t;
            }
            if (!dupfree()) {
                restore_state();
                stall++;
                continue;
            }
            int nw = score();
            if (nw <= cur) {
                if (nw < cur) stall = 0;
                else stall++;
                cur = nw;
            } else {
                restore_state();
                stall++;
            }
        }
        if (cur == 0) {
            record();
            return 1;
        }
    }
    return 0;
}

/* Keep ramping the target order for base size a while time remains. */
static void run_for_a(int a, double until) {
    while (now() < until) {
        int N = bestV / (2 * a) + 1;
        if (N < d) N = d;
        if (N > MAXN || 2L * a * N > moore || 2 * a * N > MAXV) return;
        if (!attempt(a, N, until)) return;
    }
}

/* ---------------------------------------------------------- output */

static int output_best(void) {
    if (bestV <= 0) return 0;
    int a = bestA, N = bestN, V = 2 * a * N;
    set_group(bestG);
    CA = a;
    ND = bestND;
    memcpy(dI, bI, sizeof(int) * (size_t)ND);
    memcpy(dJ, bJ, sizeof(int) * (size_t)ND);
    memcpy(dG, bG, sizeof(int) * (size_t)ND);

    static int adjl[MAXV][MAXDEG];
    static int degl[MAXV];
    static int eu[MAXV * MAXDEG / 2 + 8], ev[MAXV * MAXDEG / 2 + 8];
    static int dd[MAXV], qq[MAXV];

    for (int v = 0; v < V; v++) degl[v] = 0;
    int E = 0;
    for (int p = 0; p < ND; p++) {
        for (int x = 0; x < N; x++) {
            int u = dI[p] * N + x;
            int w = a * N + dJ[p] * N + gmul(x, dG[p]);
            if (degl[u] >= MAXDEG || degl[w] >= MAXDEG) return 0;
            if (E >= MAXV * MAXDEG / 2) return 0;
            eu[E] = u;
            ev[E] = w;
            E++;
            adjl[u][degl[u]++] = w;
            adjl[w][degl[w]++] = u;
        }
    }
    /* Explicit checks: degrees, simple graph, diameter. */
    for (int v = 0; v < V; v++) {
        if (degl[v] < 1 || degl[v] > d) return 0;
        for (int i = 0; i < degl[v]; i++)
            for (int j = i + 1; j < degl[v]; j++)
                if (adjl[v][i] == adjl[v][j]) return 0;
    }
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
    printf("%d %d\n", V, E);
    for (int e = 0; e < E; e++) printf("%d %d\n", eu[e], ev[e]);
    return 1;
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now();
    t_end = t0 + budget * 0.9;
    moore = moore_bound();

    double slice = budget / 16.0;
    if (slice < 0.5) slice = 0.5;
    if (slice > 5.0) slice = 5.0;

    while (now() < t_end && bestV < moore) {
        for (int a = 1; a <= MAXA && now() < t_end; a++) {
            double until = now() + slice;
            if (until > t_end) until = t_end;
            run_for_a(a, until);
        }
    }

    if (!output_best()) printf("0 0\n");
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

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
