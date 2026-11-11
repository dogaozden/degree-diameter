"""Bold variant: annealed voltage lifts over semidirect products Z_m x| Z_k.

The graph is a d-regular bipartite lift of a base multigraph with NB vertices per
side. Each of the d layers is a permutation of the base vertices, and each dart
carries a voltage in a group G of order N. The lift has 2*NB*N vertices.

Left multiplication by G is an automorphism, so eccentricities are constant on
fibres. The diameter check therefore needs only 2*NB BFS runs, one from each base
representative. Simulated annealing minimises the number of (representative,
vertex) pairs at distance > D. A zero cost gives a valid graph, which is then
re-verified by a full BFS from every vertex before it is printed.

The C search targets lift orders above the current best, round-robins over NB,
and raises the target after each success. If nothing is found by 30% of the
budget, the target is lowered gradually so that a valid graph is still returned.
Python keeps the best of the known start and the C result, and checks everything
with lib.is_valid.
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
#include <math.h>

#define MAXN 1024
#define MAXB 6
#define MAXDEG 16
#define MAXV (2 * MAXB * MAXN)
#define MAXGRP 4096
#define ITERS 15000

static int d, D;
static long MOORE;
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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp grps[MAXGRP];
static int ngrp;

/* All semidirect products Z_m x| Z_k of order N (r = 1 gives abelian ones). */
static void enum_groups(int N) {
    ngrp = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ngrp < MAXGRP) {
                grps[ngrp].m = 1; grps[ngrp].k = k; grps[ngrp].r = 0;
                ngrp++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngrp < MAXGRP) {
                grps[ngrp].m = m; grps[ngrp].k = k; grps[ngrp].r = r;
                ngrp++;
            }
        }
    }
}

static int MT[MAXN * MAXN];  /* multiplication table of the current group */
static int INVG[MAXN];       /* inverses */
static int NG;               /* current group order */

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_group(Grp G) {
    int m = G.m, k = G.k, n = m * k;
    NG = n;
    static int rp[MAXN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INVG[x] = y; break; }
}

/* ---------------------------------------------------------- lift state */

static int NB;                  /* base vertices per side */
static int N;                   /* group order */
static int PERM[MAXDEG][MAXB];  /* layer t: left i -> right PERM[t][i] */
static int PINV[MAXDEG][MAXB];  /* layer t: right j -> left PINV[t][j] */
static int VOLT[MAXDEG][MAXB];  /* voltage of dart (t, i) */

static int dist_[MAXV], queue_[MAXV];

/* Left vertex (i,x) = i*N + x; right vertex (j,y) = (NB + j)*N + y.
 * Edge (i,x) ~ (j, x*g) for j = PERM[t][i], g = VOLT[t][i]. */
static inline int nbr(int v, int t) {
    if (v < NB * N) {
        int i = v / N, x = v % N;
        int j = PERM[t][i];
        int y = MT[x * N + VOLT[t][i]];
        return (NB + j) * N + y;
    } else {
        int j = v / N - NB, y = v % N;
        int i = PINV[t][j];
        int x = MT[y * N + INVG[VOLT[t][i]]];
        return i * N + x;
    }
}

/* Number of vertices not within distance D of s. */
static int bad_from(int s) {
    int V = 2 * NB * N;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[s] = 0;
    queue_[tail++] = s;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        for (int t = 0; t < d; t++) {
            int u = nbr(v, t);
            if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
        }
    }
    return V - tail;
}

/* Sum of bad counts over the 2*NB fibre representatives. */
static int total_cost(void) {
    int c = 0;
    for (int i = 0; i < NB; i++) {
        c += bad_from(i * N);
        c += bad_from((NB + i) * N);
    }
    return c;
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < NB; i++) PERM[t][i] = i;
        for (int i = NB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = PERM[t][i]; PERM[t][i] = PERM[t][j]; PERM[t][j] = tmp;
        }
        for (int i = 0; i < NB; i++) PINV[t][PERM[t][i]] = i;
        for (int i = 0; i < NB; i++) VOLT[t][i] = rndint(N);
    }
}

static void swap_perm(int t, int i, int k) {
    int a = PERM[t][i], b = PERM[t][k];
    PERM[t][i] = b; PERM[t][k] = a;
    PINV[t][b] = i; PINV[t][a] = k;
}

/* ---------------------------------------------------------- explicit graph */

static int adjl[MAXV][MAXDEG], degl[MAXV];

/* Materialise the lift with duplicate edges removed. Returns the vertex count or -1. */
static int build_explicit(void) {
    int V = 2 * NB * N;
    for (int v = 0; v < V; v++) degl[v] = 0;
    for (int v = 0; v < V; v++)
        for (int t = 0; t < d; t++) {
            int u = nbr(v, t);
            int seen = 0;
            for (int q = 0; q < degl[v]; q++)
                if (adjl[v][q] == u) { seen = 1; break; }
            if (seen) continue;
            if (degl[v] >= MAXDEG || degl[u] >= MAXDEG) return -1;
            adjl[v][degl[v]++] = u;
            adjl[u][degl[u]++] = v;
        }
    return V;
}

/* Full BFS from every vertex on the explicit graph. */
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

/* ---------------------------------------------------------- search */

static int have_sol = 0;
static Grp solG;
static int solb, solN;
static int solP[MAXDEG][MAXB], solV[MAXDEG][MAXB];

static void save_solution(Grp G) {
    have_sol = 1;
    solG = G;
    solb = NB;
    solN = N;
    memcpy(solP, PERM, sizeof(PERM));
    memcpy(solV, VOLT, sizeof(VOLT));
}

/* Anneal voltages and permutations for NB = b, group order n until a zero-cost
 * state appears or the time runs out. Returns 1 on success (solution saved). */
static int anneal_level(int b, int n, double until) {
    enum_groups(n);
    if (ngrp == 0) return 0;
    NB = b;
    N = n;
    while (now() < until) {
        Grp G = grps[rndint(ngrp)];
        build_group(G);
        random_state();
        int c = total_cost();
        double T0 = 1.0 + 0.03 * c, T1 = 0.3;
        for (int it = 0; it < ITERS && c > 0; it++) {
            if ((it & 255) == 0 && now() > until) break;
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            int t = rndint(d), i = rndint(NB);
            if (NB == 1 || rndint(2) == 0) {
                int old = VOLT[t][i];
                int nv = rndint(N);
                if (nv == old) continue;
                VOLT[t][i] = nv;
                int nc = total_cost();
                int delta = nc - c;
                if (delta <= 0 || rnd01() < exp(-delta / T)) c = nc;
                else VOLT[t][i] = old;
            } else {
                int k2 = rndint(NB - 1);
                if (k2 >= i) k2++;
                swap_perm(t, i, k2);
                int nc = total_cost();
                int delta = nc - c;
                if (delta <= 0 || rnd01() < exp(-delta / T)) c = nc;
                else swap_perm(t, i, k2);
            }
        }
        if (c == 0) {
            int V = build_explicit();
            if (V > 0 && verify_explicit(V)) {
                save_solution(G);
                return 1;
            }
        }
    }
    return 0;
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed budget tmin hard\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int tmin = atoi(argv[5]);
    int hard = atoi(argv[6]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    MOORE = moore_bound();
    if (MOORE > MAXV / 2) MOORE = MAXV / 2;

    int cur = tmin - 1;
    if (cur < hard - 1) cur = hard - 1;
    if (cur < 0) cur = 0;

    double slice = budget / 30.0;
    if (slice < 0.5) slice = 0.5;
    if (slice > 4.0) slice = 4.0;

    while (now() < t_end) {
        if (cur >= MOORE) break;
        for (int b = 1; b <= MAXB && now() < t_end; b++) {
            long Nl = cur / (2 * b) + 1;
            if (Nl > MAXN - 1) continue;
            long order = 2L * b * Nl;
            if (order > MOORE) continue;
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (anneal_level(b, (int)Nl, until)) {
                cur = (int)order;
                break;
            }
        }
        if (!have_sol && now() - t0 > 0.3 * budget && cur > hard - 1) {
            int nc = (int)(cur * 0.97);
            if (nc < hard - 1) nc = hard - 1;
            cur = nc;
        }
    }

    if (!have_sol) { printf("0 0\n"); return 0; }

    build_group(solG);
    NB = solb;
    N = solN;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < NB; i++) {
            PERM[t][i] = solP[t][i];
            VOLT[t][i] = solV[t][i];
        }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < NB; i++) PINV[t][PERM[t][i]] = i;
    int V = build_explicit();
    if (V <= 0 || !verify_explicit(V)) { printf("0 0\n"); return 0; }
    print_explicit(V);
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

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    hard = best[0] + 1
    tmin = max(hard, int(0.35 * moore))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), tmin, hard],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
