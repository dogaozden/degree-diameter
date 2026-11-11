"""Combined search for the d=5, D=7 target: bi-Cayley voltage annealing with a new multiplier-symmetric
voltage family, elite restarts, unit-wise steepest-descent polishing, and ruin-and-recreate growth.

For D >= 6 and d in {3, 5} the start is the incidence graph of the split Cayley hexagon H(q),
q = d-1 in {2, 4}: bipartite, degree d, diameter 6, so valid for D = 7.

NEW IDEA (multiplier-symmetric voltage sets). For a semidirect group G = Z_m x| Z_k, the map
phi(a, b) = (s*a mod m, b) with s = m-1 (i.e. -1) is an automorphism. If the voltage set S is
phi-invariant, then a_x -> a_{phi(x)}, b_y -> b_{phi(y)} is an automorphism of the bi-Cayley graph,
so the search space shrinks to phi-orbits. Voltage slots are grouped into units: fixed units
(phi(x) = x, single slot) and pair units (x and phi(x) in one unit). Plain mode is the special case
where every slot is its own unit with no symmetry. Climbing, elite restarts and polishing all act on
units, so one code path serves both modes. Symmetric attempts are drawn with probability 1/2 when m >= 3.

Phases within the C budget:
  1. Bi-Cayley lifts of order 2N, with N drawn from a window above the incumbent (u^1.5 bias to the
     low end). Each attempt is plain or symmetric. Climbs cool geometrically from 2.0 to 0.2.
     Residuals of at most POLISH_MAX bad pairs are polished by steepest descent over unit moves.
  2. Greedy-endpoint growth by vertex pairs, with ruin-and-recreate when growth stalls.
Every candidate is verified in C and again in Python with lib.is_valid. The algebraic starts are the
fallback, so every case returns a valid graph.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXH 2048
#define INIT_TRIALS 6
#define GREEDY_CAND 24
#define BC_SPAN 200
#define BC_STEPS 6000
#define BC_ATTEMPTS 8
#define BC_GROUPS 6
#define POLISH_MAX 400
#define SYM_PROB 0.5

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D, by bitsets. Fills badv per vertex. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Z_m x|_r Z_k: element a*k + b (identity 0), (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random admissible semidirect product of order N (reservoir sampling). */
static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* Prefer a non-abelian choice (r != 1, k > 1) when one is sampled quickly. */
static int pick_group_bc(int N, Grp *G) {
    for (int tries = 0; tries < 8; tries++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

/* ---------------- bi-Cayley lift search ----------------
 * Vertices: a_x = x (side 0), b_x = N + x (side 1), x in G.
 * Edges: a_x -- b_{x * g_t} for t = 0..d-1, with g_0 = e and distinct g_t.
 * Left multiplication is transitive on each side, so BFS from a_e and b_e suffices. */

static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int PHIT[MAXH];   /* multiplier automorphism table, identity when symmetry is off */
static int NN, GM, GK;
static int dist_bc[2 * MAXH], seen_bc[2 * MAXH], q_bc[2 * MAXH];
static int stamp_bc = 0;

static void setup_group(int N, const Grp *G) {
    NN = N;
    GM = G->m;
    GK = G->k;
    for (int x = 0; x < N; x++) {
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) row[y] = gmul(G, x, y);
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

/* phi(a,b) = (-a mod m, b) is an automorphism of Z_m x|_r Z_k for every unit -1. */
static void set_phi(int sym) {
    for (int x = 0; x < NN; x++) {
        if (!sym) { PHIT[x] = x; continue; }
        int a = x / GK, b = x % GK;
        PHIT[x] = ((GM - 1) * a % GM) * GK + b;
    }
}

/* Number of (source, vertex) pairs at distance > D, sources a_e and b_e. */
static long eval_bad(const int *gv) {
    int N = NN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_bc++;
        seen_bc[src] = stamp_bc;
        dist_bc[src] = 0;
        q_bc[tail++] = src;
        while (head < tail) {
            int v = q_bc[head++];
            int dv = dist_bc[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MTAB + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_bc[u] != stamp_bc) {
                        seen_bc[u] = stamp_bc;
                        dist_bc[u] = dv + 1;
                        q_bc[tail++] = u;
                    }
                }
            } else {
                const int *row = MTAB + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (seen_bc[u] != stamp_bc) {
                        seen_bc[u] = stamp_bc;
                        dist_bc[u] = dv + 1;
                        q_bc[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Units: groups of voltage slots that change together.
 * kind 0: one free slot. kind 1: one slot whose element is phi-fixed.
 * kind 2: two slots holding x and phi(x), with phi(x) != x. */
typedef struct { int nu; int s0[MAXD], s1[MAXD], kind[MAXD]; } Units;

static void plain_units(Units *U) {
    U->nu = d - 1;
    for (int u = 0; u < U->nu; u++) {
        U->s0[u] = u + 1; U->s1[u] = -1; U->kind[u] = 0;
    }
}

/* f fixed single slots, then (d-1-f)/2 phi-pairs. f must have the parity of d-1. */
static void sym_units(Units *U, int f) {
    int nu = 0;
    for (int t = 1; t <= f; t++) {
        U->s0[nu] = t; U->s1[nu] = -1; U->kind[nu] = 1; nu++;
    }
    for (int t = f + 1; t + 1 <= d - 1; t += 2) {
        U->s0[nu] = t; U->s1[nu] = t + 1; U->kind[nu] = 2; nu++;
    }
    U->nu = nu;
}

/* Is x in use by a slot other than the slots of unit u? */
static int in_use(const int *gv, const Units *U, int u, int x) {
    for (int i = 0; i < d; i++) {
        if (i == U->s0[u] || i == U->s1[u]) continue;
        if (gv[i] == x) return 1;
    }
    return 0;
}

static int accept_x(const int *gv, const Units *U, int u, int x, int *x1) {
    int kind = U->kind[u];
    if (kind == 1) {
        if (PHIT[x] != x || in_use(gv, U, u, x)) return 0;
        *x1 = -1;
        return 1;
    }
    if (kind == 2) {
        int y = PHIT[x];
        if (y == x || in_use(gv, U, u, x) || in_use(gv, U, u, y)) return 0;
        *x1 = y;
        return 1;
    }
    if (in_use(gv, U, u, x)) return 0;
    *x1 = -1;
    return 1;
}

static int propose(const int *gv, const Units *U, int u, int *x0, int *x1) {
    for (int tries = 0; tries < 400; tries++) {
        int x = rndint(NN);
        if (accept_x(gv, U, u, x, x1)) { *x0 = x; return 1; }
    }
    return 0;
}

static void apply_unit(int *gv, const Units *U, int u, int x0, int x1) {
    gv[U->s0[u]] = x0;
    if (U->s1[u] >= 0) gv[U->s1[u]] = x1;
}

static int fill_voltages(int *gv, const Units *U) {
    gv[0] = 0;
    for (int t = 1; t < d; t++) gv[t] = -1;
    for (int u = 0; u < U->nu; u++) {
        int x0, x1;
        if (!propose(gv, U, u, &x0, &x1)) return 0;
        apply_unit(gv, U, u, x0, x1);
    }
    return 1;
}

/* Annealed unit hill-climb; gv[0] = 0 stays fixed.
 * Returns the best objective seen; bestgv receives the voltages that achieved it. */
static long climb(int *gv, const Units *U, int *bestgv, double until) {
    long bad = eval_bad(gv);
    long bestb = bad;
    memcpy(bestgv, gv, sizeof(int) * d);
    double T = 2.0;
    const double alpha = pow(0.1, 1.0 / BC_STEPS);
    for (long s = 0; s < BC_STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int u = rndint(U->nu);
        int o0 = gv[U->s0[u]];
        int o1 = U->s1[u] >= 0 ? gv[U->s1[u]] : -1;
        int x0, x1;
        if (propose(gv, U, u, &x0, &x1)) {
            apply_unit(gv, U, u, x0, x1);
            long nb = eval_bad(gv);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
                if (bad < bestb) {
                    bestb = bad;
                    memcpy(bestgv, gv, sizeof(int) * d);
                }
            } else {
                gv[U->s0[u]] = o0;
                if (U->s1[u] >= 0) gv[U->s1[u]] = o1;
            }
        }
        T *= alpha;
        if (T < 0.2) T = 0.2;
    }
    return bestb;
}

/* Steepest-descent polish over unit moves: evaluate every admissible replacement of every unit,
 * apply the best strict improvement, repeat until none helps or the deadline passes. */
static long polish(int *gv, const Units *U, long bad, double deadline) {
    while (bad > 0 && now() < deadline) {
        long bestb = bad;
        int bu = -1, bx0 = 0, bx1 = -1;
        for (int u = 0; u < U->nu && now() < deadline; u++) {
            int o0 = gv[U->s0[u]];
            int o1 = U->s1[u] >= 0 ? gv[U->s1[u]] : -1;
            for (int x = 0; x < NN; x++) {
                if (now() >= deadline) break;
                int x1;
                if (!accept_x(gv, U, u, x, &x1)) continue;
                apply_unit(gv, U, u, x, x1);
                long nb = eval_bad(gv);
                if (nb < bestb) { bestb = nb; bu = u; bx0 = x; bx1 = x1; }
                gv[U->s0[u]] = o0;
                if (U->s1[u] >= 0) gv[U->s1[u]] = o1;
            }
        }
        if (bu < 0) break;
        apply_unit(gv, U, bu, bx0, bx1);
        bad = bestb;
    }
    return bad;
}

static void build_bc(Graph *g, int N, const int *gv) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + MTAB[(size_t)x * N + gv[t]]);
}

static Graph bc_cand;

/* Search bi-Cayley lifts of order 2N > best->n, raising the bar on each success.
 * Attempts are plain or phi-symmetric. Within one (N, group) pair, later attempts restart from
 * the elite voltage set (same mode) with one unit re-drawn, with probability 0.6. */
static void bicayley_search(Graph *best, double until) {
    static int gv[MAXD], bestgv[MAXD], elite[MAXD];
    static Grp G;
    static Units U, EU;
    int Nlo = best->n / 2 + 1;
    if (Nlo < d + 1) Nlo = d + 1;
    long moore = moore_bound();
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXH) Nmax_l = MAXH;
    if (Nmax_l > MAXN / 2) Nmax_l = MAXN / 2;
    int Nmax = (int)Nmax_l;
    while (now() < until && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > BC_SPAN) span = BC_SPAN;
        double u0 = rnd01();
        int N = Nlo + (int)(u0 * sqrt(u0) * span);
        if (N > Nmax) N = Nmax;
        for (int grp = 0; grp < BC_GROUPS && now() < until; grp++) {
            if (!pick_group_bc(N, &G)) break;
            setup_group(N, &G);
            int symok = G.m >= 3;
            long elite_bad = -1;
            int elite_sym = 0;
            for (int att = 0; att < BC_ATTEMPTS && now() < until; att++) {
                int sym = symok && rnd01() < SYM_PROB;
                set_phi(sym);
                int ok = 0;
                if (elite_bad >= 0 && elite_sym == sym && rnd01() < 0.6) {
                    U = EU;
                    memcpy(gv, elite, sizeof(int) * d);
                    if (U.nu > 0) {
                        int uu = rndint(U.nu), x0, x1;
                        ok = propose(gv, &U, uu, &x0, &x1);
                        if (ok) apply_unit(gv, &U, uu, x0, x1);
                    }
                } else {
                    if (sym) {
                        int f = rndint(d);
                        if ((d - 1 - f) & 1) f = f > 0 ? f - 1 : f + 1;
                        sym_units(&U, f);
                    } else {
                        plain_units(&U);
                    }
                    ok = fill_voltages(gv, &U);
                }
                if (!ok) continue;
                long b = climb(gv, &U, bestgv, until);
                if (b > 0 && b <= POLISH_MAX) {
                    double pd = now() + 2.0;
                    if (pd > until) pd = until;
                    b = polish(bestgv, &U, b, pd);
                }
                if (b == 0) {
                    build_bc(&bc_cand, N, bestgv);
                    if (bc_cand.n > best->n && is_valid(&bc_cand)) {
                        copy_graph(best, &bc_cand);
                        Nlo = N + 1;
                        return bicayley_search(best, until);
                    }
                    continue;
                }
                if (elite_bad < 0 || b < elite_bad) {
                    elite_bad = b;
                    elite_sym = sym;
                    memcpy(elite, bestgv, sizeof(int) * d);
                    EU = U;
                }
            }
        }
    }
}

/* ---------------- greedy endpoint growth ---------------- */

/* Random wiring of one new vertex pair x (side 0), y (side 1) onto best (fallback). */
static void wire_pair(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

static int bq_dist[MAXN], bq_queue[MAXN], bq_mark[MAXN];
static int bq_stamp = 0;

/* Number of vertices within distance D of src (src included). */
static int ball_size(const Graph *g, int src) {
    int head = 0, tail = 0;
    bq_stamp++;
    bq_mark[src] = bq_stamp;
    bq_dist[src] = 0;
    bq_queue[tail++] = src;
    while (head < tail) {
        int v = bq_queue[head++];
        if (bq_dist[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (bq_mark[u] != bq_stamp) {
                bq_mark[u] = bq_stamp;
                bq_dist[u] = bq_dist[v] + 1;
                bq_queue[tail++] = u;
            }
        }
    }
    return tail;
}

/* Greedy endpoint-coverage wiring of the new pair x (side 0), y (side 1). */
static int wire_greedy(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0; k < d - 1; k++) {
        int ba = -1, bb = -1;
        long bscore = -1;
        int got = 0;
        for (int att = 0; got < GREEDY_CAND && att < 4000; att++) {
            int a = rndint(n);
            if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
            int b = work->adj[a][rndint(work->deg[a])];
            if (b >= n || used[b] == stamp) continue;
            got++;
            del_edge(work, a, b);
            add_edge(work, x, b);
            add_edge(work, y, a);
            long score = (long)(work->n - ball_size(work, x)) +
                         (long)(work->n - ball_size(work, y)) +
                         (long)(work->n - ball_size(work, a)) +
                         (long)(work->n - ball_size(work, b));
            del_edge(work, x, b);
            del_edge(work, y, a);
            add_edge(work, a, b);
            if (bscore < 0 || score < bscore) { bscore = score; ba = a; bb = b; }
        }
        if (ba < 0) return 0;
        del_edge(work, ba, bb);
        add_edge(work, x, bb);
        add_edge(work, y, ba);
        used[ba] = used[bb] = stamp;
    }
    return 1;
}

/* Grow best by one vertex pair: pick the best of INIT_TRIALS wirings, then anneal. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    static Graph trial;
    long bestbad = -1;
    for (int t = 0; t < INIT_TRIALS; t++) {
        if (!wire_greedy(best, &trial)) wire_pair(best, &trial);
        long b = bad_pairs(&trial);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &trial);
        }
        if (bestbad == 0 || now() > until) break;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

/* ---------------- ruin and recreate ----------------
 * Remove a BFS ball holding k A-vertices and k B-vertices, refill the freed degree slots with
 * random new A-B edges, then regrow k+1 pairs. Kept only if valid and larger. */

static Graph rr_cur, rr_nxt;
static int rr_ball[MAXN], rr_mark[MAXN], rr_map[MAXN];
static unsigned char rr_rem[MAXN];

static void deficit_fill(Graph *g) {
    int n = g->n;
    if (n < 2) return;
    for (long it = 0; it < 40L * n; it++) {
        int a = rndint(n), b = rndint(n);
        if (g->side[a] != 0 || g->side[b] != 1) continue;
        if (g->deg[a] >= d || g->deg[b] >= d || has_edge(g, a, b)) continue;
        add_edge(g, a, b);
    }
}

static int ruin_recreate(const Graph *best, Graph *out, int k, double until) {
    int n = best->n;
    if (k < 1 || n < 2 * k + 4 || n > MAXN - 2) return 0;
    int v0 = rndint(n);
    for (int i = 0; i < n; i++) { rr_mark[i] = 0; rr_rem[i] = 0; }
    int head = 0, tail = 0;
    rr_mark[v0] = 1;
    rr_ball[tail++] = v0;
    while (head < tail && tail < 6 * k + 6) {
        int v = rr_ball[head++];
        for (int i = 0; i < best->deg[v]; i++) {
            int u = best->adj[v][i];
            if (!rr_mark[u]) { rr_mark[u] = 1; rr_ball[tail++] = u; }
        }
    }
    int ra = 0, rb = 0;
    for (int i = 0; i < tail; i++) {
        int v = rr_ball[i];
        if (best->side[v] == 0) {
            if (ra < k) { rr_rem[v] = 1; ra++; }
        } else if (rb < k) {
            rr_rem[v] = 1;
            rb++;
        }
    }
    if (ra < k || rb < k) return 0;

    int m = 0;
    for (int v = 0; v < n; v++) rr_map[v] = rr_rem[v] ? -1 : m++;
    out->n = m;
    for (int v = 0; v < n; v++) {
        if (rr_map[v] < 0) continue;
        out->deg[rr_map[v]] = 0;
        out->side[rr_map[v]] = best->side[v];
    }
    for (int v = 0; v < n; v++) {
        if (rr_map[v] < 0) continue;
        for (int i = 0; i < best->deg[v]; i++) {
            int u = best->adj[v][i];
            if (u > v && rr_map[u] >= 0) add_edge(out, rr_map[v], rr_map[u]);
        }
    }
    deficit_fill(out);

    copy_graph(&rr_cur, out);
    for (int s = 0; s <= k; s++) {
        if (now() > until) return 0;
        if (rr_cur.n + 2 > moore_bound() || rr_cur.n + 2 > MAXN) return 0;
        if (!grow_once(&rr_cur, &rr_nxt, until)) return 0;
        copy_graph(&rr_cur, &rr_nxt);
    }
    copy_graph(out, &rr_cur);
    return is_valid(out);
}

static void grow_search(Graph *best, double until) {
    static Graph work, rr;
    int fails = 0;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) {
            copy_graph(best, &work);
            fails = 0;
            continue;
        }
        fails++;
        if (fails % 2 == 0 && now() < until) {
            int k = 2 + rndint(3);
            double rslice = now() + slice;
            if (rslice > until) rslice = until;
            if (ruin_recreate(best, &rr, k, rslice) && rr.n > best->n) copy_graph(best, &rr);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double L = t_end - t0;
    if (D >= 2 && best.n < moore_bound()) {
        double bc_until = best.n >= 1500 ? t0 + L * 0.97 : t0 + L * 0.88;
        if (d >= 3) bicayley_search(&best, bc_until);
        if (best.n < moore_bound()) grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
