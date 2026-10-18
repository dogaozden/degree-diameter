"""Starter program: Python builds the best known start graph, the C engine searches from it.

This version replaces the grow-by-two annealing with a different construction: voltage lifts
of small base graphs over groups Z_m x| Z_k. A lift of a d-regular base with p vertices per side
over a group G is invariant under left multiplication by G. So the diameter check needs only 2p
BFS runs, one per base vertex, which makes each candidate check very cheap. The C engine
samples groups and base graphs, then anneals the voltages until the diameter is at most D.
Every accepted lift is re-checked with a full bitset validity test, and Python keeps a valid
fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: fast group-lift search.
 *
 * Usage:   prog d D seed time_limit [goal]   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * goal:    optional record order; the search aims at orders >= goal + 2 part of the time.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Construction: a base multigraph with p A-vertices and p B-vertices, d-regular, is lifted over
 * a group G of order N. Dart (i, j, g) joins A(i,x) to B(j, x*g) for all x in G. The lift has
 * 2pN vertices and is G-invariant under left multiplication, so the diameter is at most D iff
 * every BFS from the 2p representatives A(i,1), B(j,1) reaches everything within D steps.
 * Voltages are annealed to minimise the total number of unreached (source, vertex) pairs.
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
#define MAXP 4
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static long goal_n = 0;

/* ------------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* Number of unordered pairs at distance > D (0 means connected with diameter <= D). */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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
        total += n - c;
    }
    return total / 2;
}

/* Full validity check: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* Read "n m" + edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
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

/* K_{d,d}: valid for D >= 2 when d <= MAXD. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* K_2: valid for every d >= 1 and D >= 1. */
static void k2(Graph *g) {
    g->n = 2;
    g->deg[0] = g->deg[1] = 0;
    g->side[0] = 0;
    g->side[1] = 1;
    add_edge(g, 0, 1);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Inverse of (a, b) is (-r^(-b) a, -b). */
static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long v = (-(long)G->rp[nb] * a) % G->m;
    if (v < 0) v += G->m;
    return (int)v * G->k + nb;
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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
            if (rndint((int)count) == 0) { G->m = m; G->k = k; G->r = r; }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------------ base graph and darts */

typedef struct { int i, j, g, gi; } Dart; /* A-vertex i -> B-vertex j, voltage g, inverse gi */

static Dart dart[MAXDART];
static int nd;
static int adjA[MAXP][MAXD], adjB[MAXP][MAXD]; /* dart indices at each base vertex */
static int base_M[MAXP][MAXP];

/* Random d-regular bipartite base multigraph with p vertices per side (sum of d random
 * permutation matrices), retried until connected. */
static void make_base(int p) {
    for (;;) {
        memset(base_M, 0, sizeof base_M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) base_M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && base_M[v][u - p]) : (u < p && base_M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* A voltage not used by another dart between the same pair of base vertices. */
static int fresh_voltage(int t, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int s = 0; s < nd; s++)
            if (s != t && dart[s].i == dart[t].i && dart[s].j == dart[t].j && dart[s].g == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
}

/* Fresh random base graph and random voltages for group G of order N. */
static void setup_base(int p, const Grp *G, int N) {
    make_base(p);
    nd = 0;
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < base_M[i][j]; c++) {
                dart[nd].i = i;
                dart[nd].j = j;
                dart[nd].g = -1;
                dart[nd].gi = -1;
                adjA[i][ca[i]++] = nd;
                adjB[j][cb[j]++] = nd;
                nd++;
            }
    for (int t = 0; t < nd; t++) {
        int g = fresh_voltage(t, N);
        dart[t].g = g;
        dart[t].gi = ginv(G, g);
    }
}

/* ------------------------------------------------------------------ fast evaluation */

static int bf_vis[MAXN], bf_dist[MAXN], bf_q[MAXN];
static int bf_stamp = 0;

/* Total number of (source, vertex) pairs not reached within D steps, over the 2p
 * representative sources. Zero iff the lift has diameter <= D. */
static long eval_bad(const Grp *G, int p, int N) {
    int V = 2 * p * N, pn = p * N;
    long total = 0;
    for (int src = 0; src < 2 * p; src++) {
        int s = src * N; /* A(src,0) for src < p, B(src-p,0) = (src)*N otherwise */
        bf_stamp++;
        int head = 0, tail = 0;
        bf_vis[s] = bf_stamp;
        bf_dist[s] = 0;
        bf_q[tail++] = s;
        while (head < tail) {
            int v = bf_q[head++];
            int dv = bf_dist[v];
            if (dv >= D) continue;
            if (v < pn) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    const Dart *dt = &dart[adjA[i][k]];
                    int u = pn + dt->j * N + gmul(G, x, dt->g);
                    if (bf_vis[u] != bf_stamp) {
                        bf_vis[u] = bf_stamp;
                        bf_dist[u] = dv + 1;
                        bf_q[tail++] = u;
                    }
                }
            } else {
                int w = v - pn, j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    const Dart *dt = &dart[adjB[j][k]];
                    int u = dt->i * N + gmul(G, y, dt->gi);
                    if (bf_vis[u] != bf_stamp) {
                        bf_vis[u] = bf_stamp;
                        bf_dist[u] = dv + 1;
                        bf_q[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Simulated annealing over the voltages of the current base. Returns the final cost. */
static long anneal(const Grp *G, int p, int N, long steps) {
    long cur = eval_bad(G, p, N);
    double T = 2.0;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        int t = rndint(nd);
        int og = dart[t].g, ogi = dart[t].gi;
        int g = fresh_voltage(t, N);
        dart[t].g = g;
        dart[t].gi = ginv(G, g);
        long nb = eval_bad(G, p, N);
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
            cur = nb;
        } else {
            dart[t].g = og;
            dart[t].gi = ogi;
        }
        T *= 0.997;
        if (T < 0.1) T = 2.0;
    }
    return cur;
}

/* Materialise the current lift as an explicit graph. */
static void build_lift(Graph *g, const Grp *G, int p, int N) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dart[t].i * N + x, p * N + dart[t].j * N + gmul(G, x, dart[t].g));
}

/* ------------------------------------------------------------------ search loop */

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    int fails = 0;
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 17 ? 3 : 4;
        long lim = cap / (2 * p);       /* largest N with 2pN within both bounds */
        long lo = best->n / (2 * p) + 1; /* smallest N that beats the current best */
        if (goal_n > 0 && rndint(3) == 0) {
            long ng = (goal_n + 2 + 2 * p - 1) / (2 * p); /* aim just past the goal */
            if (ng > lo) lo = ng;
        }
        if (lo < d) lo = d;
        if (lo > lim) {
            if (++fails > 5000) return;
            continue;
        }
        long N = lo;
        if (rndint(2) == 0) N += rndint(1 + (int)(lo / 8));
        if (N > lim) N = lim;
        if (!random_group((int)N, &G)) continue;
        setup_base(p, &G, (int)N);
        long bad = anneal(&G, p, (int)N, 4000);
        if (bad == 0) {
            build_lift(&cand, &G, p, (int)N);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    goal_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { k2(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && d >= 2 && best.n < moore_bound()) lift_search(&best, t_end);

    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) k2(&best);
    print_graph(&best);
    return 0;
}
'''

# Known record orders, passed to the C engine as a search goal (it aims just past this).
RECORD_GOAL = {(3, 9): 506}


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
    if not lib.is_valid(*best, d, D):
        best = (2, [(0, 1)])
    if not lib.is_valid(*best, d, D):
        return best

    budget = min(0.75 * time_limit, time_limit - 12.0) - (time.monotonic() - t0)
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine
    if budget > 0.5:
        goal = RECORD_GOAL.get((d, D), 0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), goal],
                             stdin_graph=best, timeout=budget + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
