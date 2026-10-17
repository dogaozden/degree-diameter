"""Group-lift search with orbit-reduced distance checks.

New in this version: a lift of a bipartite base graph over a group G is invariant under
left translation by G, so the diameter condition only has to be checked from the 2p base
vertices at the identity. Each candidate is scored by the number of vertex pairs left
farther than D apart, and the voltages are annealed toward zero. This is much cheaper
than checking all pairs with bitsets.

Python builds the trivial K_{d,d} start (or the known Moore/record graph for D = 3) and
keeps the best valid graph it receives back from C.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core: group lifts with orbit-reduced evaluation.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Method:
 *   A lift of a d-regular bipartite base multigraph with p vertices per side over a group G
 *   (|G| = N) has vertices (side, base, g). Left multiplication by h in G is an automorphism
 *   of the lift, so the lift is vertex-transitive inside each fibre. Hence the diameter is
 *   at most D iff every one of the 2p base vertices at the identity reaches all 2pN vertices
 *   within D steps. Cost = total number of unreached (source, vertex) pairs over those 2p
 *   sources. The voltages are annealed until the cost is 0.
 *   Each evaluation is 2p breadth-first searches, roughly 10^3 times cheaper than a full
 *   bitset check. The search ratchets the order upward: each success requires a larger N.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXP 8
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

static int d, D;
static double t_end;

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
    if (D == 1) return 2L * d;
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

/* ------------------------------------------------------------------ full check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (0 means diameter <= D; disconnected pairs count). */
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

/* Full validity: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ input / output */

/* Read "n m" + edges from stdin and 2-colour it. Leaves g->n = 0 if absent or invalid. */
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

/* K_{d,d}: always valid for D >= 2 (and for D = 1). */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k).
 * Identity is index 0. */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
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
            if (rndint((int)(count < 1000000000L ? count : 1000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------------ base multigraph */

/* Random d-regular bipartite base multigraph on p + p vertices, as a sum of d random
 * permutation matrices, retried until connected. M[i][j] = number of darts i -> j. */
static int make_base(int p, int M[MAXP][MAXP]) {
    for (int tries = 0; tries < 2000; tries++) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ lifts */

/* Lift: dart t joins A(di[t], x) to B(dj[t], x * dg[t]) for all x in G.
 * A(i, x) has id i*N + x; B(j, y) has id p*N + j*N + y. */
static void build_lift(Graph *g, int p, int N, const Grp *G,
                       const int *di, const int *dj, const int *dg, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= p * N); }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, p * N + dj[t] * N + gmul(G, x, dg[t]));
}

/* A voltage not used by another dart between the same base pair (unassigned darts have dg = -1). */
static int fresh_voltage(const int *di, const int *dj, const int *dg, int nd, int t, int N) {
    for (int guard = 0;; guard++) {
        int g = rndint(N), clash = 0;
        for (int s = 0; s < nd; s++)
            if (s != t && dg[s] == g && di[s] == di[t] && dj[s] == dj[t]) { clash = 1; break; }
        if (!clash || guard > 100000) return g;
    }
}

/* Orbit-reduced cost: total number of vertices NOT within D steps of the 2p identity
 * vertices (one per base vertex). Zero iff the lift has diameter <= D. */
static long lift_cost(const Graph *g, int p, int N) {
    static int vis[MAXN], q[MAXN];
    static int stamp = 0;
    long cost = 0;
    int n = g->n;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N; /* identity of base vertex s (A for s < p, B otherwise) */
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        q[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int v = q[head++];
                for (int i = 0; i < g->deg[v]; i++) {
                    int u = g->adj[v][i];
                    if (vis[u] != stamp) { vis[u] = stamp; q[tail++] = u; }
                }
            }
        }
        cost += n - tail;
    }
    return cost;
}

/* Anneal the voltages of one random base graph over one group. Returns 1 if cost reaches 0;
 * then out holds that valid lift. */
static int lift_attempt(Graph *out, int p, int N, const Grp *G, long steps) {
    static int M[MAXP][MAXP];
    static int di[MAXDART], dj[MAXDART], dg[MAXDART];
    if (!make_base(p, M)) return 0;
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                di[nd] = i; dj[nd] = j; dg[nd] = -1;
                nd++;
            }
    for (int t = 0; t < nd; t++) dg[t] = fresh_voltage(di, dj, dg, nd, t, N);
    build_lift(out, p, N, G, di, dj, dg, nd);
    long cost = lift_cost(out, p, N);
    for (long s = 0; s < steps && cost > 0; s++) {
        if (now() > t_end) break;
        double T = 2.0 * pow(0.02, (double)s / (double)steps);
        int t = rndint(nd);
        int old = dg[t];
        dg[t] = fresh_voltage(di, dj, dg, nd, t, N);
        build_lift(out, p, N, G, di, dj, dg, nd);
        long c2 = lift_cost(out, p, N);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            dg[t] = old;
            build_lift(out, p, N, G, di, dj, dg, nd);
        }
    }
    return cost == 0;
}

/* Ratchet: keep trying lifts just above the current best order. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    long fails = 0;
    while (now() < until) {
        int r = rndint(12);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : r < 10 ? 4 : r < 11 ? 6 : 8;
        if (d < 3) p = 1;   /* a connected random base needs at least 3 darts per vertex */
        long target = best->n + 2;
        if (target > moore || target > MAXN) return;
        long Nmin = (target + 2L * p - 1) / (2L * p);
        if (Nmin < d) Nmin = d;
        long N = Nmin + (rndint(2) ? rndint(3) : 0);
        if (2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 100000) return;
            continue;
        }
        if (!random_group((int)N, &G)) continue;
        long steps = 6000 / p;
        if (!lift_attempt(&cand, p, (int)N, &G, steps)) continue;
        if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1) {
        printf("1 0\n");
        return 0;
    }
    if (d > MAXD) {
        printf("1 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n < moore_bound()) lift_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
