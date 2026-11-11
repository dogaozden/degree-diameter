"""Starter program with a new search core: random bipartite regular graphs at a target order, repaired by annealed edge swaps, climbing a ladder of orders.

Most improvements belong in C_SOURCE (it runs 10-100x faster than Python).
build() keeps the best valid graph it has, so a broken idea in C can only cost time.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * New in this version: random-regular repair ladder.
 *   1. For a target order N = 2M, build a random simple d-regular bipartite graph
 *      (stub pairing, then degree-preserving endpoint swaps that remove multi-edges).
 *   2. Anneal degree-preserving bipartite edge swaps, aimed at vertices that are too far
 *      from something, until every pair is within distance D or the attempt slice ends.
 *   3. Climb: on success, raise the target order by a fraction f of the current order;
 *      on failure, shrink f. The best valid graph is always kept.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12000
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)
#define MAXE ((MAXN / 2) * MAXD)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A (vertices 0..n/2-1 of a lift), 1 = part B */
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

static int count_edge(const Graph *g, int u, int v) {
    int c = 0;
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) c++;
    return c;
}

/* Replace one occurrence of old by nw in the adjacency list of v. */
static void repl(Graph *g, int v, int old, int nw) {
    for (int i = 0; i < g->deg[v]; i++)
        if (g->adj[v][i] == old) { g->adj[v][i] = nw; return; }
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

/* Number of unordered pairs at distance > D (0 means connected with diameter <= D). */
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

/* ------------------------------------------------------------------ input / output */

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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ random regular bipartite */

static int ea[MAXE], eb[MAXE], bst[MAXE], dupk[MAXE];

/* Random simple d-regular bipartite graph with sides 0..M-1 and M..2M-1.
 * Stub pairing first; then each duplicate edge (a,b) is fixed by a random degree-preserving
 * swap with another edge (a2,b2) -> (a,b2),(a2,b), accepted only if both new edges are absent.
 * Returns 1 on success. */
static int random_regular(Graph *g, int M) {
    if (M < d || 2 * M > MAXN || M * d > MAXE) return 0;
    int N = 2 * M, E = M * d;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= M; }
    for (int k = 0; k < E; k++) { ea[k] = k / d; bst[k] = M + k / d; }
    for (int k = E - 1; k > 0; k--) {
        int j = rndint(k + 1);
        int s = bst[k]; bst[k] = bst[j]; bst[j] = s;
    }
    for (int k = 0; k < E; k++) { eb[k] = bst[k]; add_edge(g, ea[k], eb[k]); }
    for (int round = 0; round < 300; round++) {
        int nd = 0;
        for (int k = 0; k < E; k++)
            if (count_edge(g, ea[k], eb[k]) > 1) dupk[nd++] = k;
        if (nd == 0) return 1;
        for (int it = 0; it < 100 * nd + 200; it++) {
            int k = dupk[rndint(nd)];
            if (count_edge(g, ea[k], eb[k]) < 2) continue;
            int l = rndint(E);
            int a = ea[k], b = eb[k], c = ea[l], e = eb[l];
            if (a == c || b == e) continue;
            if (count_edge(g, a, e) || count_edge(g, c, b)) continue;
            repl(g, a, b, e);
            repl(g, b, a, c);
            repl(g, c, e, b);
            repl(g, e, c, a);
            ea[k] = a; eb[k] = e;
            ea[l] = c; eb[l] = b;
        }
    }
    return 0;
}

/* ------------------------------------------------------------------ annealing */

static int badcur[MAXN]; /* badv of the currently accepted state */

/* Degree-preserving bipartite swaps that reduce the number of bad pairs.
 * A move removes (v,u) and (s,t), adds (v,t) and (s,u), where v and s lie on the same side.
 * Returns 0 if every pair became within distance D; otherwise the bad count at the deadline. */
static long anneal(Graph *g, double until, double T0) {
    long bad = bad_pairs(g);
    memcpy(badcur, badv, sizeof(int) * g->n);
    int M = g->n / 2;
    double T = T0;
    while (bad > 0) {
        if (now() > until) return bad;
        int v = rndint(g->n);
        for (int t = 0; t < 40 && badcur[v] == 0; t++) v = rndint(g->n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int s = g->side[v] ? M + rndint(M) : rndint(M);
        if (s == v || g->deg[s] == 0) continue;
        int t = g->adj[s][rndint(g->deg[s])];
        if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) continue;
        del_edge(g, v, u);
        del_edge(g, s, t);
        add_edge(g, v, t);
        add_edge(g, s, u);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            memcpy(badcur, badv, sizeof(int) * g->n);
        } else {
            del_edge(g, v, t);
            del_edge(g, s, u);
            add_edge(g, v, u);
            add_edge(g, s, t);
        }
        T *= 0.9995;
        if (T < 0.1) T = T0;
    }
    return 0;
}

/* ------------------------------------------------------------------ ladder over orders */

static void ladder(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    double f = 1.0 / 16;
    while (now() < until) {
        long lo = best->n;
        if (lo + 2 > moore || lo + 2 > MAXN) return;
        long step = (long)(lo * f);
        step += step & 1;
        if (step < 2) step = 2;
        long N = lo + step;
        if (N > moore || N > MAXN) N = lo + 2;
        int M = (int)(N / 2);

        double left = until - now();
        double cap = left * 0.3;
        if (cap > 12.0) cap = 12.0;
        if (cap < 1.0) cap = left;
        double dl = now() + cap;
        if (dl > until) dl = until;

        if (!random_regular(&cand, M)) {
            f = f * 0.5 > 0.0005 ? f * 0.5 : 0.0005;
            continue;
        }
        long rest = anneal(&cand, dl, 1.0);
        if (rest == 0 && is_valid(&cand)) {
            copy_graph(best, &cand);
            f = f * 1.5 < 0.25 ? f * 1.5 : 0.25;
        } else {
            f = f * 0.5 > 0.0005 ? f * 0.5 : 0.0005;
        }
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
    t_end = t0 + limit * 0.93 - 0.5;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        best.n = 0;
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n < moore_bound()) ladder(&best, t_end);
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
    best = known_start(d, D)
    if best is None or not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))             # K_{d,d}: valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])                                 # trivial fallback

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
