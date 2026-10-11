"""Combined program: Python builds the best known start graph (Araujo-Pardo and Lopez record,
projective plane, GQ W(q) for D >= 4), and the C engine grows it by two vertices at a time.

New in this version: ruin-and-recreate. A frontier can start from the best graph with two random
vertices deleted (their former neighbours get spare degree), then two new vertex pairs are
reinserted greedily. Repair runs on that frontier as usual, so the search can leave the local
basin of the record graph instead of only adding pairs. Ruin frontiers are cycled with greedy and
random insertion (fails % 3), so each failed frontier tries a different kind of move.

Other parts: targeted and random annealed swaps, best-of-k swaps when few bad pairs remain,
monotone greedy chords and spare-degree fill. Every C step respects a hard deadline.

build() always returns a graph that passes lib.is_valid, so a failure in C only costs time.
"""
import itertools
import time

import lib

GQ_Q_MAX = 7      # largest q for which W(q) is built in Python (D >= 4 only)
TIME_FRAC = 0.93  # fraction of time_limit covered by the C run plus its compile

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search (grow by two, from the start graph or from K_{d,d}):
 *   - A new vertex pair is inserted randomly, greedily, or by ruin-and-recreate
 *     (delete two random vertices, reinsert two pairs greedily).
 *   - Repair by annealed degree-preserving swaps (two thirds targeted at unreached
 *     partners), plus best-of-k swaps when few bad pairs remain.
 *   - The unfinished repair is a frontier that persists across time slices.
 *   - Spare degree is filled by monotone greedy chords (added edges never raise distances).
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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static double chord_deadline = 1e18; /* hard limit for polishing loops */

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

/* Delete vertex v and compact labels: the last vertex takes label v.
 * Neighbours of v lose their edge to v, so they gain spare degree. */
static void remove_vertex(Graph *g, int v) {
    for (int i = 0; i < g->deg[v]; i++) del_half(g, g->adj[v][i], v);
    int last = g->n - 1;
    if (v != last) {
        g->deg[v] = g->deg[last];
        g->side[v] = g->side[last];
        memcpy(g->adj[v], g->adj[last], sizeof(int) * g->deg[last]);
        for (int i = 0; i < g->deg[v]; i++) {
            int w = g->adj[v][i];
            for (int j = 0; j < g->deg[w]; j++)
                if (g->adj[w][j] == last) g->adj[w][j] = v;
        }
    }
    g->deg[last] = 0;
    g->n--;
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
/* Reach balls of the most recent bad_pairs call: bit w of ball v is set iff dist(v,w) <= D. */
static uint64_t *final_reach = RA;
static int final_W = 0;

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
    final_reach = cur;
    final_W = W;
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

/* ------------------------------------------------------------------ swaps */

/* Propose a degree-preserving swap (v,u),(s,t) -> (v,t),(s,u) with side(t) != side(v) and
 * side(s) == side(v). Random mode picks s uniformly. Targeted mode picks an unreached partner
 * w of v and walks from w to t: one step if w is on v's side, two steps otherwise.
 * Targeted mode reads final_reach, so the state must match the last bad_pairs call. */
static int propose(const Graph *g, int v, int *pu, int *ps, int *pt, int targeted) {
    int n = g->n;
    int u, s, t;
    if (g->deg[v] == 0) return 0;
    u = g->adj[v][rndint(g->deg[v])];
    if (!targeted) {
        s = rndint(n);
        if (g->side[s] != g->side[v] || g->deg[s] == 0) return 0;
        t = g->adj[s][rndint(g->deg[s])];
    } else {
        int w = -1;
        for (int tries = 0; tries < 64; tries++) {
            int c = rndint(n);
            if (c != v && !((final_reach[(size_t)v * final_W + c / 64] >> (c % 64)) & 1ULL)) { w = c; break; }
        }
        if (w < 0) return 0;
        int L = g->side[w] == g->side[v] ? 1 : 2;
        t = w;
        for (int k = 0; k < L; k++) {
            if (g->deg[t] == 0) return 0;
            t = g->adj[t][rndint(g->deg[t])];
        }
        if (g->deg[t] == 0) return 0;
        s = g->adj[t][rndint(g->deg[t])];
    }
    if (s == v || t == u || g->side[t] == g->side[v] || g->side[s] != g->side[v]) return 0;
    if (has_edge(g, v, t) || has_edge(g, s, u)) return 0;
    *pu = u; *ps = s; *pt = t;
    return 1;
}

/* Apply the swap, keep or revert by the annealing rule. Returns the bad-pair count of the
 * kept state; reach balls and badv refer to that state on return. */
static long apply_swap(Graph *work, int v, int u, int s, int t, long bad, double T) {
    del_edge(work, v, u);
    del_edge(work, s, t);
    add_edge(work, v, t);
    add_edge(work, s, u);
    long nb = bad_pairs(work);
    if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) return nb;
    del_edge(work, v, t);
    del_edge(work, s, u);
    add_edge(work, v, u);
    add_edge(work, s, t);
    bad_pairs(work);
    return bad;
}

/* Best-of-k repair step: collect k targeted proposals, evaluate each exactly, then anneal in
 * the best one. Used when few bad pairs remain. */
static long best_of_k(Graph *work, long bad, int k, double T) {
    int PV[16], PU[16], PS[16], PT[16];
    int np = 0;
    if (k > 16) k = 16;
    for (int c = 0; c < k; c++) {
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        int u, s, t;
        if (!propose(work, v, &u, &s, &t, 1)) continue;
        PV[np] = v; PU[np] = u; PS[np] = s; PT[np] = t; np++;
    }
    long bn = -1;
    int bi = -1;
    for (int i = 0; i < np; i++) {
        int v = PV[i], u = PU[i], s = PS[i], t = PT[i];
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        del_edge(work, v, t);
        del_edge(work, s, u);
        add_edge(work, v, u);
        add_edge(work, s, t);
        if (bn < 0 || nb < bn) { bn = nb; bi = i; }
    }
    if (bi >= 0 && (bn <= bad || rnd01() < exp((double)(bad - bn) / T))) {
        int v = PV[bi], u = PU[bi], s = PS[bi], t = PT[bi];
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
    }
    return bad_pairs(work);
}

/* Spare-degree fill: add any cross-side edge whose endpoints both have spare degree.
 * Never increases a distance. */
static int fill_slack(Graph *g) {
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            added++;
        }
    }
    return added;
}

/* Greedy chords: repeatedly add the sampled cross-side edge between spare-degree vertices that
 * most reduces the exact bad-pair count, kept only if it strictly helps. Monotone. */
static int greedy_chord(Graph *g, int samples) {
    static int A[MAXN], B[MAXN];
    int added = 0;
    for (;;) {
        if (now() > chord_deadline) break;
        int na = 0, nb = 0;
        for (int v = 0; v < g->n; v++) {
            if (g->deg[v] >= d) continue;
            if (g->side[v] == 0) A[na++] = v;
            else B[nb++] = v;
        }
        if (na == 0 || nb == 0) break;
        long base = bad_pairs(g);
        if (base == 0) break;
        long bestv = -1;
        int ba = -1, bb = -1;
        for (int c = 0; c < samples; c++) {
            int a = A[rndint(na)], b = B[rndint(nb)];
            if (has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            long nbp = bad_pairs(g);
            del_edge(g, a, b);
            if (bestv < 0 || nbp < bestv) { bestv = nbp; ba = a; bb = b; }
        }
        if (ba < 0 || bestv >= base) break;
        add_edge(g, ba, bb);
        added++;
    }
    bad_pairs(g);
    return added;
}

/* ------------------------------------------------------------------ insertion moves */

/* Copy best into dst and add one vertex per side (x on side 0, y on side 1, joined),
 * rewiring d-1 random edges: x takes one neighbour b of a random side-0 vertex a, y takes a. */
static void insert_pair(const Graph *best, Graph *dst) {
    int n = best->n;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (dst->side[a] != 0 || used[a] == stamp || dst->deg[a] == 0) continue;
        int b = dst->adj[a][rndint(dst->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(dst, a, b);
        add_edge(dst, x, b);
        add_edge(dst, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

/* Greedy-rewire insertion: each of the d-1 rewires is the sampled candidate that leaves the
 * fewest bad pairs. Spare degree is then filled by greedy chords and a plain fill. */
static long insert_pair_greedy(const Graph *best, Graph *dst, int cand) {
    int n = best->n;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0; k < d - 1; k++) {
        int ba = -1, bb = -1;
        long bestbad = -1;
        for (int c = 0; c < cand; c++) {
            int a = rndint(n);
            if (dst->side[a] != 0 || used[a] == stamp || dst->deg[a] == 0) continue;
            int b = dst->adj[a][rndint(dst->deg[a])];
            if (b >= n || used[b] == stamp) continue;
            del_edge(dst, a, b);
            add_edge(dst, x, b);
            add_edge(dst, y, a);
            long nb = bad_pairs(dst);
            del_edge(dst, x, b);
            del_edge(dst, y, a);
            add_edge(dst, a, b);
            if (bestbad < 0 || nb < bestbad) { bestbad = nb; ba = a; bb = b; }
        }
        if (ba < 0) break;
        del_edge(dst, ba, bb);
        add_edge(dst, x, bb);
        add_edge(dst, y, ba);
        used[ba] = used[bb] = stamp;
    }
    greedy_chord(dst, 40);
    fill_slack(dst);
    return bad_pairs(dst);
}

/* NEW: ruin-and-recreate. Delete two random vertices from best (their former neighbours get
 * spare degree), then reinsert two vertex pairs greedily. The result has best->n + 2 vertices
 * and may have bad pairs; the frontier annealer repairs it. This moves the search away from
 * the record's local basin, which pure pair insertion cannot do. */
static void ruin_recreate(const Graph *best, Graph *dst) {
    static Graph tmp;
    copy_graph(dst, best);
    int a = rndint(dst->n);
    remove_vertex(dst, a);
    int b = rndint(dst->n);
    remove_vertex(dst, b);
    copy_graph(&tmp, dst);
    insert_pair_greedy(&tmp, dst, 30);   /* n-2 -> n */
    copy_graph(&tmp, dst);
    insert_pair_greedy(&tmp, dst, 30);   /* n -> n+2 */
}

/* ------------------------------------------------------------------ grow by two */

/* Frontier: a graph with best->n + 2 vertices whose repair may be unfinished. It persists
 * across time slices and is reset after repeated failed slices or after success. */
static int have_frontier = 0;
static Graph frontier;
static double frontier_T = 1.0;

/* Anneal on work until it has no bad pairs (returns 0) or the deadline passes (returns the
 * current, possibly positive, bad count). The state stays consistent. */
static long anneal_frontier(Graph *work, double until) {
    long bad = bad_pairs(work);
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return bad;
        if (bad <= 4 && rndint(2) == 0) {
            bad = best_of_k(work, bad, 8, frontier_T);
        } else {
            int v = rndint(work->n);
            for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
            int u, s, t;
            int targeted = rndint(3) != 0; /* two thirds of proposals are targeted */
            if (!propose(work, v, &u, &s, &t, targeted)) continue;
            bad = apply_swap(work, v, u, s, t, bad, frontier_T);
        }
        frontier_T *= 0.9995;
        if (frontier_T < 0.05) frontier_T = 1.0;
    }
    return 0;
}

static void grow_search(Graph *best, double until) {
    int fails = 0;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        if (!have_frontier) {
            /* Cycle the three move types: greedy insert, random insert, ruin-and-recreate. */
            int mode = fails % 3;
            if (mode == 0) insert_pair_greedy(best, &frontier, 40);
            else if (mode == 1) { insert_pair(best, &frontier); greedy_chord(&frontier, 40); fill_slack(&frontier); }
            else ruin_recreate(best, &frontier);
            have_frontier = 1;
            frontier_T = 1.0;
        }
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 2 > 4.0 ? left / 2 : 4.0);
        long bad = anneal_frontier(&frontier, now() + slice);
        if (bad == 0 && is_valid(&frontier)) {
            copy_graph(best, &frontier);
            have_frontier = 0;
            fails = 0;
        } else if (++fails >= 3) {
            have_frontier = 0;   /* diversify: restart from best with the next move type */
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
    t_end = t0 + limit * 0.96;
    chord_deadline = t0 + limit * 0.975;   /* polishing never runs past this */
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;
    if (!had_start) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound() && best.n + 2 <= MAXN)
        grow_search(&best, t_end);

    if (!is_valid(&best)) complete_bipartite(&best);

    /* Final monotone polish: greedy chords, then any cross-side edges spare degree allows. */
    static Graph tmp;
    copy_graph(&tmp, &best);
    greedy_chord(&tmp, 200);
    fill_slack(&tmp);
    if (is_valid(&tmp)) copy_graph(&best, &tmp);

    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best known construction Python builds directly for (d, D), or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)       # Moore graph, optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                return lib.araujo_lopez_graph(d - 2)           # record 2(q^2+q+5), q = d-2
            except ValueError:
                return None
        return None
    if D >= 4:
        return _best_gq(d)
    return None


def _finish(cands, d, D):
    """Largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]           # K_{d,d}: always valid

    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    if start is not None:
        cands.append(start)
    elif d >= 3 and D == 3:
        try:
            base = _pg_base(d)
            if base is not None:
                cands.append(base)
        except Exception:
            pass

    best = _finish(cands, d, D)

    # Moore-extremal start: nothing to search for.
    if start is not None and start[0] >= lib.moore_bound(d, D):
        return best

    # Reserve ~3 s for the C compile (not covered by the run timeout) and Python overhead.
    budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 3.0
    if budget > 1.0:
        stdin_graph = best if best[0] > 2 * d else None
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=stdin_graph, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass                                    # keep the valid Python fallback
    return best
