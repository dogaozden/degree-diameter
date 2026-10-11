"""Arc-extended projective planes, saturated with spare degree, then grown by C.

New in this version: C runs a fixed-core annealing extension. The PG(2,q) core
edges (and any other core-core edge) are never touched. Each round adds two
extension vertices (one per side) and anneals only the edges that touch extension
vertices, minimising the number of pairs at distance > D. Python also saturates
the extension vertices with spare degree before handing the graph to C.
"""
import random
import time

import lib

C_SOURCE = r'''
/* Fixed-core extension annealing for bipartite degree-diameter graphs.
 *
 * Usage:   prog d D seed time_limit [core_m]   < start_graph
 *   core_m: the first 2*core_m vertices form a fixed core (their mutual edges are
 *           never changed). Vertices >= 2*core_m are extension vertices.
 *   core_m = 0 means no fixed core (every vertex may change).
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Each round appends one vertex per side, then anneals on the number of bad pairs
 * (pairs at distance > D). Moves add an edge between an extension vertex and an
 * opposite-side vertex, removing an edge if a degree cap would be exceeded. Every
 * removed edge has at least one extension endpoint, so core-core edges are safe.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int u, v, added; } Op;

static int d, D, core_n;
static double t_end;
static Op ops[64];
static int nops;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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

/* ------------------------------------------------------------------ distance check */

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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

/* ------------------------------------------------------------------ edit log */

static void log_add(Graph *g, int u, int v) {
    add_edge(g, u, v);
    ops[nops].u = u; ops[nops].v = v; ops[nops].added = 1;
    nops++;
}

static void log_del(Graph *g, int u, int v) {
    del_edge(g, u, v);
    ops[nops].u = u; ops[nops].v = v; ops[nops].added = 0;
    nops++;
}

static void undo(Graph *g) {
    while (nops > 0) {
        Op o = ops[--nops];
        if (o.added) del_edge(g, o.u, o.v);
        else add_edge(g, o.u, o.v);
    }
}

/* One random move touching extension vertices only.
 * Adds edge v-w (v extension, w opposite side). If v is full, drops one of v's
 * edges. If w is full, drops one of w's edges that has an extension endpoint.
 * Returns 1 if a move was applied (log in ops), 0 otherwise (graph unchanged). */
static int propose(Graph *g) {
    int ext = g->n - core_n;
    if (ext < 2) return 0;
    nops = 0;
    int v = (rnd01() < 0.5) ? g->n - 2 + rndint(2) : core_n + rndint(ext);
    int w = rndint(g->n);
    if (w == v || g->side[w] == g->side[v] || has_edge(g, v, w)) return 0;
    if (g->deg[v] >= d) {
        int u = g->adj[v][rndint(g->deg[v])];
        log_del(g, v, u);
    }
    if (g->deg[w] >= d) {
        int cand[MAXD], c = 0;
        for (int i = 0; i < g->deg[w]; i++) {
            int z = g->adj[w][i];
            if (w >= core_n || z >= core_n) cand[c++] = z;
        }
        if (c == 0) { undo(g); return 0; }
        log_del(g, w, cand[rndint(c)]);
    }
    log_add(g, v, w);
    return 1;
}

/* Simulated annealing on the bad-pair count. Returns 1 if the graph became valid. */
static int anneal(Graph *g, double until) {
    long cur = bad_pairs(g);
    double start = now();
    double span = until - start;
    if (span <= 0) return cur == 0;
    const double T0 = 4.0, T1 = 0.3;
    while (cur > 0) {
        double tn = now();
        if (tn >= until) break;
        double frac = (tn - start) / span;
        double T = T0 * pow(T1 / T0, frac);
        if (!propose(g)) continue;
        long nb = bad_pairs(g);
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
        else undo(g);
        nops = 0;
    }
    nops = 0;
    return cur == 0;
}

/* Repeatedly append a pair of extension vertices and anneal until valid. */
static void ext_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        int ok = 0;
        while (!ok && now() < until) {
            double left = until - now();
            double slice = left * 0.5 > 3.0 ? left * 0.5 : left;
            copy_graph(&work, best);
            int x = work.n, y = work.n + 1;
            work.n += 2;
            work.deg[x] = work.deg[y] = 0;
            work.side[x] = 0;
            work.side[y] = 1;
            ok = anneal(&work, now() + slice);
        }
        if (!ok) return;
        copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [core_m] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int core_m = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    core_n = 2 * core_m;
    if (core_n > best.n) core_n = 0;

    if (D >= 2 && best.n + 2 <= moore_bound()) ext_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _pg_data(q):
    """Points/lines of PG(2, q): point i and line i share the vector pts[i]."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG(2,q) incidence plus, per element P of S, a new A-vertex on the lines through P
    and a new B-vertex on the points of line P. Diameter 3, max degree q+1+s."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """(n, edges, core_m) candidates from arc-extended projective planes, for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n, E = _arc_graph(m, edges, point_lines, line_points, S)
        out.append((n, E, m))
    return out


def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of a bipartite graph on 0..n-1."""
    adj = lib.adjacency(n, edges)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _saturate(n, edges, d, ext_from, seed):
    """Greedily add edges between deficient opposite-colour vertices, touching at least one
    vertex >= ext_from. Adding edges keeps bipartiteness, degree <= d and diameter <= D."""
    col = _two_color(n, edges)
    E = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    pairs = [(a, b) for a in range(n) if col[a] == 0 and deg[a] < d
             for b in range(n) if col[b] == 1 and deg[b] < d and max(a, b) >= ext_from]
    random.Random(seed + 17).shuffle(pairs)
    for a, b in pairs:
        key = (min(a, b), max(a, b))
        if deg[a] < d and deg[b] < d and key not in E:
            E.add(key)
            deg[a] += 1
            deg[b] += 1
    return n, sorted(E)


def known_start(d, D):
    """Best closed-form graph for (d, D) as (n, edges, core_m), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        n, E = lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
        return n, E, n // 2
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        n, E = lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
        return n, E, 0
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    n0, E0 = lib.haar_graph(d, range(d))
    best = (n0, E0, 0)   # (n, edges, core_m)

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        cands = sorted(_arc_candidates(d, t0 + 0.15 * time_limit, rng), key=lambda t: -t[0])
        for n, E, m in cands[:3]:
            n2, E2 = _saturate(n, E, d, 2 * m, seed)
            consider((n2, E2, m))
            consider((n, E, m))

    # Hand the best construction to C, which anneals extension vertices into the graph.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[2]],
                             stdin_graph=(best[0], best[1]), timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e, best[2])
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        n0, E0 = lib.haar_graph(d, range(d))
        return n0, E0
    return best[0], best[1]
