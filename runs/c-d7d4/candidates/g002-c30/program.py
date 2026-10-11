"""Shrink-and-grow search for the bipartite degree-diameter problem.

Python: incidence-graph starts (PG(2,q), W(q), Araujo-Pardo-Lopez), grown by cover extension.
For D = 4 a new route: take W(q) with q >= d (too dense), strip edges down to max degree d,
and let C delete the worst vertices until the diameter is at most D.
C: (1) shrink an over-dense or invalid start to a valid graph by deleting the vertex with the
most bad pairs, (2) grow by two with simulated annealing over degree-preserving bipartite
2-switches, minimising the number of pairs farther apart than D.
Every candidate is validated with lib.is_valid, and the best valid graph is returned.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: shrink-then-grow with annealed 2-switches.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v". The graph must be bipartite with max degree <= d.
 *          It need not satisfy the diameter bound. "0 0" means no start.
 * stdout:  "n m" then m lines "u v" for the largest valid graph found.
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

static int d, D;
static double t_end;
static Graph best_g, work_g, cand_g, in_g;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static double T_cur = 0.5;

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph basics */

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

/* Delete vertex v; the last vertex is moved into slot v. */
static void remove_vertex(Graph *g, int v) {
    int L = g->n - 1;
    for (int i = 0; i < g->deg[v]; i++) del_half(g, g->adj[v][i], v);
    g->deg[v] = 0;
    if (v != L) {
        for (int i = 0; i < g->deg[L]; i++) {
            int u = g->adj[L][i];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == L) { g->adj[u][j] = v; break; }
        }
        g->deg[v] = g->deg[L];
        memcpy(g->adj[v], g->adj[L], sizeof(int) * g->deg[L]);
        g->side[v] = g->side[L];
    }
    g->n = L;
}

/* ------------------------------------------------------------ distance check */

/* Number of unordered pairs at distance > D. Also fills badv[v]. */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------ input / output */

/* Read "n m" + edges. Requires simple, bipartite, max degree <= d. Returns 1 on success. */
static int read_input(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 2 || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { g->n = 0; return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || has_edge(g, u, v) ||
            g->deg[u] >= d || g->deg[v] >= d) { g->n = 0; return 0; }
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
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return 0;
                }
            }
        }
    }
    return 1;
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
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= d); }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ shrink */

/* Repeatedly delete a vertex with the most bad pairs until the graph is valid. */
static void shrink_to_valid(Graph *g) {
    long bad = bad_pairs(g);
    while (bad > 0 && g->n > 2) {
        int bv = -1, mx = -1, cnt = 0;
        for (int v = 0; v < g->n; v++) {
            if (badv[v] > mx) {
                mx = badv[v];
                bv = v;
                cnt = 1;
            } else if (badv[v] == mx && mx > 0) {
                cnt++;
                if (rndint(cnt) == 0) bv = v;
            }
        }
        remove_vertex(g, bv);
        bad = bad_pairs(g);
    }
}

/* ------------------------------------------------------------ grow by two */

/* Copy b, add one vertex x on side 0 and y on side 1, then wire them with
 * direct edges to deficient vertices and degree-preserving swaps. */
static void grow_init(Graph *g, const Graph *b) {
    int n = b->n;
    copy_graph(g, b);
    g->n = n + 2;
    int x = n, y = n + 1;
    g->deg[x] = g->deg[y] = 0;
    g->side[x] = 0;
    g->side[y] = 1;
    add_edge(g, x, y);

    int tries = 0;
    while (g->deg[x] < d && tries < 20000) {
        tries++;
        int c = rndint(n);
        if (g->side[c] == 1 && g->deg[c] < d && !has_edge(g, x, c)) add_edge(g, x, c);
    }
    tries = 0;
    while (g->deg[y] < d && tries < 20000) {
        tries++;
        int c = rndint(n);
        if (g->side[c] == 0 && g->deg[c] < d && !has_edge(g, y, c)) add_edge(g, y, c);
    }
    tries = 0;
    while (g->deg[x] < d && g->deg[y] < d && tries < 200000) {
        tries++;
        int a = rndint(n);
        if (g->side[a] != 0 || g->deg[a] == 0) continue;
        int b2 = g->adj[a][rndint(g->deg[a])];
        if (b2 >= n || has_edge(g, x, b2) || has_edge(g, y, a)) continue;
        del_edge(g, a, b2);
        add_edge(g, x, b2);
        add_edge(g, y, a);
    }
}

/* Choose a 2-switch (a,b),(c,e) -> (a,e),(c,b) on side-0 vertices a,c. */
static int pick_swap(const Graph *g, int *pa, int *pb, int *pc, int *pe) {
    int n = g->n, a = -1, c = -1;
    for (int t = 0; t < 40; t++) {
        int v = rndint(n);
        if (g->side[v] != 0 || g->deg[v] == 0) continue;
        a = v;
        if (badv[v] > 0) break;
    }
    if (a < 0) return 0;
    for (int t = 0; t < 40; t++) {
        int v = rndint(n);
        if (v == a || g->side[v] != 0 || g->deg[v] == 0) continue;
        c = v;
        break;
    }
    if (c < 0) return 0;
    int b = g->adj[a][rndint(g->deg[a])];
    int e = g->adj[c][rndint(g->deg[c])];
    if (b == e || has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}

/* Anneal 2-switches to reduce bad pairs to zero. Returns 1 on success. */
static int anneal(Graph *g, double until) {
    long bad = bad_pairs(g);
    long it = 0;
    while (bad > 0) {
        if ((++it & 31) == 0 && now() > until) return 0;
        int a, b, c, e;
        if (!pick_swap(g, &a, &b, &c, &e)) continue;
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T_cur)) {
            bad = nb;
        } else {
            del_edge(g, a, e);
            del_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
        T_cur *= 0.9995;
        if (T_cur < 0.03) T_cur = 0.5;
    }
    return 1;
}

static void grow_loop(double until) {
    while (now() < until && best_g.n + 2 <= moore_bound() && best_g.n + 2 <= MAXN - 2) {
        double left = until - now();
        double slice = left < 3.0 ? left : (left * 0.5 > 3.0 ? left * 0.5 : 3.0);
        grow_init(&cand_g, &best_g);
        if (anneal(&cand_g, now() + slice) && is_valid(&cand_g))
            copy_graph(&best_g, &cand_g);
    }
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    int got = read_input(&in_g);
    if (got) {
        copy_graph(&best_g, &in_g);
        if (!is_valid(&best_g)) {
            copy_graph(&work_g, &in_g);
            shrink_to_valid(&work_g);
            if (work_g.n > 0 && is_valid(&work_g)) copy_graph(&best_g, &work_g);
            else best_g.n = 0;
        }
    } else {
        best_g.n = 0;
    }
    if (best_g.n == 0) complete_bipartite(&best_g);
    if (!is_valid(&best_g)) complete_bipartite(&best_g);

    if (best_g.n + 2 <= moore_bound()) grow_loop(t_end);

    print_graph(&best_g);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _gq_big(d):
    """W(q) with q >= d (degree above d, to be stripped), for the smallest prime power q >= d, q <= 8."""
    for q in range(max(d, 2), 9):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _strip_to_degree(n, edges, d, rng):
    """Remove edges (keeping bipartiteness) until every vertex has degree at most d."""
    edges = list(edges)
    rng.shuffle(edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    keep = set()
    for u, v in edges:
        if deg[u] > d and deg[v] > d:
            deg[u] -= 1
            deg[v] -= 1
        else:
            keep.add((min(u, v), max(u, v)))
    nbr = [set() for _ in range(n)]
    for u, v in keep:
        nbr[u].add(v)
        nbr[v].add(u)
    for v in range(n):
        while len(nbr[v]) > d:
            u = next(iter(nbr[v]))
            nbr[v].discard(u)
            nbr[u].discard(v)
            keep.discard((min(u, v), max(u, v)))
    return n, sorted(keep)


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidates; randomized restarts explore covers."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within radius D-1 (keeps diameter D)."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Cover-extend, then saturate with spare degree, repeated while it keeps growing."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def known_start(d, D):
    """Best directly constructed graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = 0.85 * time_limit - 1.0   # margin for compile, process start and output
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    def left():
        return budget - (time.monotonic() - t0)

    rng = random.Random(seed)
    cands = []
    ks = known_start(d, D)
    if ks is not None:
        cands.append(ks)
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            cands.append(pg)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            cands.append(gq)
    for g in cands:
        consider(g)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Python growth of the largest non-Moore start, kept short.
    grow_deadline = t0 + 0.12 * budget
    cands.sort(key=lambda g: -g[0])
    for g in cands[:2]:
        if time.monotonic() >= grow_deadline:
            break
        if g[0] >= moore:
            continue
        n2, e2 = _grow(g[0], g[1], d, D, grow_deadline, rng)
        consider((n2, e2))

    def run_engine(start, arg_budget):
        if arg_budget <= 1.0:
            return
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(arg_budget, 2)],
                             stdin_graph=start, timeout=arg_budget + 8)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass

    # Bold route for D = 4: shrink a denser generalized quadrangle to degree d, then grow.
    if D == 4 and left() > 4.0:
        big = _gq_big(d)
        if big is not None:
            stripped = _strip_to_degree(big[0], big[1], d, rng)
            run_engine(stripped, 0.55 * left())

    # Continue the search from the best valid graph found so far.
    if best[0] < moore and left() > 2.0:
        run_engine(best, left() - 1.0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
