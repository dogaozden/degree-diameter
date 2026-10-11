import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: validity-preserving random walk on valid bipartite graphs.
#
# Moves: (1) degree-preserving edge switch, (2) edge deletion, both kept only
# if the diameter stays <= D. After each move, grow by adding vertices whose
# neighbourhoods are covers (radius D-1 balls) of the whole graph, using the
# spare degree. Vertices are never removed, so the order never shrinks.
# The best graph is saturated with extra edges (which keeps validity) and printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4200
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)
#define RATT 4

typedef struct {
    int n;
    int deg[MAXN];
    int color[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static Graph G, PREV, BEST, OUT;
static int DIAM = 0, DEG = 0;
static uint64_t cov[MAXN][MAXW];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static uint64_t covered[MAXW];
static int candv[MAXN];
static int gainv[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double t_end = 0.0;

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static uint64_t last_mask(int n) {
    int r = n % 64;
    return r == 0 ? ~0ULL : ((1ULL << r) - 1ULL);
}

static int has_edge(const Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++)
        if (g->adj[a][i] == b) return 1;
    return 0;
}

static void add_edge_g(Graph *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}

static void repl(Graph *g, int u, int old, int nw) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == old) { g->adj[u][i] = nw; return; }
}

static void del_from(Graph *g, int u, int x) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == x) {
            g->adj[u][i] = g->adj[u][g->deg[u] - 1];
            g->deg[u]--;
            return;
        }
}

/* out[v] = bitset of vertices within distance `radius` of v. */
static void compute_balls(const Graph *g, int radius, uint64_t (*out)[MAXW], uint64_t (*tmp)[MAXW]) {
    int n = g->n;
    int w = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(out[v], 0, sizeof(uint64_t) * (size_t)w);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < radius; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(tmp[v], out[v], sizeof(uint64_t) * (size_t)w);
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *src = out[g->adj[v][i]];
                for (int k = 0; k < w; k++) tmp[v][k] |= src[k];
            }
        }
        for (int v = 0; v < n; v++)
            memcpy(out[v], tmp[v], sizeof(uint64_t) * (size_t)w);
    }
}

/* Full validity: degree <= DEG, proper bipartition, diameter <= DIAM, connected. */
static int full_ok(const Graph *g) {
    int n = g->n;
    if (n < 1) return 0;
    int w = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > DEG) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->color[u] == g->color[v]) return 0;
        }
    }
    compute_balls(g, DIAM, bufA, bufB);
    uint64_t lm = last_mask(n);
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w - 1; k++)
            if (bufA[v][k] != ~0ULL) return 0;
        if ((bufA[v][w - 1] & lm) != lm) return 0;
    }
    return 1;
}

static int is_covered(int n) {
    int w = (n + 63) / 64;
    for (int k = 0; k < w - 1; k++)
        if (covered[k] != ~0ULL) return 0;
    uint64_t lm = last_mask(n);
    return (covered[w - 1] & lm) == lm;
}

/* Find <= DEG vertices of colour != newc with spare degree whose cov balls cover all
   vertices. cov must be fresh for the current graph. Returns count, 0 on failure. */
static int try_cover(int newc, int randomize, int *S) {
    int n = G.n;
    int w = (n + 63) / 64;
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (G.color[v] != newc && G.deg[v] < DEG) candv[nc++] = v;
    for (int k = 0; k < w; k++) covered[k] = 0;
    int ns = 0;
    while (!is_covered(n)) {
        if (ns >= DEG || nc == 0) return 0;
        int best = 0;
        for (int i = 0; i < nc; i++) {
            const uint64_t *b = cov[candv[i]];
            int g = 0;
            for (int k = 0; k < w; k++) g += popc(b[k] & ~covered[k]);
            gainv[i] = g;
            if (g > best) best = g;
        }
        if (best == 0) return 0;
        int thr = best;
        if (randomize && best > 1 && rnd01() < 0.5) thr = best - 1;
        int pick = -1;
        if (randomize) {
            int opts = 0;
            for (int i = 0; i < nc; i++)
                if (gainv[i] >= thr && gainv[i] > 0) opts++;
            int r = rndint(opts);
            for (int i = 0; i < nc; i++)
                if (gainv[i] >= thr && gainv[i] > 0) {
                    if (r == 0) { pick = i; break; }
                    r--;
                }
        } else {
            for (int i = 0; i < nc; i++)
                if (gainv[i] == best) { pick = i; break; }
        }
        if (pick < 0) return 0;
        int s = candv[pick];
        S[ns++] = s;
        const uint64_t *b = cov[s];
        for (int k = 0; k < w; k++) covered[k] |= b[k];
        candv[pick] = candv[--nc];
        gainv[pick] = gainv[nc];
    }
    return ns;
}

static void add_vertex(int newc, const int *S, int k) {
    int x = G.n++;
    G.color[x] = newc;
    G.deg[x] = 0;
    for (int i = 0; i < k; i++) {
        int s = S[i];
        G.adj[s][G.deg[s]++] = x;
        G.adj[x][G.deg[x]++] = s;
    }
}

/* Try to add one vertex. Returns 1 if added. */
static int grow_once(void) {
    if (G.n >= MAXN - 2) return 0;
    compute_balls(&G, DIAM - 1, cov, bufB);
    int S[MAXD];
    for (int newc = 0; newc < 2; newc++) {
        for (int a = 0; a <= RATT; a++) {
            int k = try_cover(newc, a > 0, S);
            if (k > 0) {
                add_vertex(newc, S, k);
                return 1;
            }
        }
    }
    return 0;
}

static int rand_edge(int *x, int *y) {
    if (G.n < 2) return 0;
    for (int tries = 0; tries < 200; tries++) {
        int v = rndint(G.n);
        if (G.deg[v] == 0) continue;
        int u = G.adj[v][rndint(G.deg[v])];
        if (G.color[v] == 0) { *x = v; *y = u; }
        else { *x = u; *y = v; }
        return 1;
    }
    return 0;
}

/* Degree-preserving switch: (a,b),(c,d) -> (a,d),(c,b). a,c colour 0; b,d colour 1. */
static int do_switch(void) {
    int a, b, c, d;
    if (!rand_edge(&a, &b) || !rand_edge(&c, &d)) return 0;
    if (a == c || b == d) return 0;
    if (has_edge(&G, a, d) || has_edge(&G, c, b)) return 0;
    repl(&G, a, b, d);
    repl(&G, b, a, c);
    repl(&G, c, d, b);
    repl(&G, d, c, a);
    if (full_ok(&G)) return 1;
    repl(&G, a, d, b);
    repl(&G, b, c, a);
    repl(&G, c, b, d);
    repl(&G, d, a, c);
    return 0;
}

/* Delete a random edge if the graph stays valid (frees spare degree). */
static int do_delete(void) {
    int a, b;
    if (!rand_edge(&a, &b)) return 0;
    del_from(&G, a, b);
    del_from(&G, b, a);
    if (full_ok(&G)) return 1;
    add_edge_g(&G, a, b);
    return 0;
}

/* Add edges between spare-degree vertices on opposite sides (keeps validity). */
static void saturate(Graph *g) {
    static int L[MAXN], R[MAXN];
    for (int pass = 0; pass < 6; pass++) {
        int nl = 0, nr = 0;
        for (int v = 0; v < g->n; v++) {
            if (g->deg[v] >= DEG) continue;
            if (g->color[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
        if (nl == 0 || nr == 0) break;
        for (int i = nl - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = L[i]; L[i] = L[j]; L[j] = t;
        }
        for (int i = nr - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = R[i]; R[i] = R[j]; R[j] = t;
        }
        int added = 0;
        for (int i = 0; i < nl; i++) {
            int a = L[i];
            for (int j = 0; j < nr && g->deg[a] < DEG; j++) {
                int b = R[j];
                if (g->deg[b] >= DEG || has_edge(g, a, b)) continue;
                add_edge_g(g, a, b);
                added++;
            }
        }
        if (!added) break;
    }
}

static int colour_graph(Graph *g) {
    static int queue[MAXN];
    int n = g->n;
    for (int v = 0; v < n; v++) g->color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (g->color[s] != -1) continue;
        g->color[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < g->deg[u]; i++) {
                int v = g->adj[u][i];
                if (g->color[v] == -1) {
                    g->color[v] = 1 - g->color[u];
                    queue[qt++] = v;
                } else if (g->color[v] == g->color[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 2 || m < 0) return 0;
    G.n = n;
    for (int v = 0; v < n; v++) {
        G.deg[v] = 0;
        G.color[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (G.deg[u] >= DEG || G.deg[v] >= DEG) return 0;
        if (has_edge(&G, u, v)) return 0;
        add_edge_g(&G, u, v);
    }
    return colour_graph(&G);
}

static void print_graph(const Graph *g) {
    int m = 0;
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->adj[v][i] > v) m++;
    printf("%d %d\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->adj[v][i] > v) printf("%d %d\n", v, g->adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double t0 = now_sec();
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    DEG = d;
    t_end = t0 + budget * 0.95 - 0.2;
    if (DEG < 1 || DEG > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    if (!read_input() || !full_ok(&G)) {
        printf("0 0\n");
        return 0;
    }
    BEST = G;
    int best_n = G.n;
    while (now_sec() < t_end) {
        PREV = G;
        int ok = (rndint(100) < 70) ? do_switch() : do_delete();
        if (!ok) continue;
        int grew = 0;
        while (grow_once()) grew = 1;
        if (grew && !full_ok(&G)) {
            G = PREV;
            continue;
        }
        if (G.n > best_n) {
            BEST = G;
            best_n = G.n;
        }
    }
    OUT = BEST;
    saturate(&OUT);
    if (!full_ok(&OUT)) OUT = BEST;
    print_graph(&OUT);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: generalized quadrangle W(q) and projective plane starts,
# grown by cover-based vertex extension (no saturation, so spare degree stays
# available for the C engine).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedy set cover of `full` by at most d candidate vertices (randomized on retries)."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within radius D-1.

    Adding vertices never increases distances, so diameter and degree stay valid.
    Spare degree is deliberately NOT spent on edge saturation here.
    """
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
            for attempt in range(60):
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


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Base construction: PG(2,q) for D = 3, W(q) for D >= 4.
    base = None
    if D == 3:
        base = _best_pg(d)
    elif D >= 4:
        base = _best_gq(d)
    if base is not None:
        consider(base[0], base[1])
        # Python growth on the base; the spare degree left over is the C engine's resource.
        n1, e1 = _extend_cover(base[0], base[1], d, D, t0 + 0.35 * time_limit, rng)
        consider(n1, e1)

    # C engine: random walk on valid graphs (switches, deletions, cover growth).
    if D >= 2 and d <= 32 and best_n < lib.moore_bound(d, D):
        remaining = end - time.monotonic()
        if remaining > 1.0:
            budget = remaining - 0.5
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best[1]),
                                timeout=remaining + 0.05 * time_limit)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
