"""Combined diameter-3 (and general D) bipartite search.

Python builds the best valid start it can: the Araujo-Pardo-Lopez graph when it applies,
arc-extended projective planes (greedy arcs and conics), the generalized quadrangle for D >= 4,
or K_{d,d}. Every candidate is checked with lib.is_valid.

The C engine then grows the start in two ways:
  1. Grow by one: add a vertex on one side joined to a set T of spare vertices on the other side.
     T is chosen by randomized greedy cover until every existing vertex is within distance D-1 of T.
     This keeps all old distances valid and keeps the new vertex within distance D of everything.
  2. Grow by two: add an edge-linked pair of vertices, steal edges to fill them, then anneal
     degree-preserving swaps until the graph has diameter at most D.
Every accepted state is valid, and the C output is checked again in Python.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static Graph G, SNAP, ORIG;
static int d, D, W;
static double t_end;
static uint64_t ball[MAXN][MAXW];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static int bq[MAXN], lev[MAXN], mark[MAXN];
static int stampc = 0;
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
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
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

static void setW(void) { W = (G.n + 63) / 64; }

/* Bitset of vertices within distance r of src (uses current W). */
static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, tail = 0;
    stampc++;
    for (int w = 0; w < W; w++) bits[w] = 0;
    bq[tail++] = src;
    mark[src] = stampc;
    lev[src] = 0;
    while (head < tail) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < G.deg[u]; k++) {
            int v = G.adj[u][k];
            if (mark[v] != stampc) {
                mark[v] = stampc;
                lev[v] = lev[u] + 1;
                bq[tail++] = v;
            }
        }
    }
}

static void refresh(void) {
    setW();
    for (int v = 0; v < G.n; v++) ball_of(v, D - 1, ball[v]);
}

/* Total number of unordered pairs at distance > D; also sets badv[]. */
static long bad_pairs(void) {
    setW();
    int n = G.n;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < G.deg[v]; i++) {
                const uint64_t *s = cur + (size_t)G.adj[v][i] * W;
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
        for (int w = 0; w < W; w++) c += popc(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int graph_ok(void) {
    int n = G.n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (G.deg[v] > d) return 0;
        for (int i = 0; i < G.deg[v]; i++) {
            int u = G.adj[v][i];
            if (u < 0 || u >= n || u == v || G.side[u] == G.side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (G.adj[v][j] == u) return 0;
        }
    }
    return bad_pairs() == 0;
}

static int any_bits(const uint64_t *U) {
    for (int w = 0; w < W; w++)
        if (U[w]) return 1;
    return 0;
}

/* Add one vertex on side X joined to T (other side, spare degree), where T covers every
   vertex within distance D-1. Returns 1 if the graph grew. */
static int try_add_one(int X, int trials) {
    static int T[MAXD];
    static unsigned char chosen[MAXN];
    static uint64_t U[MAXW];
    int n = G.n;
    if (n + 1 > MAXN - 1) return 0;
    for (int tr = 0; tr < trials; tr++) {
        int nt = 0;
        setW();
        for (int w = 0; w < W; w++) U[w] = ~0ULL;
        if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
        while (nt < d && any_bits(U)) {
            int best = -1;
            double bs = -1.0;
            for (int v = 0; v < n; v++) {
                if (G.side[v] == X || G.deg[v] >= d || chosen[v]) continue;
                int g = 0;
                for (int w = 0; w < W; w++) g += popc(ball[v][w] & U[w]);
                if (g == 0) continue;
                double sc = (double)g + (tr > 0 ? 3.0 * rnd01() : 0.0);
                if (sc > bs) {
                    bs = sc;
                    best = v;
                }
            }
            if (best < 0) break;
            chosen[best] = 1;
            T[nt++] = best;
            for (int w = 0; w < W; w++) U[w] &= ~ball[best][w];
        }
        int ok = (!any_bits(U)) && nt > 0;
        for (int k = 0; k < nt; k++) chosen[T[k]] = 0;
        if (!ok) continue;
        int x = n;
        G.side[x] = (unsigned char)X;
        G.deg[x] = nt;
        for (int k = 0; k < nt; k++) {
            int t = T[k];
            G.adj[x][k] = t;
            G.adj[t][G.deg[t]++] = x;
        }
        G.n = n + 1;
        if (graph_ok()) {
            refresh();
            return 1;
        }
        for (int k = 0; k < nt; k++) del_half(&G, T[k], x);
        G.n = n;
        setW();
    }
    return 0;
}

/* Add two linked vertices (one per side), steal edges to fill them, then anneal. */
static int grow_two(double until) {
    int n = G.n;
    if (n + 2 > MAXN - 1) return 0;
    SNAP = G;
    int x = n, y = n + 1;
    G.n = n + 2;
    G.deg[x] = 0;
    G.deg[y] = 0;
    G.side[x] = 0;
    G.side[y] = 1;
    add_edge(&G, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = stamp;
    used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (G.side[a] != 0 || used[a] == stamp || G.deg[a] == 0) continue;
        int b = G.adj[a][rndint(G.deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(&G, a, b);
        add_edge(&G, x, b);
        add_edge(&G, y, a);
        used[a] = stamp;
        used[b] = stamp;
        k++;
    }
    long bad = bad_pairs();
    double Temp = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) {
            G = SNAP;
            refresh();
            return 0;
        }
        int v = rndint(G.n);
        for (int tr = 0; tr < 30 && badv[v] == 0; tr++) v = rndint(G.n);
        if (G.deg[v] == 0) continue;
        int u = G.adj[v][rndint(G.deg[v])];
        int s = rndint(G.n);
        if (s == v || G.side[s] != G.side[v] || G.deg[s] == 0) continue;
        int t = G.adj[s][rndint(G.deg[s])];
        if (t == u || has_edge(&G, v, t) || has_edge(&G, s, u)) continue;
        del_edge(&G, v, u);
        del_edge(&G, s, t);
        add_edge(&G, v, t);
        add_edge(&G, s, u);
        long nb = bad_pairs();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / Temp)) {
            bad = nb;
        } else {
            del_edge(&G, v, t);
            del_edge(&G, s, u);
            add_edge(&G, v, u);
            add_edge(&G, s, t);
        }
        Temp *= 0.9995;
        if (Temp < 0.05) Temp = 1.0;
    }
    if (graph_ok()) {
        refresh();
        return 1;
    }
    G = SNAP;
    refresh();
    return 0;
}

static int read_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    G.n = n;
    for (int v = 0; v < n; v++) {
        G.deg[v] = 0;
        G.side[v] = 0;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (G.deg[u] >= MAXD || G.deg[v] >= MAXD) return 0;
        if (has_edge(&G, u, v)) return 0;
        add_edge(&G, u, v);
    }
    static unsigned char seen[MAXN];
    memset(seen, 0, sizeof(seen));
    for (int s = 0; s < n; s++) {
        if (seen[s]) continue;
        int head = 0, tail = 0;
        seen[s] = 1;
        G.side[s] = 0;
        bq[tail++] = s;
        while (head < tail) {
            int x = bq[head++];
            for (int i = 0; i < G.deg[x]; i++) {
                int y = G.adj[x][i];
                if (!seen[y]) {
                    seen[y] = 1;
                    G.side[y] = (unsigned char)(1 - G.side[x]);
                    bq[tail++] = y;
                }
            }
        }
    }
    return graph_ok();
}

static void complete_bipartite(void) {
    G.n = 2 * d;
    for (int v = 0; v < G.n; v++) {
        G.deg[v] = 0;
        G.side[v] = (unsigned char)(v >= d);
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(&G, a, d + b);
}

static void print_graph(void) {
    long m = 0;
    for (int u = 0; u < G.n; u++)
        for (int i = 0; i < G.deg[u]; i++)
            if (u < G.adj[u][i]) m++;
    printf("%d %ld\n", G.n, m);
    for (int u = 0; u < G.n; u++)
        for (int i = 0; i < G.deg[u]; i++)
            if (u < G.adj[u][i]) printf("%d %d\n", u, G.adj[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int ok = read_start();
    if (!ok) complete_bipartite();
    refresh();
    ORIG = G;

    if (D >= 2) {
        int fails = 0;
        while (now() < t_end && G.n + 2 < MAXN - 1) {
            int grown = 0;
            int first = rndint(2);
            for (int j = 0; j < 2 && !grown; j++)
                grown = try_add_one((first + j) & 1, 150);
            if (grown) continue;
            double rem = t_end - now();
            if (rem < 0.1) break;
            double slice = rem > 2.0 ? rem * 0.5 : rem;
            if (grow_two(now() + slice)) {
                fails = 0;
                continue;
            }
            if (++fails >= 3) break;
        }
    }
    if (!graph_ok()) G = ORIG;
    print_graph();
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
    """PG(2,q) incidence plus, per element P of S, an A-vertex on the lines through P
    and a B-vertex on the points of line P. Diameter 3, max degree q+1+s."""
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
    """(n, edges) candidates from arc-extended projective planes for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp, index = _pg_data(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(S) and _loads_ok(cs, s, m, pl, lp):
                S = cs
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 88% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    cands = [fallback]
    rng = random.Random(seed * 7919 + d)

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        cands.append(lib.araujo_lopez_graph(d - 2))
    if D >= 3:
        cands.extend(_arc_candidates(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            cands.append(gq)

    best = fallback
    for c in sorted(cands, key=lambda g: -g[0]):
        if c[0] > best[0] and lib.is_valid(c[0], c[1], d, D):
            best = c
            break
    if best is fallback:
        for c in cands:
            if c[0] > best[0] and lib.is_valid(c[0], c[1], d, D):
                best = c

    # Hand the best valid start to C, which grows it.
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 1.0 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 3.0)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
