"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C engine.

Each start is a valid graph (arc-extended PG(2,q) incidence, the generalized quadrangle
for D >= 4, or K_{d,d}). The C engine works in two phases:

1. Greedy augmentation: add a new vertex on a random side, joined to a spare-capacity
   cover T on the other side. Accepted only if every vertex lies within D-1 of T, which
   keeps the graph valid.
2. NEW: remove-and-refill local search. Pick a random vertex, delete it, then try to add
   up to two replacement vertices with greedy covers. The state is accepted only if a full
   bitset diameter check passes and the order did not drop. Otherwise it is rolled back.
   The best valid graph seen is kept. This walks across plateaus of equal order and
   occasionally finds a larger graph.

Python re-checks everything with lib.is_valid and keeps a valid fallback.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define WORDS (MAXN / 64)
#define MAXDEG 64

typedef struct {
    int N;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
} Graph;

static Graph G, SAVE, BEST;
static int Dd, Dist;
static uint64_t ball[MAXN][WORDS];
static uint64_t tmpb[MAXN][WORDS];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int words_for(int n) { return (n + 63) / 64; }

/* out[v] = bitset of vertices within distance r of v in the current graph. */
static void compute_reach(int r, uint64_t out[][WORDS]) {
    int N = G.N, W = words_for(N);
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) out[v][i] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) tmpb[v][i] = out[v][i];
            for (int k = 0; k < G.deg[v]; k++) {
                int u = G.adj[v][k];
                for (int i = 0; i < W; i++) tmpb[v][i] |= out[u][i];
            }
        }
        for (int v = 0; v < N; v++)
            for (int i = 0; i < W; i++) out[v][i] = tmpb[v][i];
    }
}

/* True if the radius-Dist ball table (ball[]) covers every vertex from every vertex. */
static int all_full(void) {
    int N = G.N, W = words_for(N);
    uint64_t last = (N & 63) ? ((1ULL << (N & 63)) - 1ULL) : ~0ULL;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W - 1; i++)
            if (ball[v][i] != ~0ULL) return 0;
        if (ball[v][W - 1] != last) return 0;
    }
    return 1;
}

/* Full validity of the current graph for diameter Dist (degrees and sides are kept by construction). */
static int full_valid(void) {
    if (G.N < 1) return 0;
    for (int v = 0; v < G.N; v++)
        if (G.deg[v] > Dd) return 0;
    compute_reach(Dist, ball);
    return all_full();
}

/* Greedy cover on the current ball[] (radius Dist-1). Fills T with opposite-side vertices. */
static int select_cover(int X, int *T, int *covered) {
    int N = G.N, W = words_for(N);
    uint64_t U[WORDS];
    int sel[MAXN];
    int nt = 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    for (int v = 0; v < N; v++) sel[v] = 0;
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (G.side[v] == X || G.deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    int c = 1;
    for (int i = 0; i < W; i++)
        if (U[i]) c = 0;
    *covered = c;
    return nt;
}

static void add_vertex(int X, const int *T, int nt) {
    int x = G.N;
    G.side[x] = X;
    G.deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        G.adj[x][k] = t;
        G.adj[t][G.deg[t]++] = x;
    }
    G.N++;
}

/* Delete vertex x; the last vertex is moved into slot x so indices stay 0..N-1. */
static void remove_vertex(int x) {
    int N = G.N, y = N - 1;
    for (int k = 0; k < G.deg[x]; k++) {
        int u = G.adj[x][k];
        for (int j = 0; j < G.deg[u]; j++)
            if (G.adj[u][j] == x) {
                G.adj[u][j] = G.adj[u][--G.deg[u]];
                break;
            }
    }
    if (x != y) {
        G.side[x] = G.side[y];
        G.deg[x] = G.deg[y];
        for (int k = 0; k < G.deg[y]; k++) G.adj[x][k] = G.adj[y][k];
        for (int k = 0; k < G.deg[x]; k++) {
            int u = G.adj[x][k];
            for (int j = 0; j < G.deg[u]; j++)
                if (G.adj[u][j] == y) {
                    G.adj[u][j] = x;
                    break;
                }
        }
    }
    G.deg[y] = 0;
    G.N = N - 1;
}

static void copy_graph(Graph *dst, const Graph *src) {
    int N = src->N;
    dst->N = N;
    for (int v = 0; v < N; v++) {
        dst->side[v] = src->side[v];
        dst->deg[v] = src->deg[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

/* Phase 1: validity-preserving greedy growth. */
static void grow_greedy(double t_end, int fails_max) {
    int fails = 0;
    while (fails < fails_max && G.N < MAXN - 2 && now() < t_end) {
        int X = rndint(2);
        compute_reach(Dist - 1, ball);
        int T[MAXDEG], cov = 0;
        int nt = select_cover(X, T, &cov);
        if (cov && nt > 0) {
            add_vertex(X, T, nt);
            fails = 0;
        } else {
            fails++;
        }
    }
}

/* Phase 2 (new): remove-and-refill plateau search with full validity checks and rollback. */
static void local_search(double t_end) {
    long iters = 0;
    while (now() < t_end) {
        if (G.N < 3) break;
        iters++;
        copy_graph(&SAVE, &G);
        int before = G.N;
        remove_vertex(rndint(G.N));
        int adds = 0;
        for (int t = 0; t < 4 && adds < 2 && G.N < MAXN - 2; t++) {
            int X = rndint(2);
            compute_reach(Dist - 1, ball);
            int T[MAXDEG], cov = 0;
            int nt = select_cover(X, T, &cov);
            if (nt > 0) {
                add_vertex(X, T, nt);
                adds++;
            }
        }
        if (G.N >= before && full_valid()) {
            if (G.N > BEST.N) copy_graph(&BEST, &G);
        } else {
            copy_graph(&G, &SAVE);
        }
    }
}

static void print_graph(const Graph *g) {
    int M = 0;
    for (int v = 0; v < g->N; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) M++;
    printf("%d %d\n", g->N, M);
    for (int v = 0; v < g->N; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) printf("%d %d\n", v, g->adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    G.N = n;
    for (int v = 0; v < n; v++) G.deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (G.deg[u] >= Dd || G.deg[v] >= Dd) continue;
        G.adj[u][G.deg[u]++] = v;
        G.adj[v][G.deg[v]++] = u;
    }

    for (int v = 0; v < n; v++) G.side[v] = -1;
    {
        static int q[MAXN];
        for (int s = 0; s < n; s++) {
            if (G.side[s] >= 0) continue;
            G.side[s] = 0;
            int head = 0, t = 0;
            q[t++] = s;
            while (head < t) {
                int u = q[head++];
                for (int k = 0; k < G.deg[u]; k++) {
                    int v = G.adj[u][k];
                    if (G.side[v] < 0) {
                        G.side[v] = 1 - G.side[u];
                        q[t++] = v;
                    }
                }
            }
        }
    }

    if (!full_valid()) {
        /* Input is not valid: return it unchanged so the caller can reject it. */
        print_graph(&G);
        return 0;
    }

    double t_end = now() + budget;
    copy_graph(&BEST, &G);
    grow_greedy(t_end, 3000);
    if (G.N > BEST.N) copy_graph(&BEST, &G);
    local_search(t_end);

    print_graph(&BEST);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has spare capacity s = d - q - 1. Choose a point set S that is an arc, so each
# line holds at most s points of S. Add an A-vertex for each P in S (joined to
# lines through P) and a B-vertex for each j in S (joined to points on line j).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# C driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.25 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    # Run the remove-and-refill engine on the two largest starts, then polish the best.
    plan = starts[:2]
    for idx, src in enumerate(plan):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        share = remaining / (len(plan) - idx)
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    remaining = hard_end - time.monotonic()
    if remaining >= 2.0:
        try:
            n1, e1 = _augment(best[0], best[1], d, D, seed * 31 + 7,
                              max(0.3, remaining - 1.0), remaining + 3.0)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
