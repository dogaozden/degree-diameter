import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXDEG 64
#define MAXW ((MAXN + 63) / 64)

typedef uint64_t u64;
typedef u64 Row[MAXW];

typedef struct {
    int n;
    int color[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
} Graph;

static int DD = 3, DIAM = 3;
static double TLIM = 1.0;
static clock_t T0;
static uint64_t rs = 88172645463325252ULL;
static Row bufA[MAXN], bufB[MAXN];
static Graph gbest, gcur;
static int stackbuf[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }
static int timeup(void) { return elapsed() >= TLIM; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const Graph *g, int u, int v) {
    for (int k = 0; k < g->deg[u]; k++)
        if (g->adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_one(Graph *g, int u, int v) {
    for (int k = 0; k < g->deg[u]; k++) {
        if (g->adj[u][k] == v) {
            g->adj[u][k] = g->adj[u][--g->deg[u]];
            return;
        }
    }
}

static void del_edge(Graph *g, int u, int v) {
    del_one(g, u, v);
    del_one(g, v, u);
}

/* Balls of radius r as bitmasks. Returns a pointer to bufA or bufB. */
static Row *balls(const Graph *g, int r) {
    int n = g->n, nw = (n + 63) >> 6;
    Row *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(u64) * nw);
            for (int k = 0; k < g->deg[v]; k++) {
                const u64 *s = cur[g->adj[v][k]];
                for (int w = 0; w < nw; w++) nxt[v][w] |= s[w];
            }
        }
        Row *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DIAM (disconnected counts). */
static long long bad_count(const Graph *g) {
    int n = g->n, nw = (n + 63) >> 6;
    Row *R = balls(g, DIAM);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(R[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int color_graph(Graph *g) {
    int n = g->n;
    for (int v = 0; v < n; v++) g->color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (g->color[s] >= 0) continue;
        int sp = 0;
        g->color[s] = 0;
        stackbuf[sp++] = s;
        while (sp > 0) {
            int u = stackbuf[--sp];
            for (int k = 0; k < g->deg[u]; k++) {
                int v = g->adj[u][k];
                if (g->color[v] < 0) {
                    g->color[v] = 1 - g->color[u];
                    stackbuf[sp++] = v;
                } else if (g->color[v] == g->color[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int read_start(Graph *g) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 2 || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) g->deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= DD || g->deg[v] >= DD) return 0;
        if (has_edge(g, u, v)) return 0;
        add_edge(g, u, v);
    }
    if (!color_graph(g)) return 0;
    if (bad_count(g) != 0) return 0;
    return 1;
}

static void make_k2(Graph *g) {
    g->n = 2;
    g->deg[0] = 0;
    g->deg[1] = 0;
    g->color[0] = 0;
    g->color[1] = 1;
    add_edge(g, 0, 1);
}

/* Insert vertex n with colour c, joined greedily to opposite-colour vertices
   to cover the old vertices by radius DIAM-1 balls. */
static void greedy_attach(Graph *g, int c) {
    int n = g->n, nw = (n + 63) >> 6;
    Row *R = balls(g, DIAM - 1);
    Row cov;
    memset(cov, 0, sizeof(Row));
    int covered = 0, picks = 0, nc = 0;
    int w = n;
    for (int u = 0; u < n; u++)
        if (g->color[u] != c && g->deg[u] < DD) candbuf[nc++] = u;
    g->color[w] = c;
    g->deg[w] = 0;
    g->n = n + 1;
    while (picks < DD && covered < n) {
        int bsel = -1, bg = 0, ties = 0;
        for (int i = 0; i < nc; i++) {
            int u = candbuf[i];
            if (g->deg[u] >= DD) continue;
            int gain = 0;
            for (int x = 0; x < nw; x++) gain += popc(R[u][x] & ~cov[x]);
            if (gain > bg) {
                bg = gain;
                bsel = u;
                ties = 1;
            } else if (gain == bg && gain > 0) {
                ties++;
                if (rndint(ties) == 0) bsel = u;
            }
        }
        if (bsel < 0) break;
        add_edge(g, bsel, w);
        picks++;
        covered += bg;
        for (int x = 0; x < nw; x++) cov[x] |= R[bsel][x];
    }
}

/* Add one random cross edge between two spare vertices. Monotone: never hurts. */
static int try_fill(Graph *g) {
    int n = g->n;
    for (int t = 0; t < 30; t++) {
        int u = rndint(n), v = rndint(n);
        if (g->color[u] == g->color[v]) continue;
        if (g->deg[u] >= DD || g->deg[v] >= DD) continue;
        if (has_edge(g, u, v)) continue;
        add_edge(g, u, v);
        return 1;
    }
    return 0;
}

static void fill_all(Graph *g, int tries) {
    for (int t = 0; t < tries; t++) try_fill(g);
}

static int pick_color_vertex(const Graph *g, int c) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(g->n);
        if (g->color[v] == c && g->deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving 2-switch: (A,B),(C,E) -> (A,E),(C,B), A and C colour 0. */
static int two_switch(Graph *g, int *a, int *b, int *c, int *e) {
    int A = pick_color_vertex(g, 0);
    int C = pick_color_vertex(g, 0);
    if (A < 0 || C < 0 || A == C) return 0;
    int B = g->adj[A][rndint(g->deg[A])];
    int E = g->adj[C][rndint(g->deg[C])];
    if (B == E) return 0;
    if (has_edge(g, A, E) || has_edge(g, C, B)) return 0;
    del_edge(g, A, B);
    del_edge(g, C, E);
    add_edge(g, A, E);
    add_edge(g, C, B);
    *a = A;
    *b = B;
    *c = C;
    *e = E;
    return 1;
}

static void undo_switch(Graph *g, int a, int b, int c, int e) {
    del_edge(g, a, e);
    del_edge(g, c, b);
    add_edge(g, a, b);
    add_edge(g, c, e);
}

/* Simulated annealing on the bad-pair count. Returns the final cost of g. */
static long long anneal(Graph *g, long long cur, int iters, double T0v, double T1v) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && timeup()) break;
        double T = T0v * pow(T1v / T0v, (double)it / (double)iters);
        if (rnd01() < 0.25 && try_fill(g)) {
            cur = bad_count(g);
            continue;
        }
        int a, b, c, e;
        if (!two_switch(g, &a, &b, &c, &e)) continue;
        long long nxt = bad_count(g);
        long long delta = nxt - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nxt;
        } else {
            undo_switch(g, a, b, c, e);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    if (DD > MAXDEG) DD = MAXDEG;
    if (DD < 1) DD = 1;
    if (DIAM < 1) DIAM = 1;
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TLIM = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    T0 = clock();

    if (!read_start(&gbest)) make_k2(&gbest);

    if (DIAM >= 2) {
        const int ITERS = 1500;
        while (!timeup() && gbest.n + 1 < MAXN) {
            gcur = gbest;
            greedy_attach(&gcur, rndint(2));
            fill_all(&gcur, 60);
            long long cost = bad_count(&gcur);
            if (cost > 0 && !timeup()) cost = anneal(&gcur, cost, ITERS, 1.0, 0.05);
            if (cost == 0) gbest = gcur;
        }
    }

    int n = gbest.n, m = 0;
    for (int u = 0; u < n; u++)
        for (int k = 0; k < gbest.deg[u]; k++)
            if (gbest.adj[u][k] > u) m++;
    printf("%d %d\n", n, m);
    for (int u = 0; u < n; u++)
        for (int k = 0; k < gbest.deg[u]; k++) {
            int v = gbest.adj[u][k];
            if (v > u) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Build: best arc-extended graph (or K_{d,d}) is the start for the C search,
# which inserts vertices and repairs with annealing over 2-switches.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        arcs = _arc_extensions(d, t0 + 0.12 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for cand in arcs[:3]:
            consider(cand)

    # C search from the best valid start. Total wall time stays well under time_limit.
    elapsed = time.monotonic() - t0
    budget = 0.80 * time_limit - elapsed - 1.5
    if budget >= 1.0:
        remaining = 0.92 * time_limit - (time.monotonic() - t0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=best,
                             timeout=max(1.0, remaining))
            n, e = lib.parse_graph_text(text)
            consider((n, e))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
