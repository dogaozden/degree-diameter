"""Combined diameter-3/4 bipartite search.

Python builds the strongest closed-form start it can: Moore graphs, Araujo-Pardo-Lopez graphs,
arc-extended projective planes (greedy and conic arcs), and for D >= 4 the generalized quadrangle
W(q). The C engine then grows that graph with two moves:
  1. Add one vertex on a random side, joined to a greedy set cover T of spare vertices on the
     other side. Valid by construction: every old vertex lies within D-1 of T.
  2. When that stalls, add two vertices (an edge between them, with d-1 stolen edges each) and
     anneal degree-preserving edge swaps until no pair is farther than D apart.
Every output is re-validated in C and again in Python with lib.is_valid.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXD 64

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static Graph G_best, G_work, G_tmp;
static uint64_t REACH[MAXN * MAXW];
static uint64_t BALL[MAXN * MAXW];
static uint64_t TMP[MAXN * MAXW];
static int badv[MAXN];

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

static void add_half(Graph *g, int u, int v) { g->adj[u][g->deg[u]++] = v; }

static void add_edge(Graph *g, int u, int v) {
    add_half(g, u, v);
    add_half(g, v, u);
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

/* ------------------------------------------------------------ reachability */

/* out[v] = bitset of vertices within distance r of v. */
static void reach_sets(const Graph *g, int r, uint64_t *out) {
    int n = g->n, w = (n + 63) / 64;
    uint64_t *cur = out, *nxt = TMP;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + v / 64] |= 1ULL << (v % 64);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            const uint64_t *src = cur + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * w);
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * w;
                for (int j = 0; j < w; j++) dst[j] |= s[j];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint64_t) * (size_t)n * w);
}

/* Number of unordered pairs at distance > D; fills badv[]. */
static long eval_bad(const Graph *g) {
    int n = g->n, w = (n + 63) / 64;
    reach_sets(g, D, REACH);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = REACH + (size_t)v * w;
        for (int j = 0; j < w; j++) c += __builtin_popcountll(s[j]);
        badv[v] = n - c;
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
    return eval_bad(g) == 0;
}

/* ------------------------------------------------------------ I/O */

static int read_start(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
        for (int i = 0; i < g->deg[u]; i++)
            if (g->adj[u][i] == v) return 0;
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
                }
            }
        }
    }
    return is_valid(g);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= d);
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
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

/* ------------------------------------------------------------ move 1: add one vertex */

/* Adds vertex x on side X joined to a greedy cover T (other side, spare degree)
   such that every vertex lies within D-1 of T. BALL must hold radius D-1 balls of g. */
static int try_add_one(Graph *g, int X) {
    int n = g->n, w = (n + 63) / 64;
    if (n + 1 > MAXN) return 0;
    uint64_t U[MAXW];
    for (int i = 0; i < w; i++) U[i] = ~0ULL;
    if (n & 63) U[w - 1] = (1ULL << (n & 63)) - 1ULL;
    static char used[MAXN];
    memset(used, 0, (size_t)n);
    int T[MAXD], nt = 0;
    while (nt < d) {
        int any = 0;
        for (int i = 0; i < w; i++)
            if (U[i]) { any = 1; break; }
        if (!any) break;
        int best = -1;
        long bs = -1;
        for (int v = 0; v < n; v++) {
            if (g->side[v] == X || g->deg[v] >= d || used[v]) continue;
            const uint64_t *bl = BALL + (size_t)v * w;
            long gain = 0;
            for (int i = 0; i < w; i++) gain += __builtin_popcountll(bl[i] & U[i]);
            if (gain <= 0) continue;
            long sc = gain * 1024 + rndint(1024);
            if (sc > bs) {
                bs = sc;
                best = v;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        T[nt++] = best;
        const uint64_t *bl = BALL + (size_t)best * w;
        for (int i = 0; i < w; i++) U[i] &= ~bl[i];
    }
    for (int i = 0; i < w; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = n;
    g->n = n + 1;
    g->side[x] = (unsigned char)X;
    g->deg[x] = 0;
    for (int k = 0; k < nt; k++) {
        add_edge(g, x, T[k]);
    }
    return 1;
}

/* Try a few random sides; accept only a fully validated graph. */
static int add_one_tries(Graph *g, int tries) {
    if (g->n + 1 > MAXN) return 0;
    for (int t = 0; t < tries; t++) {
        reach_sets(g, D - 1, BALL);
        copy_graph(&G_tmp, g);
        if (try_add_one(&G_tmp, rndint(2)) && is_valid(&G_tmp)) {
            copy_graph(g, &G_tmp);
            return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ move 2: grow by two + anneal */

static int grow_two(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || work->deg[a] == 0 || used[a] == stamp) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }

    long bad = eval_bad(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tr = 0; tr < 30 && badv[v] == 0; tr++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (s == v || work->side[s] != work->side[v] || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = eval_bad(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    if (!read_start(&G_best)) complete_bipartite(&G_best);
    if (!is_valid(&G_best)) complete_bipartite(&G_best);

    if (D >= 2) {
        long moore = moore_bound();
        while (now() < t_end && G_best.n < moore && G_best.n < MAXN) {
            if (add_one_tries(&G_best, 30)) continue;
            double left = t_end - now();
            double slice = left < 3.0 ? left : (left / 3.0 > 3.0 ? left / 3.0 : 3.0);
            if (grow_two(&G_best, &G_work, now() + slice))
                copy_graph(&G_best, &G_work);
        }
    }
    if (!is_valid(&G_best)) complete_bipartite(&G_best);
    print_graph(&G_best);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane based starts (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
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
    """Old PG(2,q) incidence plus, per element P of S, an A-vertex on the lines through P
    and a B-vertex on the points of line P. Diameter 3."""
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


def _arc_candidates(d, D, deadline, rng):
    """Validated (n, edges) from arc-extended projective planes, one per prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index = _pg_data(q)
        cands = [_greedy_arc(m, s, pl, lp, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, pl, lp):
            continue
        n, E = _arc_graph(m, edges, pl, lp, S)
        if lib.is_valid(n, E, d, D):
            out.append((n, E))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), for D >= 4.
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


def _best_gq(d, D):
    """Validated W(q) start for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            n, E = _gq_w(q)
            if lib.is_valid(n, E, d, D):
                return n, E
    return None


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    rng = random.Random(seed * 7919 + d)
    if D >= 3:
        consider(known_start(d, D))
        for cand in sorted(_arc_candidates(d, D, t0 + 0.2 * time_limit, rng),
                           key=lambda t: -t[0]):
            consider(cand)
    if D >= 4 and time.monotonic() < t0 + 0.3 * time_limit:
        consider(_best_gq(d, D))

    # Hand the best construction to C, which grows it.
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 0.5 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 3)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
