"""Diameter-3 bipartite search: arc-extended projective-plane starts plus a C augmentation engine.

Construction: take the point-line incidence graph of PG(2,q) and add one new vertex per arc
element on each side. A side-A vertex for point P joins the q+1 lines through P. A side-B
vertex for line j joins the q+1 points on j. If every line holds at most s = d-q-1 arc points
and every point lies on at most s arc lines, all degrees stay <= d and the diameter stays 3.
Python tries several q and arc choices (empty, randomized greedy, conic plus nucleus) and keeps
the largest valid one. The C engine then tries two moves from that start:
  1. add one vertex on a random side, joined to a greedy set cover of the opposite side with
     radius D-1 balls (adding a vertex never shortens existing distances, so validity is kept);
  2. if that fails, add two vertices and anneal degree-preserving edge swaps until valid.
Every returned graph is re-checked with lib.is_valid.
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
    int side[MAXN];
} Graph;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static uint64_t BUF1[MAXN * MAXW], BUF2[MAXN * MAXW];
static uint64_t BALL[MAXN * MAXW], RES[MAXN * MAXW];
static int badv[MAXN];
static Graph best, work;

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
        if (s > 100000000L) return 100000000L;
        p *= (d - 1);
        if (p > 100000000L) p = 100000000L;
    }
    return 2 * s;
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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

/* res row v = bitset of vertices within distance r of v. */
static void reach(const Graph *g, int r, uint64_t *res) {
    int n = g->n, W = (n + 63) / 64;
    int rr = r < n ? r : n;
    uint64_t *cur = BUF1, *nxt = BUF2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int k = 0; k < rr; k++) {
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
    memcpy(res, cur, sizeof(uint64_t) * (size_t)n * W);
}

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    reach(g, D, RES);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = RES + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
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
    return bad_pairs(g) == 0;
}

static int read_start(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 2 || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = -1;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] >= 0) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] < 0) {
                    g->side[u] = 1 - g->side[v];
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    return 0;
                }
            }
        }
    }
    return is_valid(g);
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

/* Add one vertex on side X, joined to a greedy cover of all vertices by radius D-1 balls
 * of opposite-side vertices with spare degree. Modifies g in place on success. */
static int try_add(Graph *g, int X) {
    int n = g->n;
    if (n + 1 >= MAXN || (long)(n + 1) > moore_bound()) return 0;
    int W = (n + 63) / 64;
    reach(g, D - 1, BALL);
    uint64_t U[MAXW];
    int chosen[MAXD];
    int sel[MAXN];
    memset(sel, 0, sizeof(int) * (size_t)n);
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
    int nt = 0;
    while (nt < d) {
        int bestv = -1;
        long bestsc = -1;
        for (int v = 0; v < n; v++) {
            if (g->side[v] == X || g->deg[v] >= d || sel[v]) continue;
            int gain = 0;
            const uint64_t *row = BALL + (size_t)v * W;
            for (int w = 0; w < W; w++) gain += __builtin_popcountll(row[w] & U[w]);
            if (gain <= 0) continue;
            long sc = (long)gain * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                bestv = v;
            }
        }
        if (bestv < 0) break;
        sel[bestv] = 1;
        chosen[nt++] = bestv;
        const uint64_t *row = BALL + (size_t)bestv * W;
        for (int w = 0; w < W; w++) U[w] &= ~row[w];
    }
    for (int w = 0; w < W; w++)
        if (U[w]) return 0;
    if (nt == 0) return 0;
    int x = n;
    g->n = n + 1;
    g->deg[x] = 0;
    g->side[x] = X;
    for (int k = 0; k < nt; k++) add_edge(g, x, chosen[k]);
    return 1;
}

/* Add two vertices (one per side, joined by an edge) with stolen edges, then anneal swaps. */
static int grow_once(const Graph *src, Graph *wk, double until) {
    int n = src->n;
    if ((long)(n + 2) > moore_bound() || n + 2 >= MAXN - 1) return 0;
    copy_graph(wk, src);
    int x = n, y = n + 1;
    wk->n = n + 2;
    wk->deg[x] = wk->deg[y] = 0;
    wk->side[x] = 0;
    wk->side[y] = 1;
    add_edge(wk, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (wk->side[a] != 0 || used[a] == stamp || wk->deg[a] == 0) continue;
        int b = wk->adj[a][rndint(wk->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(wk, a, b);
        add_edge(wk, x, b);
        add_edge(wk, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(wk);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(wk->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(wk->n);
        if (wk->deg[v] == 0) continue;
        int u = wk->adj[v][rndint(wk->deg[v])];
        int s = rndint(wk->n);
        if (wk->side[s] != wk->side[v] || s == v || wk->deg[s] == 0) continue;
        int t = wk->adj[s][rndint(wk->deg[s])];
        if (t == u || has_edge(wk, v, t) || has_edge(wk, s, u)) continue;
        del_edge(wk, v, u);
        del_edge(wk, s, t);
        add_edge(wk, v, t);
        add_edge(wk, s, u);
        long nb = bad_pairs(wk);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(wk, v, t);
            del_edge(wk, s, u);
            add_edge(wk, v, u);
            add_edge(wk, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(wk);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 1 || D < 2 || d > MAXD || !read_start(&best)) {
        printf("0 0\n");
        return 0;
    }

    while (now() < t_end) {
        int grew = 0;
        for (int a = 0; a < 40 && !grew; a++) {
            copy_graph(&work, &best);
            if (try_add(&work, rndint(2)) && is_valid(&work)) {
                copy_graph(&best, &work);
                grew = 1;
            }
        }
        if (grew) continue;
        if ((long)(best.n + 2) > moore_bound()) break;
        double left = t_end - now();
        if (left <= 0) break;
        double slice = left / 3.0 > 3.0 ? left / 3.0 : (left < 3.0 ? left : 3.0);
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
    }
    if (!is_valid(&best)) {
        printf("0 0\n");
        return 0;
    }
    print_graph(&best);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q); point i and line i share a vector."""
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
    """Old PG(2,q) incidence plus, per P in S, an A-vertex on the lines through P
    and, per j in S, a B-vertex on the points of line j."""
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
    """(n, edges) candidates from arc-extended projective planes, one per prime power q <= d-1."""
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
        options = [[]]
        if s >= 1:
            options.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            options.append(_conic_set(q, index, lib.GF(q)))
        options = [S for S in options if _loads_ok(S, s, m, pl, lp)]
        S = max(options, key=len)
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
    """W(q) for the largest prime power q <= min(d-1, 7), or None."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))   # K_{d,d}: diameter 2, valid for D >= 2
    rng = random.Random(seed * 7919 + d)
    cands = [fallback]
    try:
        if D >= 3:
            if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
                cands.append(lib.araujo_lopez_graph(d - 2))
            cands += _arc_candidates(d, t0 + 0.2 * time_limit, rng)
        if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
            g = _best_gq(d)
            if g is not None:
                cands.append(g)
    except Exception:
        pass

    cands.sort(key=lambda g: -g[0])
    best = None
    for g in cands:
        if lib.is_valid(g[0], g[1], d, D):
            best = g
            break
    if best is None:
        best = fallback

    # Hand the best construction to C for augmentation.
    budget = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
    if d <= 60 and budget > 1.0 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 3)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
