"""Combined program: Python builds the best closed-form or arc-extended construction it can
(projective planes, Araujo-Pardo-Lopez, arc extensions with extra A-B edges, W(q) for D = 4).
The C engine then runs two phases on that start graph: a dominating-set insertion phase with
ruin-and-recreate, followed by grow-by-two annealing from the best graph found. Only valid
graphs are kept and returned."""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase A: insert a vertex on one side, adjacent to a set of spare-degree vertices on the
 *          other side whose radius-(D-1) balls cover all vertices. This keeps diameter <= D.
 *          When no insertion fits, remove 1-2 random vertices (ruin) and retry.
 * Phase B: grow by two (one vertex per side, stealing edges), then anneal degree-preserving
 *          edge swaps until no pair is farther than D apart.
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
static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { return __builtin_popcountll(x); }

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

/* ------------------------------------------------------------------ reach / distance */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Returns bitsets: row v has bit x set iff dist(v, x) <= R. Valid until the next call. */
static uint64_t *reach_masks(const Graph *g, int R) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < R; r++) {
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
    return cur;
}

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    const uint64_t *R = reach_masks(g, D);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = R + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(s[w]);
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

/* ------------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ phase A: insertion */

/* Greedy cover: choose <= d spare-degree vertices on side c whose radius-(D-1) balls
   (rows of B) cover all vertices. Writes the chosen vertices to sel; returns count or -1. */
static int cover_insert(const Graph *g, const uint64_t *B, int c, int restarts, int *sel) {
    static int cand[MAXN], used[MAXN], pick[MAXD + 1];
    static uint64_t unc[MAXW];
    int n = g->n, W = (n + 63) / 64;
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (g->side[v] == c && g->deg[v] < d) cand[nc++] = v;
    if (nc == 0) return -1;
    for (int r = 0; r < restarts; r++) {
        for (int w = 0; w < W; w++) unc[w] = ~0ULL;
        if (n % 64) unc[W - 1] = (1ULL << (n % 64)) - 1;
        int uncount = n, ns = 0;
        memset(used, 0, sizeof(int) * (size_t)nc);
        while (uncount > 0 && ns < d) {
            int bi = -1;
            long long bkey = -1;
            for (int i = 0; i < nc; i++) {
                if (used[i]) continue;
                const uint64_t *b = B + (size_t)cand[i] * W;
                int gain = 0;
                for (int w = 0; w < W; w++) gain += popc(b[w] & unc[w]);
                if (gain == 0) continue;
                long long key = (long long)gain * 4096 + (long long)(rnd() % 4096);
                if (key > bkey) { bkey = key; bi = i; }
            }
            if (bi < 0) break;
            used[bi] = 1;
            pick[ns++] = cand[bi];
            const uint64_t *b = B + (size_t)cand[bi] * W;
            uncount = 0;
            for (int w = 0; w < W; w++) {
                unc[w] &= ~b[w];
                uncount += popc(unc[w]);
            }
        }
        if (uncount == 0 && ns > 0) {
            for (int k = 0; k < ns; k++) sel[k] = pick[k];
            return ns;
        }
    }
    return -1;
}

static void insert_vertex(Graph *g, int c, const int *sel, int ns) {
    int v = g->n++;
    g->side[v] = (unsigned char)(1 - c);
    g->deg[v] = 0;
    for (int k = 0; k < ns; k++) add_edge(g, v, sel[k]);
}

static void remove_vertex(Graph *g, int r) {
    int last = g->n - 1;
    for (int k = 0; k < g->deg[r]; k++) del_half(g, g->adj[r][k], r);
    g->deg[r] = 0;
    if (r != last) {
        for (int k = 0; k < g->deg[last]; k++) {
            int u = g->adj[last][k];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == last) { g->adj[u][j] = r; break; }
        }
        memcpy(g->adj[r], g->adj[last], sizeof(int) * MAXD);
        g->deg[r] = g->deg[last];
        g->side[r] = g->side[last];
    }
    g->deg[last] = 0;
    g->n--;
}

static void phase_a(Graph *best, double until) {
    static Graph cur, tmp;
    static int sel[MAXD + 1];
    long moore = moore_bound();
    copy_graph(&cur, best);
    int bestn = best->n;
    while (now() < until) {
        int inserted = 0;
        if (cur.n + 1 <= moore && cur.n + 1 < MAXN) {
            const uint64_t *B = reach_masks(&cur, D - 1);
            int first = rndint(2);
            for (int t = 0; t < 2 && !inserted; t++) {
                int c = (t == 0) ? first : 1 - first;
                int ns = cover_insert(&cur, B, c, 6, sel);
                if (ns > 0) {
                    insert_vertex(&cur, c, sel, ns);
                    inserted = 1;
                }
            }
        }
        if (inserted) {
            if (cur.n > bestn && is_valid(&cur)) {
                copy_graph(best, &cur);
                bestn = cur.n;
            }
            continue;
        }
        /* ruin: remove 1-2 random vertices, keep only if still within diameter */
        copy_graph(&tmp, &cur);
        int k = 1 + rndint(2);
        for (int j = 0; j < k && cur.n > 2; j++) remove_vertex(&cur, rndint(cur.n));
        if (bad_pairs(&cur) != 0) copy_graph(&cur, &tmp);
        if (cur.n < bestn - 3) {
            copy_graph(&cur, best);
        }
    }
}

/* ------------------------------------------------------------------ phase B: grow by two */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
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

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("1 0\n");
        return 0;
    }

    static Graph best, orig;
    read_start(&best);
    if (best.n == 0) {
        if (D >= 2) complete_bipartite(&best);
        else { printf("1 0\n"); return 0; }
    }
    copy_graph(&orig, &best);

    if (D >= 2 && d >= 3 && best.n < moore_bound()) {
        phase_a(&best, t0 + (t_end - t0) * 0.5);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &orig);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#   A-side: a set SA of points, each joined to a new vertex on the lines through it.
#           Constraint: every line holds <= s points of SA.
#   B-side: a set SB of lines, each joined to a new vertex on the points of it.
#           Constraint: every point lies on <= s lines of SB.
# The sides are independent. Diameter stays 3. Afterwards, spare degree on the new
# A and B vertices is used for extra A-B edges, which can only shorten distances.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line.
    A-vertices are indexed 2m..2m+na-1 and B-vertices 2m+na..n-1."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E, list(range(2 * m, 2 * m + na)), list(range(2 * m + na, n))


def _fill_ab(n, edges, d, A, B):
    """Greedily add A-B edges while both endpoints have spare degree. Keeps diameter and bipartiteness."""
    deg = [0] * n
    have = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        have.add((u, v) if u < v else (v, u))
    E = list(edges)
    for a in A:
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] >= d:
                continue
            key = (a, b) if a < b else (b, a)
            if key in have:
                continue
            have.add(key)
            deg[a] += 1
            deg[b] += 1
            E.append(key)
    return n, E


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, one per prime power q."""
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
        SA = _greedy_side(m, s, point_lines, rng, 30, deadline)
        SB = _greedy_side(m, s, line_points, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c, A, B = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append(_fill_ab(n_c, e_c, d, A, B))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only for D >= 4.
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
    """W(q) for the largest prime power q <= min(d - 1, 7), for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.15 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        consider(_best_gq(d))

    # Hand the best construction to C: insertion phase, then grow-by-two annealing.
    elapsed = time.monotonic() - t0
    remaining = time_limit - elapsed
    budget = 0.8 * remaining - 2.0
    if budget > 0.5 and best[0] < lib.moore_bound(d, D):
        timeout = remaining - 1.5
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=timeout)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
