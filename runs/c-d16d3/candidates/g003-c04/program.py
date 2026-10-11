"""Combined diameter-degree search: closed-form starts, then a C engine that grows the best graph.

Starts: Moore graphs and Araujo-Pardo-Lopez graphs when they apply, arc-extended projective
planes (greedy and conic arcs), and W(q) for D >= 4, all checked with lib.is_valid.
The C engine repeats two moves on a valid graph and keeps only valid results:
  1. cover_add: a new vertex on one side, joined to a greedy set cover of the other side
     (each vertex must be within D-1 of a neighbour), which keeps all distances valid.
  2. grow_two: add two vertices, steal d-1 edges, then anneal degree-preserving swaps
     until no pair is farther than D apart.
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
#define MAXDEG 48
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int side[MAXN];
} Graph;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static int badv[MAXN];
static Graph cur, work, best, start;

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

/* ------------------------------------------------------------ adjacency */

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

/* ------------------------------------------------------------ distances */

/* Bitset of radius-r balls: row v (W words) has bit u set iff dist(u,v) <= r. */
static uint64_t *compute_balls(const Graph *g, int r, uint64_t *cur_b, uint64_t *nxt_b) {
    int n = g->n, W = (n + 63) / 64;
    memset(cur_b, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur_b[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt_b + (size_t)v * W;
            const uint64_t *src = cur_b + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur_b + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur_b;
        cur_b = nxt_b;
        nxt_b = t;
    }
    return cur_b;
}

/* Number of unordered pairs at distance > D; fills badv[] per vertex. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *b = compute_balls(g, D, BA, BB);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = b + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* ------------------------------------------------------------ I/O */

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
        if (g->deg[u] >= MAXDEG || g->deg[v] >= MAXDEG) return 0;
        add_edge(g, u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] >= 0) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] < 0) {
                    g->side[u] = 1 - g->side[v];
                    q[tail++] = u;
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
            if (g->adj[u][i] > u) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (g->adj[u][i] > u) printf("%d %d\n", u, g->adj[u][i]);
}

/* ------------------------------------------------------------ move 1: cover add */

/* Add one vertex x on side X joined to T (side 1-X, spare degree) so that every
   vertex lies within distance D-1 of T. Then dist(x, v) <= D for all v. */
static int cover_add(Graph *g) {
    int n = g->n;
    if (n + 1 > MAXN || n + 1 > moore_bound()) return 0;
    int W = (n + 63) / 64;
    static int chosen[MAXN];
    int first = rndint(2);
    for (int a = 0; a < 2; a++) {
        int X = (a == 0) ? first : 1 - first;
        uint64_t *b = compute_balls(g, D - 1, BA, BB);
        uint64_t U[MAXW];
        for (int w = 0; w < W; w++) U[w] = ~0ULL;
        if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
        memset(chosen, 0, sizeof(int) * (size_t)n);
        int T[MAXDEG], nt = 0;
        while (nt < d) {
            int bestv = -1;
            long bestsc = -1;
            for (int v = 0; v < n; v++) {
                if (g->side[v] == X || g->deg[v] >= d || chosen[v]) continue;
                const uint64_t *bv = b + (size_t)v * W;
                int gain = 0;
                for (int w = 0; w < W; w++) gain += __builtin_popcountll(bv[w] & U[w]);
                if (gain <= 0) continue;
                long sc = (long)gain * 64 + rndint(64);
                if (sc > bestsc) {
                    bestsc = sc;
                    bestv = v;
                }
            }
            if (bestv < 0) break;
            chosen[bestv] = 1;
            T[nt++] = bestv;
            const uint64_t *bb = b + (size_t)bestv * W;
            for (int w = 0; w < W; w++) U[w] &= ~bb[w];
            int left = 0;
            for (int w = 0; w < W; w++) left |= (U[w] != 0);
            if (!left) break;
        }
        int left = 0;
        for (int w = 0; w < W; w++) left |= (U[w] != 0);
        if (left || nt == 0) continue;
        int x = n;
        g->n = n + 1;
        g->side[x] = X;
        g->deg[x] = 0;
        for (int k = 0; k < nt; k++) add_edge(g, x, T[k]);
        if (is_valid(g)) return 1;
        for (int k = 0; k < nt; k++) del_half(g, T[k], x);
        g->deg[x] = 0;
        g->n = n;
    }
    return 0;
}

/* ------------------------------------------------------------ move 2: grow by two */

static int grow_two(Graph *g, double until, long max_iter) {
    int n = g->n;
    if (n + 2 > MAXN || n + 2 > moore_bound()) return 0;
    int x = n, y = n + 1;
    g->n = n + 2;
    g->deg[x] = g->deg[y] = 0;
    g->side[x] = 0;
    g->side[y] = 1;
    add_edge(g, x, y);

    static int usedv[MAXN];
    static int stamp = 0;
    stamp++;
    usedv[x] = usedv[y] = stamp;
    int k = 0;
    for (long tries = 0; k < d - 1 && tries < 200000; tries++) {
        int a = rndint(n);
        if (g->side[a] != 0 || usedv[a] == stamp || g->deg[a] == 0) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        if (b >= n || usedv[b] == stamp) continue;
        del_edge(g, a, b);
        add_edge(g, x, b);
        add_edge(g, y, a);
        usedv[a] = usedv[b] = stamp;
        k++;
    }

    long bad = bad_pairs(g);
    double T = 1.0;
    for (long it = 0; bad > 0 && it < max_iter; it++) {
        if ((it & 15) == 0 && now() > until) return 0;
        int v = rndint(g->n);
        for (int tr = 0; tr < 40 && badv[v] == 0; tr++) v = rndint(g->n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int s = rndint(g->n);
        if (s == v || g->side[s] != g->side[v] || g->deg[s] == 0) continue;
        int t = g->adj[s][rndint(g->deg[s])];
        if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) continue;
        del_edge(g, v, u);
        del_edge(g, s, t);
        add_edge(g, v, t);
        add_edge(g, s, u);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(g, v, t);
            del_edge(g, s, u);
            add_edge(g, v, u);
            add_edge(g, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    if (bad != 0) return 0;
    return is_valid(g);
}

/* ------------------------------------------------------------ driver */

static void search(void) {
    long mb = moore_bound();
    while (now() < t_end) {
        if (cur.n >= mb) break;
        if (cover_add(&cur)) continue;
        if (cur.n + 2 > mb) break;
        copy_graph(&work, &cur);
        double remain = t_end - now();
        double slice = remain < 2.5 ? remain : 2.5;
        if (slice <= 0) break;
        if (grow_two(&work, now() + slice, 20000)) copy_graph(&cur, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG - 8 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    if (!read_start(&start)) {
        printf("0 0\n");
        return 0;
    }
    copy_graph(&best, &start);
    copy_graph(&cur, &start);
    t_end = now() + limit;
    search();
    if (is_valid(&cur)) print_graph(&cur);
    else print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective planes (diameter 3).
# Points 0..m-1 and lines m..2m-1 of PG(2,q). For an arc S with every line holding
# at most s points of S, add an A-vertex per point of S (joined to lines through it)
# and a B-vertex per point of S (joined to points of that line index).
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


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    from_field = lib.GF(q)
    S = [index[(1, t, from_field.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG(2,q) incidence plus an A and a B vertex for each element of S."""
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
    """(n, edges) candidates from arc-extended projective planes, for each prime power q."""
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
        sets = [_greedy_arc(m, s, pl, lp, rng, 60, deadline)]
        if s >= 2:
            sets.append(_conic_set(q, index))
        for S in sets:
            if S and _loads_ok(S, s, m, pl, lp):
                out.append(_arc_graph(m, edges, pl, lp, S))
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


def _best_gq(d):
    """W(q) for the largest prime power q <= min(d-1, 7) (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family
    return None


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))   # K_{d,d}: diameter 2, valid for D >= 2
    best = fallback

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    rng = random.Random(seed * 7919 + d)
    if D >= 3:
        try:
            consider(known_start(d, D))
        except Exception:
            pass
        if best[0] < lib.moore_bound(d, D):
            try:
                for cand in sorted(_arc_candidates(d, t0 + 0.2 * time_limit, rng),
                                   key=lambda t: -t[0]):
                    consider(cand)
            except Exception:
                pass
    if D >= 4 and best[0] < lib.moore_bound(d, D) and time.monotonic() < t0 + 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)
        except Exception:
            pass

    # Hand the best construction to C, which grows it.
    budget = 0.80 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 1.0 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 5.0)
            n, e = lib.parse_graph_text(text)
            consider((n, e))
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
