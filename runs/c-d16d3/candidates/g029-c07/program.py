"""Combined diameter-3 bipartite search.

Python builds the best starting graph it can: the projective plane when d-1 is a prime power,
the Araujo-Pardo-Lopez graph when d-2 is, and arc-extended projective planes (conic or greedy
arcs) otherwise. It always keeps K_{d,d} as a valid fallback. The C engine then grows the graph
in two ways, and only valid graphs are ever kept:
  1. Set-cover addition: one new vertex joined to a greedy cover of the other side, where the
     cover balls have radius D-1. This keeps the graph valid by construction.
  2. Annealed grow-by-two: add one vertex per side by stealing edges, then anneal
     degree-preserving swaps until no pair is farther than D apart.
Python re-checks everything with lib.is_valid.
"""
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

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int side[MAXN];
} Graph;

static int d, D;
static double t_end;
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
    for (int i = 0; i < g->deg[u]; i++) {
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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

static int read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = -1;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            g->n = 0;
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return 0;
        }
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
                    g->n = 0;
                    return 0;
                }
            }
        }
    }
    if (!is_valid(g)) {
        g->n = 0;
        return 0;
    }
    return 1;
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

/* ------------------------------------------------------------ radius balls */

static uint64_t ball[MAXN][MAXW];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;

static void ball_of(const Graph *g, int src, int r, uint64_t *bits, int W) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < g->deg[u]; k++) {
            int v = g->adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void compute_balls(const Graph *g, int r) {
    int W = (g->n + 63) / 64;
    for (int v = 0; v < g->n; v++) ball_of(g, v, r, ball[v], W);
}

/* ------------------------------------------------------------ set-cover addition */

/* Add one vertex on side X, joined to a greedy set T of vertices on the other side,
   chosen so that the radius-(D-1) balls of T cover every existing vertex.
   Requires compute_balls(g, D-1) for the current graph. */
static int cover_add(Graph *g, int X) {
    int n = g->n;
    if (n + 1 > MAXN) return 0;
    int W = (n + 63) / 64;
    uint64_t U[MAXW];
    static char sel[MAXN];
    int chosen[MAXD];
    int nt = 0;
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
    memset(sel, 0, sizeof(char) * (size_t)n);
    while (nt < d) {
        int best = -1;
        long bsc = -1;
        for (int v = 0; v < n; v++) {
            if (g->side[v] == X || g->deg[v] >= d || sel[v]) continue;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += __builtin_popcountll(ball[v][w] & U[w]);
            if (gain <= 0) continue;
            long sc = (long)gain * 16 + rndint(16);
            if (sc > bsc) {
                bsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        chosen[nt++] = best;
        for (int w = 0; w < W; w++) U[w] &= ~ball[best][w];
    }
    for (int w = 0; w < W; w++)
        if (U[w]) return 0;
    if (nt == 0) return 0;
    int x = n;
    g->n = n + 1;
    g->side[x] = X;
    g->deg[x] = 0;
    for (int k = 0; k < nt; k++) add_edge(g, x, chosen[k]);
    return 1;
}

/* Apply cover_add to a copy, keep it only if the result is valid. */
static int try_add_safe(Graph *cur, int X) {
    static Graph tmp;
    copy_graph(&tmp, cur);
    if (!cover_add(&tmp, X)) return 0;
    if (!is_valid(&tmp)) return 0;
    copy_graph(cur, &tmp);
    return 1;
}

/* ------------------------------------------------------------ grow by two + anneal */

static int grow_once(const Graph *cur, Graph *work, double until) {
    int n = cur->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, cur);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);

    static int used[MAXN];
    static int stamp2 = 0;
    stamp2++;
    used[x] = stamp2;
    used[y] = stamp2;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp2 || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp2) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = stamp2;
        used[b] = stamp2;
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
        if (s == v || work->side[s] != work->side[v] || work->deg[s] == 0) continue;
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

/* ------------------------------------------------------------ improvement loop */

static void improve(Graph *cur) {
    static Graph work;
    while (now() < t_end && cur->n + 1 <= moore_bound() && cur->n + 2 <= MAXN) {
        int X = rndint(2);
        compute_balls(cur, D - 1);
        if (try_add_safe(cur, X) || try_add_safe(cur, 1 - X)) continue;
        double left = t_end - now();
        if (left <= 0) break;
        double slice = left / 4.0 > 2.0 ? left / 4.0 : left;
        if (grow_once(cur, &work, now() + slice)) copy_graph(cur, &work);
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    static Graph cur, out;
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1 || !read_start(&cur)) {
        printf("0 0\n");
        return 0;
    }
    copy_graph(&out, &cur);
    if (D >= 2) improve(&cur);
    if (cur.n > out.n && is_valid(&cur)) copy_graph(&out, &cur);
    print_graph(&out);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective planes (diameter 3, max degree d).
# Points 0..m-1 and lines m..2m-1 of PG(2,q). Each point P in an arc S gets an
# A-vertex joined to the q+1 lines through P; each j in S gets a B-vertex joined
# to the q+1 points on line j. Point and line degrees rise by at most s = d-q-1.
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
    """True if every line holds at most s points of S and every point lies on at most s lines indexed by S."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG(2,q) incidence plus an A-vertex and a B-vertex for each element of S."""
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
        m, edges, pl, lp, index = _pg_data(q)
        cands = [[], _greedy_arc(m, s, pl, lp, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def known_start(d, D):
    """Closed-form graph for (d, D) with diameter 3 (valid for every D >= 3), or None."""
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(known_start(d, D))
        except Exception:
            pass
        try:
            rng = random.Random(seed * 7919 + d)
            cands = _arc_candidates(d, t0 + 0.2 * time_limit, rng)
            for cand in sorted(cands, key=lambda t: -t[0]):
                consider(cand)
        except Exception:
            pass

    # Hand the best construction to C, which grows it while keeping every graph valid.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 3)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
