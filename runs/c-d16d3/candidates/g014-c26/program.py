"""Combined program: arc-extended projective planes give the starting graph (order 2(m+k) with the
conic arc, which reaches 394 for d=16). A C engine then grows it. Each step first tries to add one
vertex on a side, joined to a greedy set cover of spare vertices within distance D-1 of every
existing vertex. This is always valid because distances never increase. When that stalls, it
grows by two vertices with annealed degree-preserving edge swaps. Python re-checks everything."""
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

#define MAXN 1024
#define MAXDEG 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long moore;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
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

static int W_of(int n) { return (n + 63) / 64; }

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

/* Bitsets of vertices within distance r, for every vertex. Returns RA or RB. */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

static uint64_t *balls_r(const Graph *g, int r) {
    int n = g->n, W = W_of(n);
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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
    int n = g->n, W = W_of(n);
    uint64_t *b = balls_r(g, D);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = b + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(s[w]);
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
            if (!has_edge(g, u, v)) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static int read_start(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= MAXDEG || g->deg[v] >= MAXDEG) return 0;
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

/* ---------------------------------------------------------- grow by one */

static uint64_t BALL[MAXN * MAXW];
static int sel[MAXN];

/* Add one vertex on side X joined to a set T (opposite side, spare degree) such that every
   existing vertex is within distance D-1 of T. Then every vertex is within D of the new one. */
static int try_add_one(Graph *g, int X) {
    int n = g->n, W = W_of(n);
    if (n + 1 >= MAXN) return 0;
    uint64_t *b = balls_r(g, D - 1);
    memcpy(BALL, b, sizeof(uint64_t) * (size_t)n * W);
    uint64_t U[MAXW];
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
    memset(sel, 0, sizeof(int) * (size_t)n);
    int T[MAXDEG], nt = 0;
    while (nt < d) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < n; v++) {
            if (g->side[v] == X || g->deg[v] >= d || sel[v]) continue;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += popc(BALL[(size_t)v * W + w] & U[w]);
            if (gain <= 0) continue;
            long sc = (long)gain * 64 + rndint(64);
            if (sc > bestsc) { bestsc = sc; best = v; }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int w = 0; w < W; w++) U[w] &= ~BALL[(size_t)best * W + w];
        int done = 1;
        for (int w = 0; w < W; w++) if (U[w]) { done = 0; break; }
        if (done) break;
    }
    for (int w = 0; w < W; w++) if (U[w]) return 0;
    if (nt == 0) return 0;
    int x = n;
    g->side[x] = (unsigned char)X;
    g->deg[x] = 0;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        g->adj[x][g->deg[x]++] = t;
        g->adj[t][g->deg[t]++] = x;
    }
    g->n = n + 1;
    return 1;
}

static int grow_greedy(Graph *best, double until) {
    int grew = 0, fails = 0;
    while (now() < until && fails < 200 && best->n + 1 <= moore) {
        int X = rndint(2);
        if (try_add_one(best, X)) { grew = 1; fails = 0; }
        else fails++;
    }
    return grew;
}

/* ---------------------------------------------------------- grow by two */

static Graph WK;
static int used[MAXN];
static int stamp = 0;

/* Insert x (side 0) and y (side 1) with edge x-y, steal d-1 edges, then anneal swaps.
   Result is left in WK. Returns 1 if valid. */
static int grow_two(const Graph *best, double until) {
    int n = best->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
    copy_graph(&WK, best);
    int x = n, y = n + 1;
    WK.n = n + 2;
    WK.deg[x] = 0;
    WK.deg[y] = 0;
    WK.side[x] = 0;
    WK.side[y] = 1;
    add_edge(&WK, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (WK.side[a] != 0 || used[a] == stamp || WK.deg[a] == 0) continue;
        int b = WK.adj[a][rndint(WK.deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(&WK, a, b);
        add_edge(&WK, x, b);
        add_edge(&WK, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(&WK);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(WK.n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(WK.n);
        if (WK.deg[v] == 0) continue;
        int u = WK.adj[v][rndint(WK.deg[v])];
        int s = rndint(WK.n);
        if (s == v || WK.side[s] != WK.side[v] || WK.deg[s] == 0) continue;
        int t = WK.adj[s][rndint(WK.deg[s])];
        if (t == u || has_edge(&WK, v, t) || has_edge(&WK, s, u)) continue;
        del_edge(&WK, v, u);
        del_edge(&WK, s, t);
        add_edge(&WK, v, t);
        add_edge(&WK, s, u);
        long nb = bad_pairs(&WK);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(&WK, v, t);
            del_edge(&WK, s, u);
            add_edge(&WK, v, u);
            add_edge(&WK, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(&WK);
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.88 - 0.3;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 1 || D < 1 || d > MAXDEG) { printf("0 0\n"); return 0; }
    moore = moore_bound();
    static Graph best, orig;
    if (!read_start(&best)) { printf("0 0\n"); return 0; }
    copy_graph(&orig, &best);
    while (now() < t_end) {
        grow_greedy(&best, t_end);
        if (now() >= t_end) break;
        if (best.n + 2 > moore) break;
        double slice = now() + 8.0;
        if (slice > t_end) slice = t_end;
        if (grow_two(&best, slice)) copy_graph(&best, &WK);
    }
    if (!is_valid(&best)) copy_graph(&best, &orig);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# PG(2,q) incidence (points 0..m-1, lines m..2m-1). For a point set S, every line
# holds at most s points of S and every point lies on at most s lines indexed by S,
# with s = d - q - 1. Add an A-vertex per P in S (joined to lines through P) and a
# B-vertex per j in S (joined to points on line j). Diameter 3, max degree q+1+s.
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
    """Old PG(2,q) incidence plus an A and a B vertex per element of S."""
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
        cands = [_greedy_arc(m, s, pl, lp, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if S and _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def known_start(d, D):
    """Closed-form optimal or record graph for (d, D), or None."""
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph, optimal
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

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = (fallback[0], fallback[1])

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.2 * time_limit, rng), key=lambda c: -c[0]):
            consider(cand)

    # Hand the best construction to C, which grows it.
    limit = lib.moore_bound(d, D)
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 1.0 and d <= 32 and best[0] < limit:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 8)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fallback[0], fallback[1])
    return best
