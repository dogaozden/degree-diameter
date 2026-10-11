"""Combined diameter-3 bipartite search.

Starts: arc-extended PG(2,q) incidence graphs, the conic twin blow-up of PG(2,q), the projective
plane or Araujo-Pardo-Lopez graph when they apply, and K_{d,d} as a fallback. The C engine
alternates two moves on the best graph:
  1. Augmentation: add one vertex on a random side, joined to spare-degree vertices of the other
     side chosen by greedy set cover. A vertex is accepted only if every vertex lies within
     distance D-1 of the chosen neighbours, which keeps the diameter at most D.
  2. Grow-by-two: add one vertex per side (joined to each other), move d-1 edges onto them, then
     anneal degree-preserving edge swaps until no pair is farther than D apart.
Python re-checks every returned graph with lib.is_valid and keeps the best valid one.
"""
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

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXDEG 64

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    unsigned char side[MAXN];
} Graph;

static int d, D;
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static uint64_t TA[MAXN * MAXW], TB[MAXN * MAXW];
static uint64_t BALL[MAXN * MAXW];
static int badv[MAXN];

/* Row v of the result holds every vertex within r steps of v. Returns the buffer used. */
static uint64_t *reach_rows(const Graph *g, int r, uint64_t *cur, uint64_t *nxt) {
    int n = g->n, W = (n + 63) / 64;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int round = 0; round < r; round++) {
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

/* Number of unordered pairs at distance > D; fills badv[v] with the per-vertex count. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *rows = reach_rows(g, D, RA, RB);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = rows + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

/* Balls of radius D-1 for every vertex, used by augmentation. */
static void recompute_ball(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *rows = reach_rows(g, D - 1, TA, TB);
    memcpy(BALL, rows, sizeof(uint64_t) * (size_t)n * W);
}

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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
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

/* Read "n m" and edges from stdin, 2-colour the graph, and check validity. n = 0 on failure. */
static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXDEG || g->deg[v] >= MAXDEG) {
            g->n = 0;
            return;
        }
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
                    g->side[u] = 1 - g->side[v];
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

/* K_{d,d}: valid for every D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Add one vertex on side X joined to spare-degree vertices on the other side that cover
 * every vertex within distance D-1. Returns 1 if the graph grew. */
static int try_add(Graph *g, int X) {
    int n = g->n, W = (n + 63) / 64;
    if (n + 1 > MAXN) return 0;
    uint64_t U[MAXW];
    int T[MAXDEG], nt = 0;
    static char sel[MAXN];
    memset(sel, 0, sizeof(char) * n);
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
    while (nt < d) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < n; v++) {
            if (g->side[v] == X || g->deg[v] >= d || sel[v]) continue;
            int c = 0;
            const uint64_t *b = BALL + (size_t)v * W;
            for (int w = 0; w < W; w++) c += __builtin_popcountll(b[w] & U[w]);
            if (c <= 0) continue;
            long sc = (long)c * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        const uint64_t *b = BALL + (size_t)best * W;
        for (int w = 0; w < W; w++) U[w] &= ~b[w];
    }
    if (nt == 0) return 0;
    for (int w = 0; w < W; w++)
        if (U[w]) return 0;
    int x = n;
    g->side[x] = (unsigned char)X;
    g->deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        g->adj[x][k] = T[k];
        g->adj[T[k]][g->deg[T[k]]++] = x;
    }
    g->n = n + 1;
    return 1;
}

/* Insert one vertex per side (joined to each other), move d-1 edges onto them, then anneal
 * degree-preserving swaps. Returns 1 with a valid graph in work on success. */
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
        if (used[b] == stamp) continue;
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

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    double t0 = now();
    t_end = t0 + budget * 0.96;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, cur, work;
    if (d < 1 || D < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0 && D >= 2 && 2 * d <= MAXN) complete_bipartite(&best);
    if (best.n == 0) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    copy_graph(&cur, &best);
    while (now() < t_end && best.n < moore) {
        recompute_ball(&cur);
        int fails = 0;
        while (now() < t_end && fails < 400 && cur.n + 1 <= MAXN) {
            if (try_add(&cur, rndint(2))) {
                fails = 0;
                recompute_ball(&cur);
            } else {
                fails++;
            }
        }
        if (cur.n > best.n && is_valid(&cur)) copy_graph(&best, &cur);
        if (now() >= t_end || cur.n + 2 > moore || cur.n + 2 > MAXN) break;
        double left = t_end - now();
        double slice = left < 3.0 ? left : 3.0;
        if (grow_once(&cur, &work, now() + slice)) {
            copy_graph(&cur, &work);
            if (cur.n > best.n) copy_graph(&best, &cur);
        }
    }
    if (!is_valid(&best) && D >= 2 && 2 * d <= MAXN) complete_bipartite(&best);
    print_graph(&best);
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
    """Randomized greedy point set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
    """Return (n, edges) candidates from PG(2, q) for each prime power q with q + 1 <= d."""
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


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd: duplicate each conic point and each dual-conic line once.

    Gives 2(q^2+q+1) + 2(q+1) vertices, which is 394 for q = 13 (d = 16).
    """
    q = d - 3
    if D < 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


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
    rng = random.Random(seed * 7919 + d)
    cands = []

    def consider(g):
        try:
            if g is not None and lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass

    if D >= 3:
        try:
            for g in _arc_extensions(d, t0 + 0.2 * time_limit, rng):
                consider(g)
        except Exception:
            pass
    consider(conic_blowup(d, D) if D >= 3 and d >= 6 else None)
    consider(lib.projective_plane_incidence(d - 1)
             if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1) else None)
    consider(lib.araujo_lopez_graph(d - 2)
             if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2) else None)
    consider(lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2

    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    if best[0] < lib.moore_bound(d, D):
        budget = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 0.5:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                 stdin_graph=best, timeout=budget + 5)
                out = lib.parse_graph_text(text)
                if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                    best = out
            except Exception:
                pass
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
