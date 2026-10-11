"""Bi-Cayley and voltage-lift search with a fresh C grow engine.

Construction: for each target (d, D), build the best algebraic start (K_{d,d}, PG(2,q), the
Araujo-Pardo-Lopez graph, or the W(q) incidence graph). Then search Python-side for
regular bipartite lifts with fibre count p in {1,2,3} over semidirect groups Z_m x| Z_k, scoring
each voltage assignment by an orbit-reduced diameter count: BFS only from the 2p fibre
representatives. The lift search is a different family from the earlier hill-climb (it uses
fibre count p = 2, 3 and Python-side scoring), and it can reach orders like 4N with N prime,
which the cyclic-only lifts miss. Finally a small C engine grows the best graph by two vertices
at a time with bad-pair annealing and saturation. Every returned graph is checked by lib.is_valid,
and the fallback is always a valid graph.
"""
import itertools
import math
import random
import time
from collections import deque

import lib

C_SOURCE = r'''
/* Grow-by-two annealing with saturation for bipartite degree-diameter graphs.
 * Usage: prog d D seed time_limit < start_graph
 * stdin: "n m" then m lines "u v", or "0 0". stdout: "n m" then edges.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
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

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Returns the number of unordered pairs at distance > D; fills badv[v]. */
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
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Adding an edge between opposite sides never increases a distance. */
static void saturate(Graph *g) {
    for (int pass = 0; pass < 4; pass++) {
        int added = 0;
        for (int v = 0; v < g->n; v++) {
            for (int t = 0; t < 200 && g->deg[v] < d; t++) {
                int u = rndint(g->n);
                if (u == v || g->side[u] == g->side[v] || g->deg[u] >= d || has_edge(g, v, u))
                    continue;
                add_edge(g, v, u);
                added++;
            }
        }
        if (!added) break;
    }
}

static int list_buf[MAXN];
static int pick_bad_vertex(const Graph *g) {
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list_buf[c++] = v;
    if (!c) return -1;
    return list_buf[rndint(c)];
}

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
        int v;
        if (rnd01() < 0.8) {
            v = pick_bad_vertex(work);
            if (v < 0) v = rndint(work->n);
        } else {
            v = rndint(work->n);
        }
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
            bad_pairs(work);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) {
            saturate(&work);
            copy_graph(best, &work);
        }
    }
}

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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2) grow_search(&best, t_end);

    static Graph sat;
    copy_graph(&sat, &best);
    saturate(&sat);
    if (is_valid(&sat)) copy_graph(&best, &sat);

    print_graph(&best);
    return 0;
}
'''


# ------------------------------------------------------------ algebraic starts

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


# ------------------------------------------------------------ lift search

_GROUP_CACHE = {}


def _group_table(m, k, r):
    """Multiplication table M[x][y] of Z_m x| Z_k (identity is element 0)."""
    key = (m, k, r)
    if key not in _GROUP_CACHE:
        order, mul, _inv = lib.semidirect_group(m, k, r)
        _GROUP_CACHE[key] = [[mul(x, y) for y in range(order)] for x in range(order)]
    return _GROUP_CACHE[key]


def _groups_of_order(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving all Z_m x| Z_k of order N."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _lift_bad(p, N, M, darts, D):
    """Count (representative, vertex) pairs at distance > D; zero iff the lift has diameter <= D.

    Vertex (fibre f, element x) has id f*N + x. The A fibres are 0..p-1, the B fibres p..2p-1.
    Dart (i, j, g) joins (i, x) to (p + j, M[x][g]). Left multiplication by the group is an
    automorphism, so BFS from (f, 0) for each fibre f is enough.
    """
    V = 2 * p * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = (p + j) * N + M[x][g]
            adj[a].append(b)
            adj[b].append(a)
    bad = 0
    for s in range(0, V, N):
        dist = [-1] * V
        dist[s] = 0
        q = deque([s])
        seen = 1
        while q:
            v = q.popleft()
            dv = dist[v]
            if dv >= D:
                continue
            for u in adj[v]:
                if dist[u] < 0:
                    dist[u] = dv + 1
                    q.append(u)
                    seen += 1
        bad += V - seen
    return bad


def _score(p, N, M, darts, D):
    if len(set(darts)) != len(darts):  # duplicate darts would create parallel edges
        return 10 ** 9
    return _lift_bad(p, N, M, darts, D)


def _try_lift(p, N, M, d, D, steps, rng, deadline):
    """Hill-climb the voltages of a random d-regular base on p + p fibres. Returns darts or None."""
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            darts.append((i, perm[i], rng.randrange(N)))
    cur = _score(p, N, M, darts, D)
    for _ in range(steps):
        if cur == 0 or time.monotonic() > deadline:
            break
        t = rng.randrange(len(darts))
        i, j, g_old = darts[t]
        darts[t] = (i, j, rng.randrange(N))
        new = _score(p, N, M, darts, D)
        if new <= cur or rng.random() < 0.01:
            cur = new
        else:
            darts[t] = (i, j, g_old)
    return list(darts) if cur == 0 else None


def _lift_edges(p, N, M, darts):
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (p + j) * N + M[x][g]))
    return 2 * p * N, edges


def _lift_search(d, D, best, rng, deadline):
    """Search regular lifts of order 2pN strictly larger than best. Returns the best (n, edges)."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        p = rng.choice([1, 1, 2, 2, 3])
        target = best[0] + 2
        Nmin = -(-target // (2 * p))
        N = Nmin + rng.randrange(3)
        if N < 2 or 2 * p * N > moore:
            continue
        groups = _groups_of_order(N)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        M = _group_table(m, k, r)
        for _ in range(2):
            darts = _try_lift(p, N, M, d, D, 600, rng, deadline)
            if darts:
                n, edges = _lift_edges(p, N, M, darts)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                break
    return best


# ------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    usable = 0.85 * time_limit - 1.0
    rng = random.Random(seed)
    try:
        best = _lift_search(d, D, best, rng, t0 + 0.5 * usable)
    except Exception:
        pass

    budget = t0 + usable - time.monotonic()
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                             stdin_graph=best, timeout=budget + 4)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
