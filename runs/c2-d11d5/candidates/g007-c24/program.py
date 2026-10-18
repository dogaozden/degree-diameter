"""Bold variant: random-regular bipartite starts annealed toward diameter D, with a
Python bi-Cayley lift search as the initial fallback. Every returned graph is checked with
lib.is_valid, and K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
/* Random-regular annealing engine.
 * Usage:  prog d D seed time_limit [s_guess] < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0" (then K_{d,d} is the start).
 * stdout: "n m" + edges of the best valid graph found (never worse than the start).
 *
 * Phase moves: (a) a random d-regular bipartite graph on s+s vertices is annealed with
 * degree-preserving 2-switches until every pair is within distance D; (b) a small
 * growth from the current best (inserting one vertex pair with d-1 switches) is annealed.
 * Every accepted graph is re-verified with is_valid before it becomes the best.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int a, b, c, e; } Move;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static int P[MAXD][MAXN / 2];
static int markv[MAXN / 2];
static int mark_stamp = 0;
static int used[MAXN];
static int used_stamp = 0;
static double t_end;
static Graph gbest, gwork;

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

/* Number of unordered pairs at distance > D; also sets badv[v]. */
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

static void build_complete(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v < d ? 0 : 1; }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) add_edge(g, i, d + j);
}

static int dup_count(int s) {
    int c = 0;
    for (int i = 0; i < s; i++) {
        mark_stamp++;
        for (int l = 0; l < d; l++) {
            int b = P[l][i];
            if (markv[b] == mark_stamp) c++;
            else markv[b] = mark_stamp;
        }
    }
    return c;
}

/* Random d-regular simple bipartite graph with s vertices per side. */
static int build_random(Graph *g, int s) {
    if (s < d || 2 * s > MAXN) return 0;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < s; i++) P[l][i] = i;
        for (int i = s - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i]; P[l][i] = P[l][j]; P[l][j] = t;
        }
    }
    int cur = dup_count(s);
    for (long it = 0; cur > 0 && it < 20000; it++) {
        int l = rndint(d), i = rndint(s), j = rndint(s);
        if (i == j || P[l][i] == P[l][j]) continue;
        int t = P[l][i]; P[l][i] = P[l][j]; P[l][j] = t;
        int nw = dup_count(s);
        if (nw <= cur) cur = nw;
        else { t = P[l][i]; P[l][i] = P[l][j]; P[l][j] = t; }
    }
    if (cur > 0) return 0;
    g->n = 2 * s;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v < s ? 0 : 1; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < s; i++) add_edge(g, i, s + P[l][i]);
    return 1;
}

/* Insert one vertex pair (x side 0, y side 1, joined) using d-1 degree-preserving switches. */
static void grow_one(Graph *w) {
    int n = w->n;
    if (n + 2 > MAXN) return;
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = 0; w->deg[y] = 0;
    w->side[x] = 0; w->side[y] = 1;
    add_edge(w, x, y);
    used_stamp++;
    used[x] = used_stamp; used[y] = used_stamp;
    int k = 0;
    for (long tries = 0; k < d - 1 && tries < 200000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == used_stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (b >= n || used[b] == used_stamp) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used_stamp; used[b] = used_stamp;
        k++;
    }
}

static int rnd_side0(const Graph *g) {
    int v;
    do v = rndint(g->n); while (g->side[v] != 0);
    return v;
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b), with a,c on side 0. */
static int random_move(Graph *g, Move *m, int biased) {
    int v = rndint(g->n);
    if (biased)
        for (int t = 0; t < 30 && badv[v] == 0; t++) v = rndint(g->n);
    int a, b;
    if (g->side[v] == 0) {
        a = v;
        if (g->deg[a] == 0) return 0;
        b = g->adj[a][rndint(g->deg[a])];
    } else {
        b = v;
        if (g->deg[b] == 0) return 0;
        a = g->adj[b][rndint(g->deg[b])];
    }
    int c = rnd_side0(g);
    if (c == a || g->deg[c] == 0) return 0;
    int e = g->adj[c][rndint(g->deg[c])];
    if (e == b) return 0;
    if (has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    m->a = a; m->b = b; m->c = c; m->e = e;
    del_edge(g, a, b);
    del_edge(g, c, e);
    add_edge(g, a, e);
    add_edge(g, c, b);
    return 1;
}

static void undo_move(Graph *g, const Move *m) {
    del_edge(g, m->a, m->e);
    del_edge(g, m->c, m->b);
    add_edge(g, m->a, m->b);
    add_edge(g, m->c, m->e);
}

/* Simulated annealing on the bad-pair count. Returns 1 iff g ends valid. */
static int anneal(Graph *g, double until, long max_it) {
    long bad = bad_pairs(g);
    double T = 0.7;
    for (long it = 0; bad > 0 && it < max_it; it++) {
        if (now() > until) break;
        Move mv;
        if (!random_move(g, &mv, 1)) continue;
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            undo_move(g, &mv);
        }
        T *= 0.9995;
        if (T < 0.2) T = 0.7;
    }
    return bad == 0 && is_valid(g);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [s_guess] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int s_guess = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) build_complete(&gbest);

    int max_s = MAXN / 2;
    long mb = moore_bound() / 2;
    if (mb < max_s) max_s = (int)mb;
    if (s_guess > max_s) s_guess = max_s;

    int lo = gbest.n / 2;
    int cap = lo / 10 > 1 ? lo / 10 : 1;
    int gap = cap;
    int fails = 0, first = 1;

    while (fails < 4 && now() < t_end - 0.5) {
        int try_s, random_mode;
        if (first && s_guess > lo) {
            try_s = s_guess;
            random_mode = 1;
        } else {
            try_s = lo + gap;
            random_mode = gap > 8;
        }
        first = 0;
        if (try_s > max_s) break;

        int ok_build = 1;
        if (random_mode) {
            ok_build = build_random(&gwork, try_s);
        } else {
            copy_graph(&gwork, &gbest);
            for (int k = 0; k < gap; k++) grow_one(&gwork);
        }
        if (!ok_build) { fails++; continue; }

        double remaining = t_end - now();
        double slice = remaining * 0.3;
        if (slice < 2.0) slice = remaining;
        double until = now() + slice;
        if (until > t_end) until = t_end;

        if (anneal(&gwork, until, 1L << 40)) {
            copy_graph(&gbest, &gwork);
            lo = gwork.n / 2;
            cap = lo / 10 > 1 ? lo / 10 : 1;
            gap = gap * 2 < cap ? gap * 2 : cap;
            if (gap < 1) gap = 1;
            fails = 0;
        } else {
            fails++;
            gap = gap / 2 > 1 ? gap / 2 : 1;
        }
    }

    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (Python + numpy search).
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) with Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when block representative b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Phase 1: short bi-Cayley lift search (gives the start graph and a safe fallback).
    lift_frac = 0.2 if D >= 5 else 0.5
    lift_deadline = t0 + lift_frac * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < lift_deadline:
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C random-regular annealing, grown from the best graph found so far.
    remaining = final - time.monotonic() - 2.0
    if remaining > 2.0 and best_n > 2 * d:
        try:
            s_guess = int(0.27 * lib.moore_bound(d, D) / 2)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), s_guess],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
