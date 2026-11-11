"""Bipartite d-regular random-lift search with SA repair, plus degree-preserving growth.

This version replaces the metacyclic lift family with a different construction. The C engine starts
from a uniformly random d-regular bipartite graph on the target order (no group structure) and
repairs it by simulated annealing over double-edge swaps. Each swap keeps every degree and the
bipartition, and the objective is the exact count of pairs at distance greater than D. Once a
target-order graph is valid, degree-preserving growth adds two vertices (one per side) and anneals
again, pushing the order past the record.

Python still builds the best algebraic start (PG(2,q), W(q), K_{d,d}) and checks it with
lib.is_valid. The C output is accepted only if it is valid and strictly larger than that start.
"""
import time
import itertools

import lib

C_SOURCE = r'''
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
#define MAXE (MAXN * MAXD / 2 + 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int u, v; } Edge;

static int d, D;
static long MOORE;
static double t_end;
static Edge E[MAXE];
static int M;
static int perm_buf[MAXN];
static int queue_buf[MAXN];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static Graph best, work, cur;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
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

/* Number of unordered pairs at distance > D, by bitset ball expansion. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *c = RA, *nx = RB;
    memset(c, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) c[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nx + (size_t)v * W;
            const uint64_t *src = c + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = c + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = c;
        c = nx;
        nx = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        const uint64_t *s = c + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(s[w]);
        total += n - cnt;
    }
    return total / 2;
}

static int check_valid(const Graph *g) {
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
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue_buf[tail++] = s;
        while (head < tail) {
            int v = queue_buf[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue_buf[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!check_valid(g)) g->n = 0;
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

/* Rebuild the flat edge list E (side-0 endpoint u, side-1 endpoint v) from g. */
static void rebuild_edges(const Graph *g) {
    M = 0;
    for (int u = 0; u < g->n; u++) {
        if (g->side[u] != 0) continue;
        for (int i = 0; i < g->deg[u]; i++) {
            if (M < MAXE) { E[M].u = u; E[M].v = g->adj[u][i]; M++; }
        }
    }
}

/* Uniform-ish random d-regular bipartite graph with h vertices per side:
 * d random perfect matchings, each one rejected if it repeats an existing edge. */
static int build_random(Graph *g, int h) {
    if (h < d || 2 * h > MAXN) return 0;
    g->n = 2 * h;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (v >= h); }
    for (int s = 0; s < d; s++) {
        int ok = 0;
        for (int tries = 0; tries < 5000 && !ok; tries++) {
            for (int i = 0; i < h; i++) perm_buf[i] = i;
            for (int i = h - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm_buf[i]; perm_buf[i] = perm_buf[j]; perm_buf[j] = t;
            }
            ok = 1;
            for (int i = 0; i < h && ok; i++)
                if (has_edge(g, i, h + perm_buf[i])) ok = 0;
            if (ok)
                for (int i = 0; i < h; i++) add_edge(g, i, h + perm_buf[i]);
        }
        if (!ok) return 0;
    }
    rebuild_edges(g);
    return 1;
}

/* Add one vertex per side, joined to each other, and move d-1 old edges onto them.
 * Degrees stay exactly d. Caller must give a copy, since a failed call leaves g modified. */
static int grow_from(Graph *g) {
    int n = g->n;
    if (n + 2 > MAXN || n + 2 > MOORE) return 0;
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    int x = n, y = n + 1;
    g->n = n + 2;
    g->deg[x] = 0;
    g->deg[y] = 0;
    g->side[x] = 0;
    g->side[y] = 1;
    add_edge(g, x, y);
    int k = 0;
    for (long tries = 0; k < d - 1 && tries < 1000000; tries++) {
        int a = rndint(n);
        if (g->side[a] != 0 || used[a] == stamp || g->deg[a] == 0) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(g, a, b);
        add_edge(g, x, b);
        add_edge(g, y, a);
        used[a] = stamp;
        used[b] = stamp;
        k++;
    }
    return k == d - 1;
}

/* Simulated annealing over degree-preserving double-edge swaps, minimising bad_pairs.
 * Keeps g and the edge list consistent on return. */
static long anneal(Graph *g, long bad, double until) {
    rebuild_edges(g);
    double T = 1.0;
    long it = 0;
    while (bad > 0 && M >= 2) {
        if ((++it & 7) == 0 && now() > until) break;
        int e1 = rndint(M), e2 = rndint(M);
        if (e1 == e2) continue;
        int a1 = E[e1].u, b1 = E[e1].v, a2 = E[e2].u, b2 = E[e2].v;
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(g, a1, b2) || has_edge(g, a2, b1)) continue;
        del_edge(g, a1, b1);
        del_edge(g, a2, b2);
        add_edge(g, a1, b2);
        add_edge(g, a2, b1);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            E[e1].v = b2;
            E[e2].v = b1;
        } else {
            del_edge(g, a1, b2);
            del_edge(g, a2, b1);
            add_edge(g, a1, b1);
            add_edge(g, a2, b2);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long target = (argc >= 6) ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD || 2 * d > MAXN) {
        printf("1 0\n");
        return 0;
    }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0 || !check_valid(&best)) complete_bipartite(&best);

    /* Phase A: random regular graph at the target order, annealed until valid. */
    long tgt = target;
    if (tgt % 2) tgt++;
    if (D >= 2 && tgt > best.n && tgt <= MOORE && tgt <= MAXN) {
        double endA = t0 + (t_end - t0) * 0.85;
        while (now() < endA && best.n < tgt) {
            double left = endA - now();
            double slice = left / 2;
            if (slice < 3.0) slice = left;
            if (!build_random(&cur, (int)(tgt / 2))) break;
            long bad = bad_pairs(&cur);
            bad = anneal(&cur, bad, now() + slice);
            if (bad == 0 && check_valid(&cur)) copy_graph(&best, &cur);
        }
    }

    /* Phase B: grow the current best by two vertices at a time, repairing with annealing. */
    while (D >= 2 && now() < t_end && best.n + 2 <= MOORE && best.n + 2 <= MAXN) {
        copy_graph(&work, &best);
        if (!grow_from(&work)) break;
        rebuild_edges(&work);
        long bad = bad_pairs(&work);
        bad = anneal(&work, bad, t_end);
        if (bad != 0 || !check_valid(&work)) break;
        copy_graph(&best, &work);
    }

    if (!check_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Targets for the random-regular phase (order to beat the record).
TARGETS = {(4, 8): 2186}


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = min(0.85 * time_limit, time_limit - 6.0) - (time.monotonic() - t0)
    if budget <= 1.0:
        return best
    target = max(TARGETS.get((d, D), 0), best[0] + 2)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, target],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
