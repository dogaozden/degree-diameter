"""Bold variant for the weakest parent case: random-start annealing instead of algebraic lifts.

Python supplies the best known start (or K_{d,d}) and runs the C engine under a fixed budget.
C works in two alternating modes at order n+2:
  * grow: insert one vertex per side into the best valid graph (degree-preserving splits),
  * fresh: a random d-regular bipartite graph on p+p vertices (p = best/2 + 1), built from
    d random perfect matchings with no repeated edges.
Each candidate is then annealed with degree-preserving edge swaps to minimise the number of
vertex pairs at distance > D. Only zero-cost graphs replace the best. The fallback is always
the best valid graph seen so far, so a failed search can only return the start graph.
"""
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
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXH (MAXN / 2)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} G;

static int d, D;
static double t_end;
static uint64_t R1[MAXN * MAXW], R2[MAXN * MAXW];
static unsigned char MM[MAXH * MAXH];
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

static int has_e(const G *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void del_h(G *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void add_e(G *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_e(G *g, int u, int v) {
    del_h(g, u, v);
    del_h(g, v, u);
}

/* Number of unordered pairs at distance > D. Zero means diameter <= D (and connected). */
static long bad_pairs(const G *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
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
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const G *g) {
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

/* Read "n m" and edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
static void read_start(G *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 2;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD || has_e(g, u, v)) {
            g->n = 0;
            return;
        }
        add_e(g, u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 2) continue;
        int h = 0, t = 0;
        g->side[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 2) {
                    g->side[u] = 1 - g->side[v];
                    q[t++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const G *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(G *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_e(g, a, d + b);
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

/* Grow a valid graph by two vertices x (side 0), y (side 1), joined to each other.
 * Each old vertex is touched by at most one split, so the degrees stay <= d. */
static int grow_from(const G *best, G *work) {
    int n = best->n;
    if (n + 2 > MAXN) return 0;
    *work = *best;
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_e(work, x, y);
    static unsigned char used[MAXN];
    memset(used, 0, sizeof used);
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b]) continue;
        del_e(work, a, b);
        add_e(work, x, b);
        add_e(work, y, a);
        used[a] = used[b] = 1;
        k++;
    }
    return 1;
}

/* Random d-regular bipartite graph on p + p vertices, from d random perfect matchings
 * with no repeated edge. */
static int fresh_graph(G *g, int p) {
    static int perm[MAXH];
    if (p < d || p > MAXH) return 0;
    memset(MM, 0, (size_t)p * p);
    for (int layer = 0; layer < d; layer++) {
        int ok = 0;
        for (int tries = 0; tries < 2000 && !ok; tries++) {
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            ok = 1;
            for (int i = 0; i < p && ok; i++)
                if (MM[i * p + perm[i]]) ok = 0;
            if (ok)
                for (int i = 0; i < p; i++) MM[i * p + perm[i]] = 1;
        }
        if (!ok) return 0;
    }
    g->n = 2 * p;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= p;
    }
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            if (MM[i * p + j]) add_e(g, i, p + j);
    return 1;
}

static int pick_side0(const G *g) {
    for (;;) {
        int v = rndint(g->n);
        if (g->side[v] == 0 && g->deg[v] > 0) return v;
    }
}

/* Simulated annealing over degree-preserving edge swaps, minimising bad_pairs.
 * Returns 1 when the graph has diameter <= D; otherwise stops at 'until'. */
static int anneal(G *g, double until, long *out_bad) {
    int any = 0;
    for (int v = 0; v < g->n; v++)
        if (g->side[v] == 0 && g->deg[v] > 0) {
            any = 1;
            break;
        }
    if (!any) return 0;
    long bad = bad_pairs(g);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) break;
        int a1 = pick_side0(g), a2 = pick_side0(g);
        if (a1 == a2) continue;
        int b1 = g->adj[a1][rndint(g->deg[a1])];
        int b2 = g->adj[a2][rndint(g->deg[a2])];
        if (b1 == b2 || has_e(g, a1, b2) || has_e(g, a2, b1)) continue;
        del_e(g, a1, b1);
        del_e(g, a2, b2);
        add_e(g, a1, b2);
        add_e(g, a2, b1);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_e(g, a1, b2);
            del_e(g, a2, b1);
            add_e(g, a1, b1);
            add_e(g, a2, b2);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    *out_bad = bad;
    return bad == 0;
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
    t_end = t0 + limit * 0.9 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    static G best, cur;
    if (d < 1 || D < 1 || d > MAXD || 2 * d > MAXN) {
        printf("1 0\n");
        return 0;
    }
    if (D == 1) {
        printf("2 1\n0 1\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    int attempt = 0;
    while (best.n + 2 <= moore && best.n + 2 <= MAXN && now() < t_end) {
        double left = t_end - now();
        double slice = left < 10.0 ? left : 10.0;
        int ok;
        if ((attempt++ & 1) == 0)
            ok = grow_from(&best, &cur);
        else
            ok = fresh_graph(&cur, best.n / 2 + 1);
        if (!ok) continue;
        long bad = 0;
        if (anneal(&cur, now() + slice, &bad) && cur.n > best.n && is_valid(&cur))
            best = cur;
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _fallback(d, D):
    """Always-valid simple graph used when nothing better exists."""
    if D == 1:
        return (2, [(0, 1)])
    return lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is not None and not lib.is_valid(*start, d, D):
        start = None
    best = start if start is not None else _fallback(d, D)
    if not lib.is_valid(*best, d, D):
        best = (1, [])
    if best[0] >= lib.moore_bound(d, D):
        return best   # already a Moore graph; nothing to search for

    elapsed = time.monotonic() - t0
    budget = 0.82 * time_limit - elapsed - 1.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 4.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass   # keep the valid fallback
    return best
