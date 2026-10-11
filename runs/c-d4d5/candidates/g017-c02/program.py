"""Bold variant: lift-based search from a known diameter-D start.

The base graph is the largest valid algebraic start (W(q), PG(2,q), Araujo-Pardo-Lopez, or K_{d,d}).
The C engine treats that whole base graph as a template and searches for voltage lifts over Z_m
(m = 2, 3, ...). Lifts have m * |base| vertices and keep the base degree. A spanning tree of the base
gets voltage 0, which is WLOG. The diameter check is orbit-reduced: BFS only from the base
representatives (w, 0). Any lift that passes is then grown by two vertices at a time with annealed
edge swaps, as in the parent. Python keeps the largest valid start as a fallback, and every
returned graph is checked with lib.is_valid.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Voltage-lift search over an arbitrary simple bipartite base graph.
 * Usage:   prog d D seed time_limit [mmax]   < base_graph
 * stdin:   "n m" then m lines "u v" (simple bipartite, max degree <= d).
 * stdout:  "n m" then m lines "u v": the largest valid graph found (the base itself if nothing better).
 *
 * 1. For m = 2, 3, ... (up to mmax and the Moore bound), anneal Z_m voltages on the non-tree base
 *    edges until every pair in the lift is within distance D. The lift has m * n_base vertices.
 * 2. Orbit reduction: translation by Z_m is an automorphism, so BFS from (w, 0) for each base w
 *    covers all pairs.
 * 3. Grow by two vertices with degree-preserving annealed swaps, using the remaining time.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 8
#define MAXB 512
#define MAXBE 2100
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D, gm;
static double t_end, span;

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (bitset BFS). */
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

/* ---- base graph ---- */
static int bn, be;
static int bu[MAXBE], bv[MAXBE], tree_e[MAXBE], vol[MAXBE], freeidx[MAXBE], nfree;
static unsigned char bside[MAXB];

/* Reads the base, checks it is simple and bipartite, and records a spanning forest. */
static int load_base(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXB || m < 0 || m > MAXBE) return 0;
    static int eu[MAXBE], ev[MAXBE], bae[MAXB][MAXD];
    int deg[MAXB], fill[MAXB], side[MAXB], queue[MAXB];
    for (int v = 0; v < n; v++) { deg[v] = 0; fill[v] = 0; side[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        eu[i] = u;
        ev[i] = v;
        if (++deg[u] > d || ++deg[v] > d) return 0;
    }
    for (int i = 0; i < m; i++)
        for (int j = 0; j < i; j++)
            if ((eu[i] == eu[j] && ev[i] == ev[j]) || (eu[i] == ev[j] && ev[i] == eu[j])) return 0;
    for (int i = 0; i < m; i++) {
        bae[eu[i]][fill[eu[i]]++] = i;
        bae[ev[i]][fill[ev[i]]++] = i;
    }
    for (int e = 0; e < m; e++) tree_e[e] = 0;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int k = 0; k < fill[v]; k++) {
                int e = bae[v][k];
                int u = eu[e] == v ? ev[e] : eu[e];
                if (side[u] == -1) {
                    side[u] = 1 - side[v];
                    tree_e[e] = 1;
                    queue[tail++] = u;
                } else if (side[u] == side[v]) {
                    return 0;
                }
            }
        }
    }
    bn = n;
    be = m;
    for (int v = 0; v < n; v++) bside[v] = (unsigned char)side[v];
    for (int i = 0; i < m; i++) {
        if (side[eu[i]] == 0) { bu[i] = eu[i]; bv[i] = ev[i]; }
        else { bu[i] = ev[i]; bv[i] = eu[i]; }
        vol[i] = 0;
    }
    return 1;
}

static void base_to_graph(Graph *g) {
    g->n = bn;
    for (int v = 0; v < bn; v++) {
        g->deg[v] = 0;
        g->side[v] = bside[v];
    }
    for (int e = 0; e < be; e++) add_edge(g, bu[e], bv[e]);
}

static Graph best, L, work;
static int dist_b[MAXN], q_b[MAXN];

/* Lift with current voltages vol[] over Z_gm. Vertex (u, g) = u*gm + g. */
static void build_lift(void) {
    L.n = bn * gm;
    for (int v = 0; v < L.n; v++) {
        L.deg[v] = 0;
        L.side[v] = bside[v / gm];
    }
    for (int e = 0; e < be; e++)
        for (int g = 0; g < gm; g++)
            add_edge(&L, bu[e] * gm + g, bv[e] * gm + (g + vol[e]) % gm);
}

/* Orbit-reduced count of lift pairs at distance > D. Zero iff the lift has diameter <= D. */
static long orbit_bad(void) {
    long total = 0;
    int nv = L.n;
    for (int w = 0; w < bn; w++) {
        int src = w * gm;
        for (int v = 0; v < nv; v++) dist_b[v] = -1;
        int head = 0, tail = 0;
        dist_b[src] = 0;
        q_b[tail++] = src;
        while (head < tail) {
            int v = q_b[head++];
            if (dist_b[v] >= D) continue;
            for (int i = 0; i < L.deg[v]; i++) {
                int u = L.adj[v][i];
                if (dist_b[u] < 0) {
                    dist_b[u] = dist_b[v] + 1;
                    q_b[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Simulated annealing on the free voltages. Returns the final bad count; L matches vol[] on return. */
static long anneal(double until, long steps) {
    build_lift();
    long bad = orbit_bad();
    double T = 1.0;
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int f = freeidx[rndint(nfree)];
        int old = vol[f];
        vol[f] = (old + 1 + rndint(gm - 1)) % gm;
        build_lift();
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else vol[f] = old;
        T *= 0.999;
        if (T < 0.1) T = 1.0;
    }
    build_lift();
    return bad;
}

static int search_m(int m, double until) {
    gm = m;
    nfree = 0;
    for (int e = 0; e < be; e++) {
        if (tree_e[e]) vol[e] = 0;
        else freeidx[nfree++] = e;
    }
    if (nfree == 0) return 0;
    while (now() < until) {
        for (int k = 0; k < nfree; k++) vol[freeidx[k]] = rndint(m);
        long bad = anneal(until, 4000);
        if (bad == 0) {
            build_lift();
            if (is_valid(&L)) return 1;
        }
    }
    return 0;
}

/* Adds two vertices x (side 0) and y (side 1) with rewiring, then anneals degree-preserving swaps. */
static int grow_once(const Graph *b, Graph *w, double until) {
    int n = b->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(w, b);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int bb = w->adj[a][rndint(w->deg[a])];
        if (used[bb] == stamp || bb >= n) continue;
        del_edge(w, a, bb);
        add_edge(w, x, bb);
        add_edge(w, y, a);
        used[a] = used[bb] = stamp;
        k++;
    }
    long bad = bad_pairs(w);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(w->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(w->n);
        if (w->deg[v] == 0) continue;
        int u = w->adj[v][rndint(w->deg[v])];
        int s = rndint(w->n);
        if (w->side[s] != w->side[v] || s == v || w->deg[s] == 0) continue;
        int t = w->adj[s][rndint(w->deg[s])];
        if (t == u || has_edge(w, v, t) || has_edge(w, s, u)) continue;
        del_edge(w, v, u);
        del_edge(w, s, t);
        add_edge(w, v, t);
        add_edge(w, s, u);
        long nb = bad_pairs(w);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(w, v, t);
            del_edge(w, s, u);
            add_edge(w, v, u);
            add_edge(w, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    if (!is_valid(w)) return 0;
    return 1;
}

static void grow_search(Graph *b, double until) {
    while (now() < until && b->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(b, &work, now() + slice)) copy_graph(b, &work);
    }
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

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [mmax] < base_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mmax = argc > 5 ? atoi(argv[5]) : 4;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    span = t_end - t0;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD || !load_base()) {
        printf("0 0\n");
        return 0;
    }
    base_to_graph(&best);
    if (!is_valid(&best)) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long mm = moore / bn;
    if (mm > mmax) mm = mmax;
    if (mm * bn > MAXN) mm = MAXN / bn;
    for (int m = 2; m <= mm; m++) {
        double until = t0 + (m == 2 ? 0.45 : 0.75) * span;
        if (now() >= until) break;
        if (search_m(m, until) && L.n > best.n && is_valid(&L)) copy_graph(&best, &L);
    }
    grow_search(&best, t_end);
    if (!is_valid(&best)) {
        printf("0 0\n");
        return 0;
    }
    print_graph(&best);
    return 0;
}
'''


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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 8 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 4],
                         stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
