"""Combined program, v3 (bold change for the weak d=3, D=9 case).

The previous version spent its budget on exhaustive or random sampling of bi-Cayley graphs
from small orders upward, plus voltage lifts and grow-by-two. This version replaces that
search with simulated annealing over the voltages of bi-Cayley graphs on metacyclic groups
Z_m x|_r Z_k. It jumps straight to the order that would beat the current best (2N > best.n)
and scores a candidate by its deficit: the number of vertices farther than D from a_e and
from b_e. Two BFS runs per evaluation are enough, because G acts regularly on each side. A
zero deficit gives a diameter-D graph, which is then re-checked by lib.is_valid.

Risk: this is a different search than the parent's, and it may not reach the parent's 506
for d=3, D=9. The parent's C source is not kept, so this is a regression risk on that case.
The fallback is still valid: the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or
K_{d,d}), checked with lib.is_valid.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bi-Cayley simulated-annealing search, v3.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * A-vertex x ~ B-vertex x*g_t (t = 0..d-1, g_0 = e), in a group G = Z_m x|_r Z_k.
 * Deficit = (# vertices farther than D from a_e) + (# farther than D from b_e).
 * Zero deficit implies diameter <= D, because G acts regularly on both sides.
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
#define MAXTRI 40000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;

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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
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

/* Number of unordered pairs at distance > D, by bitset expansion. */
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
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
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

/* ---------------------------------------------------------- groups */

/* Z_m x|_r Z_k, element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct { int m, k, r; } Tri;

static Tri tris[MAXTRI];
static int ntri;

static int GM, GK, NN;
static int rp[MAXN];           /* rp[b] = r^b mod m for the current group */
static int fwd[MAXD][MAXN];    /* fwd[t][x] = x * g_t */
static int bwd[MAXD][MAXN];    /* bwd[t][y] = y * g_t^{-1} */
static int gv[MAXD];           /* current voltages */

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

/* Inverse of (a, b) is (-r^{-b} a, -b); r^k = 1 mod m so r^{-b} = r^{k-b}. */
static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long c = (GM - ((long)rp[nb] * a) % GM) % GM;
    return (int)(c * GK + nb);
}

static void set_group(Tri t) {
    GM = t.m; GK = t.k; NN = GM * GK;
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * t.r % GM);
}

/* All semidirect groups of order N, one entry per (m, r) with k = N / m. */
static void list_groups(int N) {
    ntri = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ntri < MAXTRI) {
                tris[ntri].m = m; tris[ntri].k = k; tris[ntri].r = r;
                ntri++;
            }
        }
    }
}

static void set_volt(int t, int g) {
    gv[t] = g;
    int gi = ginv(g);
    for (int x = 0; x < NN; x++) {
        fwd[t][x] = gmul(x, g);
        bwd[t][x] = gmul(x, gi);
    }
}

/* Distinct voltages with g_0 = e (WLOG, by right translation). */
static void random_voltages(int nd) {
    set_volt(0, 0);
    for (int t = 1; t < nd; t++) {
        int g;
        for (;;) {
            g = rndint(NN);
            int ok = 1;
            for (int u = 0; u < t; u++)
                if (gv[u] == g) { ok = 0; break; }
            if (ok) break;
        }
        set_volt(t, g);
    }
}

/* ------------------------------------------- bi-Cayley deficit and search */

/* Vertices: A-vertex x -> x, B-vertex y -> N + y. */
static int dist_a[2 * MAXN], qbuf[2 * MAXN];

static int reach_from(int N, int nd, int src) {
    int nv = 2 * N;
    for (int v = 0; v < nv; v++) dist_a[v] = -1;
    int head = 0, tail = 0;
    dist_a[src] = 0;
    qbuf[tail++] = src;
    while (head < tail) {
        int v = qbuf[head++];
        if (dist_a[v] >= D) continue;
        int dv = dist_a[v] + 1;
        if (v < N) {
            for (int t = 0; t < nd; t++) {
                int u = N + fwd[t][v];
                if (dist_a[u] < 0) { dist_a[u] = dv; qbuf[tail++] = u; }
            }
        } else {
            int y = v - N;
            for (int t = 0; t < nd; t++) {
                int u = bwd[t][y];
                if (dist_a[u] < 0) { dist_a[u] = dv; qbuf[tail++] = u; }
            }
        }
    }
    return tail;
}

static int deficit(int N, int nd) {
    return 4 * N - reach_from(N, nd, 0) - reach_from(N, nd, N);
}

static int anneal(int N, int nd, int steps, double until) {
    int cur = deficit(N, nd);
    if (cur == 0) return 1;
    for (int s = 0; s < steps; s++) {
        if ((s & 127) == 0 && now() > until) return 0;
        double T = 1.5 * (1.0 - (double)s / steps) + 0.05;
        int t = 1 + rndint(nd - 1);
        int old = gv[t];
        int g;
        for (;;) {
            g = rndint(NN);
            int ok = 1;
            for (int u = 0; u < nd; u++)
                if (u != t && gv[u] == g) { ok = 0; break; }
            if (ok) break;
        }
        set_volt(t, g);
        int nw = deficit(N, nd);
        int df = nw - cur;
        if (df <= 0 || rnd01() < exp(-(double)df / T)) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            set_volt(t, old);
        }
    }
    return 0;
}

static void build_from_volt(Graph *g, int N, int nd) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < nd; t++)
            add_edge(g, x, N + fwd[t][x]);
}

static void bc_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int nd = d;
    while (now() < until) {
        int target = best->n / 2 + 1;
        if (target < nd + 1) target = nd + 1;
        int N = target;
        if (rndint(3) == 0) N += rndint(3);
        if ((long)2 * N > moore || 2 * N > MAXN) {
            N = target;
            if ((long)2 * N > moore || 2 * N > MAXN) break;
        }
        list_groups(N);
        if (ntri == 0) continue;
        set_group(tris[rndint(ntri)]);
        random_voltages(nd);
        if (anneal(N, nd, 4000, until)) {
            build_from_volt(&cand, N, nd);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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
    double t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (d >= 2 && D >= 2 && best.n < moore_bound())
        bc_search(&best, t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
