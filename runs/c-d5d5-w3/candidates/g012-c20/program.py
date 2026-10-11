"""Bi-Cayley search in C, then grow-by-two annealing.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.

This version replaces the voltage-lift search with a different construction. A bi-Cayley graph
over a finite group G of order g has parts G x {0} and G x {1}. Vertex (x,0) joins (x*s,1) for
each s in a d-element set S. Left multiplication is an automorphism that preserves sides, so the
diameter is <= D iff BFS of depth D from (e,0) and from (e,1) reaches everything. Each candidate
therefore costs two BFS runs. Groups are sampled from cyclic, abelian Z_a x Z_b, and semidirect
Z_m x| Z_k families (dihedral groups are the k = 2 case). The search climbs the group order one
step at a time, which gives orders 2g with g just above the current best half-order.

After the bi-Cayley phase, the C engine grows the best graph by two vertices per side and
anneals degree-preserving edge swaps. Every output is checked in C and again in Python, and the
start graph is kept as the fallback.

Risk: this family may fall below the best lift-based graphs for some (d, D). If the output is
not larger than the start, Python returns the start.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley degree-diameter search.
 *
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" then m lines "u v" (valid start), or "0 0".
 * stdout: "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (bi-Cayley): for group order g, pick a random group table (cyclic, Z_a x Z_b, or
 *   Z_m x| Z_k), choose a d-set S, and anneal S on the number of unreached pairs from (e,0) and
 *   (e,1). Graph: vertex g (side 0) to vertex G+(g*s) (side 1) for s in S.
 * Phase 2 (grow by two): add one vertex per side and anneal degree-preserving swaps.
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
#define MAXG 1024
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_stop;

/* ------------------------------------------------------------ utilities */

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

static int gcd(int a, int b) {
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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. */
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

static int G;                 /* current group order */
static int GT[MAXG][MAXG];    /* multiplication table; identity is 0 */
static int GINV[MAXG];

static void finish_group(void) {
    for (int x = 0; x < G; x++) {
        GINV[x] = 0;
        for (int y = 0; y < G; y++)
            if (GT[x][y] == 0) { GINV[x] = y; break; }
    }
}

static void build_cyclic(int g) {
    G = g;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++) GT[x][y] = (x + y) % G;
    finish_group();
}

/* Z_a x Z_b, element x = x1*b + y1. */
static void build_abelian(int a, int b) {
    G = a * b;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            GT[x][y] = ((x / b + y / b) % a) * b + (x % b + y % b) % b;
    finish_group();
}

/* Z_m x|_r Z_k, element a*k + b, (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2). */
static void build_semi(int m, int k, int r) {
    G = m * k;
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int j = 1; j < k; j++) rp[j] = (int)((long)rp[j - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < G; y++) {
            int a2 = y / k, b2 = y % k;
            GT[x][y] = (int)(((long)a1 + (long)rp[b1] * a2) % m) * k + (b1 + b2) % k;
        }
    }
    finish_group();
}

/* Random group of order gt from the three families (cyclic fallback). */
static void sample_group(int gt) {
    int t = rndint(3);
    if (t == 1) {
        int divs[64], nd = 0;
        for (int a = 2; a * 2 <= gt && nd < 64; a++)
            if (gt % a == 0) divs[nd++] = a;
        if (nd > 0) {
            int a = divs[rndint(nd)];
            build_abelian(a, gt / a);
            return;
        }
    } else if (t == 2) {
        int ms[64], nm = 0;
        for (int m = 2; m * 2 <= gt && nm < 64; m++)
            if (gt % m == 0) ms[nm++] = m;
        for (int tries = 0; tries < 40 && nm > 0; tries++) {
            int m = ms[rndint(nm)];
            int k = gt / m;
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) == 1 && powmod(r, k, m) == 1 % m) {
                build_semi(m, k, r);
                return;
            }
        }
    }
    build_cyclic(gt);
}

/* ------------------------------------------------------------ bi-Cayley */

static int S[MAXD];
static unsigned char inS[MAXG];
static int VIS[2 * MAXG];
static int VST = 0;
static int QQ[2 * MAXG];

/* Number of vertices reached from src within D steps (BFS in the bi-Cayley graph). */
static long reached_from(int src) {
    VST++;
    int h = 0, t = 0;
    VIS[src] = VST;
    QQ[t++] = src;
    for (int dep = 0; dep < D && h < t; dep++) {
        int end = t;
        while (h < end) {
            int u = QQ[h++];
            if (u < G) {
                for (int i = 0; i < d; i++) {
                    int v = G + GT[u][S[i]];
                    if (VIS[v] != VST) { VIS[v] = VST; QQ[t++] = v; }
                }
            } else {
                int hh = u - G;
                for (int i = 0; i < d; i++) {
                    int v = GT[hh][GINV[S[i]]];
                    if (VIS[v] != VST) { VIS[v] = VST; QQ[t++] = v; }
                }
            }
        }
    }
    return t;
}

/* Unreached pairs from (e,0) and (e,1). Zero means diameter <= D. */
static long bc_cost(void) {
    return 4L * G - reached_from(0) - reached_from(G);
}

/* Anneal the connection set S (|S| = d) for the current group. */
static int anneal_S(long steps) {
    for (int x = 0; x < G; x++) inS[x] = 0;
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(G); } while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
    long cost = bc_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 127) == 0 && now() > t_stop) break;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        int i = rndint(d);
        int x;
        do { x = rndint(G); } while (inS[x]);
        int old = S[i];
        inS[old] = 0;
        S[i] = x;
        inS[x] = 1;
        long c2 = bc_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            inS[x] = 0;
            S[i] = old;
            inS[old] = 1;
        }
    }
    return cost == 0;
}

static void build_bicayley_graph(Graph *out) {
    out->n = 2 * G;
    for (int v = 0; v < out->n; v++) {
        out->deg[v] = 0;
        out->side[v] = (unsigned char)(v >= G);
    }
    for (int g = 0; g < G; g++)
        for (int i = 0; i < d; i++)
            add_edge(out, g, G + GT[g][S[i]]);
}

static void bicayley_search(Graph *best) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < t_stop) {
        int base = best->n / 2;
        int gt = base + 1 + (fails / 25 < 10 ? fails / 25 : 10);
        if (gt < d + 1) gt = d + 1;
        if (2L * gt > moore || 2 * gt > MAXN || gt > MAXG) break;
        sample_group(gt);
        long steps = 4000 + rndint(4000) + 20L * (fails > 200 ? 200 : fails);
        if (anneal_S(steps)) {
            build_bicayley_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                fails = 0;
                continue;
            }
        }
        fails++;
    }
}

/* ------------------------------------------------------------ grow by two */

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

static void grow_search(Graph *best, Graph *work) {
    while (now() < t_stop && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = t_stop - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, work, now() + slice)) copy_graph(best, work);
    }
}

/* ------------------------------------------------------------ main */

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
    double span = limit * 0.96;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, work;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        t_stop = t0 + span * 0.72;
        bicayley_search(&best);
        t_stop = t0 + span;
        grow_search(&best, &work);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D) or d > 30:
        return best

    budget = 0.93 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 3.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
