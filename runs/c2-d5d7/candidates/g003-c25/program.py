"""Bi-Cayley search program: a new construction for the weakest cases.

Python builds the best algebraic start (split Cayley hexagon H(q) for D >= 6, projective planes,
Araujo-Lopez, or generalized quadrangles), checks each with lib.is_valid, and passes it to C as
the fallback. The C engine tries bi-Cayley graphs: vertices a_x and b_x for x in a group G of
order N, with a_x ~ b_{x s} for s in a set S of d distinct group elements. Left translation is an
automorphism, so the diameter check needs only two BFS runs (from a_e and b_e). Simulated
annealing over S and random semidirect-product groups Z_m x| Z_k pushes N up. If no bi-Cayley
graph beats the start, the engine grows the start by two vertices at a time, as before.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley degree-diameter search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: bi-Cayley search. Group G of order N (Z_m x|_r Z_k), S = d distinct elements.
 *          Vertices a_x (0..N-1) and b_x (N..2N-1); a_x ~ b_{x*s}. Cost = vertices unreached
 *          within D from a_e plus from b_e. Annealed over S, N increases on success.
 * Phase 2: grow the best graph by two vertices at a time with annealed edge swaps.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXV (2 * MAXN)
#define MAXD 12
#define MAXW (MAXV / 64)

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXV * MAXW], RB[MAXV * MAXW];
static int badv[MAXV];

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
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
    if (g->n <= 0 || g->n > MAXV) return 0;
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

/* ------------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXV];
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int N, m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int k = G->k, m = G->m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return (int)(((long)a + (long)G->rp[b] * c) % m) * k + (b + e) % k;
}

/* Inverse of (a,b) is (-r^{-b} a, -b), with r^{-b} = r^{k-b} since r^k = 1. */
static int ginv(const Grp *G, int x) {
    int k = G->k, m = G->m;
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    long v = (-(long)G->rp[nb] * a) % m;
    if (v < 0) v += m;
    return (int)v * k + nb;
}

/* Uniformly random semidirect group Z_m x|_r Z_k of order N (cyclic when r = 1). */
static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) {
                G->m = m;
                G->k = k;
                G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->N = N;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------------ bi-Cayley search */

static int nbr[MAXV][MAXD];       /* neighbours of each vertex in the current bi-Cayley graph */
static int Sg[MAXD], Si[MAXD];    /* connection set and its inverses */
static int bdist[MAXV], bq[MAXV];

static void build_nb(const Grp *G) {
    int N = G->N;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            nbr[x][i] = N + gmul(G, x, Sg[i]);       /* a_x ~ b_{x s} */
            nbr[N + x][i] = gmul(G, x, Si[i]);       /* b_y ~ a_{y s^-1} */
        }
}

/* Vertices not reached from src within D steps (V = 2N total). */
static int unreached(int src, int V) {
    for (int v = 0; v < V; v++) bdist[v] = -1;
    int h = 0, t = 0;
    bdist[src] = 0;
    bq[t++] = src;
    while (h < t) {
        int v = bq[h++];
        if (bdist[v] >= D) continue;
        for (int i = 0; i < d; i++) {
            int u = nbr[v][i];
            if (bdist[u] < 0) {
                bdist[u] = bdist[v] + 1;
                bq[t++] = u;
            }
        }
    }
    return V - t;
}

static long cost_of(const Grp *G) {
    build_nb(G);
    int V = 2 * G->N;
    /* Left translations are automorphisms, so these two sources cover every pair. */
    return (long)unreached(0, V) + (long)unreached(G->N, V);
}

/* Element not equal to any Sg[j] with j != skip. */
static int fresh_elem(int N, int skip) {
    for (;;) {
        int t = rndint(N), clash = 0;
        for (int j = 0; j < d; j++)
            if (j != skip && Sg[j] == t) { clash = 1; break; }
        if (!clash) return t;
    }
}

static void random_S(int N) {
    for (int i = 0; i < d; i++) Sg[i] = -1;
    for (int i = 0; i < d; i++) Sg[i] = fresh_elem(N, i);
}

/* Anneal the connection set S in group G. Returns 1 on success (cost 0); Sg holds S. */
static int anneal(Grp *G, double until, long maxsteps) {
    int N = G->N;
    random_S(N);
    for (int i = 0; i < d; i++) Si[i] = ginv(G, Sg[i]);
    long cur = cost_of(G);
    for (long s = 0; s < maxsteps && cur > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        double T = 1.5 * (1.0 - (double)s / (double)maxsteps) + 0.05;
        int i = rndint(d);
        int old = Sg[i], oldi = Si[i];
        int t = fresh_elem(N, i);
        Sg[i] = t;
        Si[i] = ginv(G, t);
        long nc = cost_of(G);
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            Sg[i] = old;
            Si[i] = oldi;
        }
    }
    return cur == 0;
}

static void graph_from_nb(Graph *g, int N) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= N;
    }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, nbr[x][i]);
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXV) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXV];
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
        long nbad = bad_pairs(work);
        if (nbad <= bad || rnd01() < exp((double)(bad - nbad) / T)) {
            bad = nbad;
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

/* ------------------------------------------------------------------ main */

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
    if (d < 1 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    static Graph best, cand, work;
    static Grp G;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();

    /* Phase 1: bi-Cayley search, N growing on success. */
    double bc_end = t0 + (t_end - t0) * 0.75;
    int N = best.n / 2 + 1;
    if (N < d) N = d;
    while (now() < bc_end) {
        if (2L * N > moore || 2L * N > MAXV) break;
        double left = bc_end - now();
        double slice = left / 3.0;
        if (slice < 3.0) slice = left < 3.0 ? left : 3.0;
        if (!random_group(N, &G)) { N++; continue; }
        if (anneal(&G, now() + slice, 150000)) {
            build_nb(&G);
            graph_from_nb(&cand, N);
            if (is_valid(&cand) && cand.n > best.n) copy_graph(&best, &cand);
            N++;
        }
    }

    /* Phase 2: grow the best graph by two vertices at a time. */
    while (now() < t_end && best.n + 2 <= moore && best.n + 2 <= MAXV) {
        double left = t_end - now();
        double slice = left / 4.0;
        if (slice > 4.0) slice = 4.0;
        if (slice < 0.05) break;
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
    }

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


def hexagon_graph(q):
    """Incidence graph of the split Cayley hexagon H(q): generalized hexagon of order (q, q).

    Order 2(q^6-1)/(q-1), degree q+1, diameter 6. Returns (n, edges) or None.
    The caller validates the result with lib.is_valid.
    """
    N = (q ** 6 - 1) // (q - 1)
    if 2 * N > 4000:
        return None
    F = lib.GF(q)
    M, A = F.mul_table, F.add_table
    negt = np.array([F.neg(x) for x in range(q)], dtype=np.int64)

    def singular(v):
        s = F.add(F.mul(v[0], v[4]), F.mul(v[1], v[5]))
        return F.add(s, F.mul(v[2], v[6])) == F.mul(v[3], v[3])

    pts = []
    for v in itertools.product(range(q), repeat=7):
        first = next((c for c in v if c), 0)
        if first == 1 and singular(v):
            pts.append(v)
    if len(pts) != N:
        return None
    idx = {v: i for i, v in enumerate(pts)}
    Pa = np.array(pts, dtype=np.int64)

    def normalize(v):
        c = next(c for c in v if c)
        ic = F.inv(c)
        return tuple(F.mul(ic, x) for x in v)

    lines = set()
    for i in range(N - 1):
        X = pts[i]
        Yf = Pa[i + 1:]
        # Polar form of the quadric; two singular points are collinear on Q iff B = 0.
        s = A[A[A[M[X[0], Yf[:, 4]], M[X[4], Yf[:, 0]]],
                A[M[X[1], Yf[:, 5]], M[X[5], Yf[:, 1]]]],
              A[M[X[2], Yf[:, 6]], M[X[6], Yf[:, 2]]]]
        t = M[X[3], Yf[:, 3]]
        B = A[s, negt[A[t, t]]]
        sel = np.nonzero(B == 0)[0]
        if sel.size == 0:
            continue
        Ys = Yf[sel].T

        def pl(a, b):
            """Plucker-type coordinate X_a Y_b - X_b Y_a, vectorised over candidate Y."""
            return A[M[X[a], Ys[b]], negt[M[X[b], Ys[a]]]]

        keep = ((pl(1, 2) == pl(3, 4)) & (pl(5, 4) == pl(3, 2)) & (pl(2, 0) == pl(3, 5))
                & (pl(6, 5) == pl(3, 0)) & (pl(0, 1) == pl(3, 6)) & (pl(4, 6) == pl(3, 1)))
        for jj in sel[keep]:
            j = i + 1 + int(jj)
            Y = pts[j]
            members = {i, j}
            for tt in range(q):
                v = tuple(F.add(X[k], F.mul(tt, Y[k])) for k in range(7))
                members.add(idx[normalize(v)])
            lines.add(tuple(sorted(members)))

    lines = sorted(lines)
    edges = [(p, N + l) for l, mem in enumerate(lines) for p in mem]
    return N + len(lines), edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic starts valid for (d, D), each checked with lib.is_valid (may be empty)."""
    makers = []
    q = d - 1
    if D >= 3 and q >= 2 and lib.is_prime_power(q):
        makers.append(lambda: lib.projective_plane_incidence(q))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        makers.append(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 6 and q >= 2 and lib.is_prime_power(q):
        makers.append(lambda: hexagon_graph(q))
    if D >= 4:
        qg = _largest_prime_power_le(min(d - 1, 9))
        if qg is not None and qg >= 2:
            makers.append(lambda: _gq_w(qg))
    out = []
    for make in makers:
        try:
            g = make()
        except Exception:
            continue
        if g is not None and lib.is_valid(g[0], g[1], d, D):
            out.append(g)
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

    starts = known_starts(d, D)
    start = max(starts, key=lambda g: g[0]) if starts else None
    best = start if start is not None else lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    if best[0] >= lib.moore_bound(d, D) or d > 11:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0 or best[0] > 8000:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 6.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
