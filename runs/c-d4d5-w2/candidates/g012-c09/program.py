"""Bold variant: bi-Cayley search over many finite groups.

Construction: vertices a_x and b_y for x, y in a group G of order N, with a_x ~ b_{x s} for s in S,
|S| = d. Left multiplication by G is an automorphism, so the diameter test needs only two BFS
(from a_e and b_e). The C engine hill-climbs the connection set S over semidirect products
Z_m x|_r Z_k of order N, for N = best/2 + 1 upward. Each success is checked in full and kept.
Fallback: K_{d,d}, the algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez), and the start graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  "n m" then m lines "u v": the best valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXV (2 * MAXG)
#define MAXDEG 32
#define MAXGROUPS 4096

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXDEG];
} Graph;

typedef struct { int m, k, r; } GDesc;

static int d, D;
static double t_end;
static int T[MAXG][MAXG];
static int INV[MAXG];
static GDesc gl[MAXGROUPS];
static int ngl;
static int vdist[MAXV], vq[MAXV], vside[MAXV];
static int g_found_S[MAXDEG];

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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static int add_edge(Graph *g, int u, int v) {
    if (g->deg[u] >= MAXDEG || g->deg[v] >= MAXDEG) return 0;
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
    return 1;
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* BFS limited to depth D from s; returns number of vertices reached. Uses vdist, vq. */
static int bfs_limited(const Graph *g, int s) {
    int n = g->n, h = 0, t = 0;
    for (int v = 0; v < n; v++) vdist[v] = -1;
    vdist[s] = 0;
    vq[t++] = s;
    while (h < t) {
        int v = vq[h++];
        if (vdist[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (vdist[u] < 0) { vdist[u] = vdist[v] + 1; vq[t++] = u; }
        }
    }
    return t;
}

static int valid_graph(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXV) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
            if (!has_edge(g, u, v)) return 0;
        }
    }
    for (int v = 0; v < n; v++) vside[v] = -1;
    for (int s = 0; s < n; s++) {
        if (vside[s] >= 0) continue;
        vside[s] = 0;
        int h = 0, t = 0;
        vq[t++] = s;
        while (h < t) {
            int v = vq[h++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (vside[u] < 0) { vside[u] = 1 - vside[v]; vq[t++] = u; }
                else if (vside[u] == vside[v]) return 0;
            }
        }
    }
    for (int s = 0; s < n; s++)
        if (bfs_limited(g, s) != n) return 0;
    return 1;
}

static int read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXV || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) g->deg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { g->n = 0; return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || !add_edge(g, u, v)) {
            g->n = 0;
            return 0;
        }
    }
    if (!valid_graph(g)) { g->n = 0; return 0; }
    return 1;
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

/* Multiplication table of Z_m x|_r Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void build_group(GDesc G) {
    int m = G.m, k = G.k, N = m * k;
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            T[x][y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (T[x][y] == 0) { INV[x] = y; break; }
}

static void enumerate_groups(int N) {
    ngl = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ngl < MAXGROUPS) { gl[ngl].m = 1; gl[ngl].k = k; gl[ngl].r = 0; ngl++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngl < MAXGROUPS) { gl[ngl].m = m; gl[ngl].k = k; gl[ngl].r = r; ngl++; }
        }
    }
}

static int in_set(int c, const int *S, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == c) return 1;
    return 0;
}

/* Neighbours of vertex v in the bi-Cayley graph: a_x = x, b_y = N + y. */
static void nb_of(int N, const int *S, int v, int *out) {
    if (v < N) {
        for (int i = 0; i < d; i++) out[i] = N + T[v][S[i]];
    } else {
        int y = v - N;
        for (int i = 0; i < d; i++) out[i] = T[y][INV[S[i]]];
    }
}

static int bi_bfs(int N, const int *S, int src) {
    int tot = 2 * N, h = 0, t = 0, nb[MAXDEG];
    for (int v = 0; v < tot; v++) vdist[v] = -1;
    vdist[src] = 0;
    vq[t++] = src;
    while (h < t) {
        int v = vq[h++];
        if (vdist[v] >= D) continue;
        nb_of(N, S, v, nb);
        for (int i = 0; i < d; i++) {
            int u = nb[i];
            if (vdist[u] < 0) { vdist[u] = vdist[v] + 1; vq[t++] = u; }
        }
    }
    return t;
}

/* Cost 0 iff the bi-Cayley graph has diameter <= D. By left-transitivity on each side,
 * BFS from a_e covers all A-A and A-B pairs and BFS from b_e covers all B-B pairs. */
static int bi_cost(int N, const int *S) {
    int cost = 2 * N - bi_bfs(N, S, 0);
    bi_bfs(N, S, N);
    for (int y = 0; y < N; y++)
        if (vdist[N + y] < 0) cost++;
    return cost;
}

/* Hill-climb the connection set S (S[0] = identity) over one group. */
static int try_group(GDesc G, int N, int steps, double until, int *S) {
    build_group(G);
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int c;
        do c = 1 + rndint(N - 1); while (in_set(c, S, i));
        S[i] = c;
    }
    int cost = bi_cost(N, S);
    for (int s = 0; s < steps && cost > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int i = 1 + rndint(d - 1);
        int c;
        do c = 1 + rndint(N - 1); while (in_set(c, S, d));
        int old = S[i];
        S[i] = c;
        int nc = bi_cost(N, S);
        if (nc <= cost || rnd01() < 0.03) cost = nc;
        else S[i] = old;
    }
    return cost == 0;
}

static void graph_from_current(Graph *g, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, N + T[x][S[i]]);
}

static Graph cand;

static void bicayley_search(Graph *best, double until) {
    long moore = moore_bound();
    long Nhi = moore / 2;
    if (Nhi > MAXG) Nhi = MAXG;
    long N = best->n / 2 + 1;
    if (N < d) N = d;
    while (N <= Nhi && now() < until) {
        enumerate_groups((int)N);
        double remain = until - now();
        double stop = now() + (remain * 0.35 > 1.0 ? remain * 0.35 : 1.0);
        if (stop > until) stop = until;
        int found = 0;
        while (!found && now() < stop && ngl > 0) {
            GDesc G = gl[rndint(ngl)];
            if (try_group(G, (int)N, 4000, stop, g_found_S)) found = 1;
        }
        if (found) {
            graph_from_current(&cand, (int)N, g_found_S);
            if (cand.n > best->n && valid_graph(&cand)) *best = cand;
        }
        N++;
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
    int have = read_start(&best);
    if (D < 2 || d < 1 || d > 31) {
        if (have) print_graph(&best);
        else printf("0 0\n");
        return 0;
    }
    if (!have) complete_bipartite(&best);
    if (d >= 3 && best.n < moore_bound())
        bicayley_search(&best, t_end);
    if (!valid_graph(&best)) complete_bipartite(&best);
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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
