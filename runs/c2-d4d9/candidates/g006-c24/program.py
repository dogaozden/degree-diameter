"""Cayley-bipartite (Haar-type) search with generator-set annealing.

This version replaces the voltage-lift search with a different construction. A bipartite graph
on two copies of a group G is built from a connection set S of d distinct elements:
x in side 0 is joined to N + x*s in side 1 for each s in S. Left multiplication is an
automorphism that is regular on each side, so a graph is valid iff the balls of radius D around
the identity of side 0 and of side 1 both cover every vertex. The C engine anneals S directly,
swapping one generator at a time to reduce the uncovered count. Groups are random semidirect
products Z_m x| Z_k of order N near the current best half-order, and PSL(2,p) for small primes.
Each success doubles into a larger graph, so the best order climbs step by step. The engine
then grows the graph by two vertices per side. Python supplies the starting graph and keeps
the largest graph that lib.is_valid accepts.
"""
import itertools
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

#define MAXN 10240
#define MAXD 32
#define MAXW (MAXN / 64)
#define CODEMAX 83521

static int d, D;
static double t_end;

/* ------------------------------------------------------------------ utilities */

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

static long cap_order(void) {
    long mb = moore_bound();
    return mb < MAXN ? mb : MAXN;
}

/* ------------------------------------------------------------------ graphs */

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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

static int bfs_stamp[MAXN];
static int bfs_tick = 0;
static int bfs_q[MAXN];

/* Number of vertices within distance D of s (s included). */
static int ball_size(const Graph *g, int s) {
    if (++bfs_tick == 0x7fffffff) {
        memset(bfs_stamp, 0, sizeof bfs_stamp);
        bfs_tick = 1;
    }
    int head = 0, tail = 0;
    bfs_stamp[s] = bfs_tick;
    bfs_q[tail++] = s;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = bfs_q[head];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (bfs_stamp[u] != bfs_tick) {
                    bfs_stamp[u] = bfs_tick;
                    bfs_q[tail++] = u;
                }
            }
        }
    }
    return tail;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* kind 0: Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e); identity 0.
 * kind 1: PSL(2,p) from the global tables; identity index e. */
typedef struct {
    int kind, N, e;
    int m, k, r;
    int rp[MAXN];
} Grp;

static int mp = 0;                 /* prime of the loaded PSL(2,p) */
static int MATN = 0;
static int MATV[MAXN][4];
static int CODE2[CODEMAX];
static int mat_loaded_p = 0;

static int code_of(int a, int b, int c, int e) { return ((a * mp + b) * mp + c) * mp + e; }

static int pnorm(int a, int b, int c, int e) {
    int v[4] = {a, b, c, e};
    int f = 0;
    for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
    if (f > (mp - 1) / 2)
        for (int i = 0; i < 4; i++) v[i] = (mp - v[i]) % mp;
    return code_of(v[0], v[1], v[2], v[3]);
}

/* Canonical representatives of PSL(2,p): det-1 matrices modulo sign. */
static void load_psl(int p) {
    if (mat_loaded_p == p) return;
    mp = p;
    int Q4 = p * p * p * p;
    for (int i = 0; i < Q4; i++) CODE2[i] = -1;
    MATN = 0;
    for (int code = 0; code < Q4; code++) {
        int e = code % p, c = (code / p) % p, b = (code / (p * p)) % p, a = code / (p * p * p);
        if ((((a * e - b * c) % p) + p) % p != 1) continue;
        if (pnorm(a, b, c, e) != code) continue;
        if (MATN >= MAXN) break;
        CODE2[code] = MATN;
        MATV[MATN][0] = a; MATV[MATN][1] = b; MATV[MATN][2] = c; MATV[MATN][3] = e;
        MATN++;
    }
    mat_loaded_p = p;
}

static int mat_mul(int x, int y) {
    const int *X = MATV[x], *Y = MATV[y];
    int a = (X[0] * Y[0] + X[1] * Y[2]) % mp;
    int b = (X[0] * Y[1] + X[1] * Y[3]) % mp;
    int c = (X[2] * Y[0] + X[3] * Y[2]) % mp;
    int e = (X[2] * Y[1] + X[3] * Y[3]) % mp;
    return CODE2[pnorm(a, b, c, e)];
}

static int gmul(const Grp *G, int x, int y) {
    if (G->kind == 1) return mat_mul(x, y);
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random semidirect group Z_m x| Z_N/m of order N. */
static int random_group(int N, Grp *G) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    G->kind = 0;
    G->N = N;
    G->e = 0;
    G->m = bm;
    G->k = bk;
    G->r = br;
    G->rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G->rp[b] = (int)((long)G->rp[b - 1] * br % bm);
    return 1;
}

/* ------------------------------------------------------------------ Cayley bipartite search */

static int S[MAXD];
static Graph cand;

static int in_S(int s) {
    for (int j = 0; j < d; j++) if (S[j] == s) return 1;
    return 0;
}

/* Haar-Cayley graph: x (side 0) ~ N + x*s (side 1) for s in S. */
static void haar_build(Graph *g, const Grp *G) {
    int N = G->N;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + gmul(G, x, S[t]));
}

/* Uncovered count from the two representatives 0 (side 0) and N (side 1). */
static long haar_cost(const Graph *g, int N) {
    return (long)(g->n - ball_size(g, 0)) + (long)(g->n - ball_size(g, N));
}

static int haar_try(const Grp *G, int steps, double until) {
    int N = G->N;
    if (N < d + 1) return 0;
    for (int t = 0; t < d;) {
        int s = rndint(N);
        if (!in_S_upto(s, t)) S[t++] = s;
    }
    haar_build(&cand, G);
    long cost = haar_cost(&cand, N);
    double T0 = 0.5 + rnd01();
    for (int s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > until) return 0;
        double T = T0 * (1.0 - (double)s / steps) + 0.02;
        int t = rndint(d);
        int old = S[t];
        int ns;
        do { ns = rndint(N); } while (in_S(ns));
        S[t] = ns;
        haar_build(&cand, G);
        long nc = haar_cost(&cand, N);
        long df = nc - cost;
        if (df <= 0 || rnd01() < exp(-(double)df / T)) cost = nc;
        else S[t] = old;
    }
    if (cost != 0) return 0;
    haar_build(&cand, G);
    return is_valid(&cand);
}

static void haar_search(Graph *best, double until) {
    static Grp G;
    long cap = cap_order();
    while (now() < until) {
        long lo = best->n / 2 + 1;
        long span = lo / 6 + 10;
        long N = lo + rndint((int)span);
        if (2 * N > cap) N = cap / 2;
        if (N < d + 1) return;
        if (2 * N <= best->n) continue;
        int steps = 15000;
        int ok = 0;
        if (rnd01() < 0.25) {
            static const int primes[] = {5, 7, 11, 13, 17};
            int cp[5], nc = 0;
            for (int i = 0; i < 5; i++) {
                long o = (long)primes[i] * (primes[i] * primes[i] - 1) / 2;
                if (o >= lo && 2 * o <= cap) cp[nc++] = primes[i];
            }
            if (nc > 0) {
                int p = cp[rndint(nc)];
                load_psl(p);
                G.kind = 1;
                G.N = MATN;
                G.e = CODE2[code_of(1, 0, 0, 1)];
                ok = haar_try(&G, steps, until);
                if (ok && cand.n > best->n) copy_graph(best, &cand);
                continue;
            }
        }
        if (!random_group((int)N, &G)) continue;
        ok = haar_try(&G, steps, until);
        if (ok && cand.n > best->n) copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ grow by two */

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

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && (long)best->n + 2 <= cap_order()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
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
    t_end = t0 + limit * 0.93 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        haar_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
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


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def known_starts(d, D):
    """Algebraic candidate graphs (filtered by lib.is_valid by the caller)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(_try(lib.projective_plane_incidence, d - 1))
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(_try(lib.araujo_lopez_graph, d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_try(_gq_w, q))
    return [c for c in out if c is not None]


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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
