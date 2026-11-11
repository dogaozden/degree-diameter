"""Combined program: Python builds the best algebraic start and checks it with lib.is_valid.
The C engine then searches from that start.

New in this version: the C engine's main search is a bi-Cayley search. For a group G of order N
(a semidirect product Z_m x|_r Z_k), it looks for a connection set S of size d such that the graph
with A_x adjacent to B_{x s} (s in S) has diameter <= D. Left multiplication is an automorphism,
so the diameter test needs only two BFS runs, from A_e and from B_e. Each candidate costs
microseconds, so the search tests many (group, S) pairs. Simulated annealing on the number of
unreached vertices drives S. Groups and orders are sampled from a window just above the current
best, and the window widens over time. Any valid graph found is then grown by two vertices at a
time, as before.

For d = 4 and D >= 6, Python builds the split Cayley generalized hexagon H(3) as a point-line
incidence graph (728 vertices, 4-regular, diameter 6, bipartite). It is valid for D = 7. The
hexagon is found by searching over sign variants of the Plucker line conditions, and every
candidate is checked with lib.is_valid. If no variant verifies, the older starts are used.
Every C output is checked with lib.is_valid before it replaces the start."""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Bi-Cayley search over semidirect groups Z_m x|_r Z_k of order N: connection set S (|S| = d)
 *    annealed so that the diameter is <= D. Only BFS from A_e and B_e is needed.
 * 2. Grow by two: insert one vertex per side and anneal degree-preserving edge swaps.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXBC 1024

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* ---------------- bi-Cayley search ----------------
 * Group G = Z_m x|_r Z_k of order N, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k).
 * MT[x*N+y] is the product x*y; INV[x] is the inverse; identity is element 0.
 * Graph: A_x (index x) adjacent to B_{x s} (index N + x s) for s in S, |S| = d.
 * Left multiplication is an automorphism, so the diameter is <= D iff every vertex is within
 * distance D of A_e and of B_e. */
static int MT[MAXBC * MAXBC];
static int INV[MAXBC];
static int RPW[MAXBC];
static int BN;
static int BS[MAXD], BSI[MAXD];
static int vst[2 * MAXBC];
static int vstamp = 0;
static int bq[2 * MAXBC];

static void build_group(int N, int m, int k, int r) {
    RPW[0] = 1 % m;
    for (int b = 1; b < k; b++) RPW[b] = (int)((long)RPW[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int ax = x / k, bx = x % k;
        for (int y = 0; y < N; y++) {
            int cy = y / k, ey = y % k;
            MT[x * N + y] = (int)(((ax + (long)RPW[bx] * cy) % m) * k + (bx + ey) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
    }
}

static int gM, gK, gR;

/* Pick a random semidirect group of order N and build its tables. */
static int pick_group(int N) {
    int divs[MAXBC];
    int nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0) divs[nd++] = m;
    for (int att = 0; att < 2000; att++) {
        int m = divs[rndint(nd)];
        int k = N / m;
        if (m == 1) {
            gM = 1; gK = k; gR = 0;
            build_group(N, 1, k, 0);
            return 1;
        }
        int r = 1 + rndint(m - 1);
        if (gcd(r, m) != 1) continue;
        if (powmod(r, k, m) != 1 % m) continue;
        gM = m; gK = k; gR = r;
        build_group(N, m, k, r);
        return 1;
    }
    return 0;
}

static int reach_count(int src) {
    int N = BN;
    vstamp++;
    int tail = 0;
    bq[tail++] = src;
    vst[src] = vstamp;
    int ls = 0, le = 1;
    for (int depth = 0; depth < D && ls < le; depth++) {
        for (int i = ls; i < le; i++) {
            int v = bq[i];
            if (v < N) {
                const int *row = MT + v * N;
                for (int j = 0; j < d; j++) {
                    int u = N + row[BS[j]];
                    if (vst[u] != vstamp) { vst[u] = vstamp; bq[tail++] = u; }
                }
            } else {
                const int *row = MT + (v - N) * N;
                for (int j = 0; j < d; j++) {
                    int u = row[BSI[j]];
                    if (vst[u] != vstamp) { vst[u] = vstamp; bq[tail++] = u; }
                }
            }
        }
        ls = le;
        le = tail;
    }
    return tail;
}

static int eval_S(void) {
    int N = BN;
    return (2 * N - reach_count(0)) + (2 * N - reach_count(N));
}

/* Anneal a connection set S of size d in the current group until the diameter objective is 0. */
static int hill_search(double until, int *out) {
    int N = BN;
    int S[MAXD];
    for (;;) {
        if (now() > until) return 0;
        for (int j = 0; j < d; j++) {
            int g, ok;
            do {
                g = rndint(N);
                ok = 1;
                for (int t = 0; t < j; t++)
                    if (S[t] == g) { ok = 0; break; }
            } while (!ok);
            S[j] = g;
            BS[j] = g;
            BSI[j] = INV[g];
        }
        int f = eval_S();
        double T = 1.0;
        for (int it = 0; it < 4000 && f > 0; it++) {
            if ((it & 127) == 0 && now() > until) return 0;
            int j = rndint(d), g = rndint(N);
            int dup = 0;
            for (int t = 0; t < d; t++)
                if (S[t] == g) { dup = 1; break; }
            if (dup) continue;
            int old = S[j];
            S[j] = g;
            BS[j] = g;
            BSI[j] = INV[g];
            int f2 = eval_S();
            if (f2 <= f || rnd01() < exp((double)(f - f2) / T)) {
                f = f2;
            } else {
                S[j] = old;
                BS[j] = old;
                BSI[j] = INV[old];
            }
            T *= 0.999;
            if (T < 0.2) T = 0.2;
        }
        if (f == 0) {
            memcpy(out, S, sizeof(int) * d);
            return 1;
        }
    }
}

static void bicayley_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    double start = now();
    double span = until - start;
    int Nmax = (int)(moore / 2);
    if (Nmax > MAXBC) Nmax = MAXBC;
    while (now() < until) {
        int Nmin = best->n / 2 + 1;
        if (Nmin < 2 * d) Nmin = 2 * d;
        if (Nmin > Nmax) return;
        double frac = span > 0 ? (now() - start) / span : 1.0;
        if (frac > 1.0) frac = 1.0;
        int width = 2 + (int)(frac * 60.0);
        int N = Nmin + rndint(width);
        if (N > Nmax) N = Nmax;
        if (!pick_group(N)) continue;
        BN = N;
        double slice = until - now();
        if (slice > 0.25) slice = 0.25;
        if (slice <= 0) return;
        int S[MAXD];
        if (hill_search(now() + slice, S)) {
            cand.n = 2 * N;
            for (int v = 0; v < cand.n; v++) {
                cand.deg[v] = 0;
                cand.side[v] = v >= N;
            }
            for (int x = 0; x < N; x++)
                for (int j = 0; j < d; j++)
                    add_edge(&cand, x, N + MT[x * N + S[j]]);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------- grow by two ---------------- */

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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && d >= 2 && best.n < moore_bound()) {
        bicayley_search(&best, t0 + (t_end - t0) * 0.8);
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


# ------------------------------------------------- split Cayley hexagon H(3)

_PAIRS7 = [(i, j) for i in range(7) for j in range(i + 1, 7)]
# Plucker conditions p_a = s * p_b for the lines of H(q) on Q(6,q): X0X4+X1X5+X2X6 = X3^2.
_HEX_EQS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
            ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]


def _q3(v):
    """Quadratic form X0X4 + X1X5 + X2X6 - X3^2 over GF(3)."""
    return (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % 3


def _norm3(v):
    """Projective normal form over GF(3): scale so the first nonzero entry is 1."""
    c = next((x for x in v if x), 0)
    if c == 0:
        return None
    return tuple((c * x) % 3 for x in v)  # c is its own inverse in GF(3)


def _pl(P, i, j):
    """Antisymmetric Plucker coordinate p_ij over GF(3)."""
    return P[(i, j)] if i < j else (-P[(j, i)]) % 3


def _hexagon_h3(D):
    """Return (n, edges) for the incidence graph of H(3) (728 vertices, degree 4, diameter 6),
    or None if no sign variant of the line conditions verifies."""
    pts = [v for v in itertools.product(range(3), repeat=7)
           if any(v) and next(c for c in v if c) == 1 and _q3(v) == 0]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    # All totally singular lines of Q(6,3): x, y singular, and x+y singular (then B(x,y)=0).
    lines = {}
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            s = tuple((a + b) % 3 for a, b in zip(x, y))
            if _q3(s) != 0:
                continue
            t = tuple((a + 2 * b) % 3 for a, b in zip(x, y))
            ids = [index.get(_norm3(x)), index.get(_norm3(y)),
                   index.get(_norm3(s)), index.get(_norm3(t))]
            if None in ids:
                continue
            L = frozenset(ids)
            if L not in lines:
                lines[L] = (x, y)

    line_pl = []
    for L, (x, y) in lines.items():
        Pv = {(i, j): (x[i] * y[j] - x[j] * y[i]) % 3 for (i, j) in _PAIRS7}
        line_pl.append((L, Pv))

    for signs in itertools.product((1, 2), repeat=len(_HEX_EQS)):
        sel = []
        for L, Pv in line_pl:
            ok = True
            for (a, b), s in zip(_HEX_EQS, signs):
                if _pl(Pv, *a) != (s * _pl(Pv, *b)) % 3:
                    ok = False
                    break
            if ok:
                sel.append(L)
        if len(sel) != P:
            continue
        deg = [0] * P
        for L in sel:
            for p in L:
                deg[p] += 1
        if any(c != 4 for c in deg):
            continue
        edges = [(p, P + j) for j, L in enumerate(sel) for p in sorted(L)]
        n = 2 * P
        if lib.is_valid(n, edges, 4, D):
            return n, edges
    return None


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

    if d == 4 and D >= 6:
        try:
            hx = _hexagon_h3(D)
            if hx is not None and hx[0] > best[0] and lib.is_valid(hx[0], hx[1], d, D):
                best = hx
        except Exception:
            pass

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
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
