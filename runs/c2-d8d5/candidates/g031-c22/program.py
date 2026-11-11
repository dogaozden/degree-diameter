"""Bold variant: C-side bi-Cayley lift annealing over semidirect products with larger base blocks (k = 2..8).

Each candidate is a bi-Cayley graph on 2kG vertices. Annealing moves voltages and layer permutations,
scored by the number of unreached (block, vertex) pairs, using block-representative bitmasks.
The exact constructions (PG(2,q), Araujo-Lopez, W(q)) still run first for the calibration cases.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over Z_m x| Z_k2 with k = 2..8 base blocks per side,
# simulated annealing on voltages and layer permutations, growing order each success.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley lift annealing with growing order.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 *
 * Vertices of a lift: A_{i,x} = i*G + x (i < k), B_{j,h} = (k+j)*G + h.
 * Layer l joins A_{i,x} to B_{P[l][i], x*S[l][i]}, with P[l] a permutation.
 * Group: Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e).
 * Diameter check: cost = number of (block representative, vertex) pairs at distance > D.
 * Left multiplication is an automorphism, so this cost is zero iff the diameter is <= D.
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
#define MAXK 8
#define MAXW (MAXN / 64)
#define PEN 1000L

static int d, D;
static double t_end;

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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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

/* Semidirect group of order G with multiplication table via formula and inverse table. */
typedef struct {
    int m, k2, r, G;
    int rp[MAXN];
    int inv[MAXN];
} Grp;

static Grp grp;

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    return (int)(((long)a + (long)g->rp[b] * c) % g->m) * g->k2 + (b + e) % g->k2;
}

static int make_group(int G, Grp *g) {
    long count = 0;
    int bm = 1, bk = G, br = 1;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    if (!count) return 0;
    g->G = G;
    g->m = bm;
    g->k2 = bk;
    g->r = br;
    g->rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) g->rp[b] = (int)((long)g->rp[b - 1] * br % bm);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (gmul(g, x, y) == 0) { g->inv[x] = y; break; }
    return 1;
}

typedef struct {
    int k, G, nd;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
    int nbr[MAXD][MAXN];
} Lift;

static Lift LF;

static void set_dart(Lift *L, int l, int i) {
    int G = L->G, k = L->k, j = L->P[l][i], s = L->S[l][i], si = grp.inv[s];
    for (int x = 0; x < G; x++) {
        L->nbr[l][i * G + x] = (k + j) * G + gmul(&grp, x, s);
        L->nbr[l][(k + j) * G + x] = i * G + gmul(&grp, x, si);
    }
}

static void build_all(Lift *L) {
    for (int l = 0; l < L->nd; l++)
        for (int i = 0; i < L->k; i++) set_dart(L, l, i);
}

static void random_lift(Lift *L) {
    for (int l = 0; l < L->nd; l++) {
        for (int i = 0; i < L->k; i++) L->P[l][i] = i;
        for (int i = L->k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = L->P[l][i];
            L->P[l][i] = L->P[l][j];
            L->P[l][j] = t;
        }
        for (int i = 0; i < L->k; i++) L->S[l][i] = rndint(L->G);
    }
    build_all(L);
}

static unsigned int RR0[MAXN], RR1[MAXN];

/* Sum over vertices of unreached block representatives (zero iff diameter <= D). */
static long diam_cost(const Lift *L) {
    int k = L->k, G = L->G, N = 2 * k * G, nd = L->nd;
    unsigned int *cur = RR0, *nxt = RR1;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[b * G] = 1u << b;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            unsigned int r = cur[v];
            for (int l = 0; l < nd; l++) r |= cur[L->nbr[l][v]];
            nxt[v] = r;
        }
        unsigned int *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long c = 0;
    for (int v = 0; v < N; v++) c += 2 * k - __builtin_popcount(cur[v]);
    return c;
}

/* Number of duplicated (layer, block) darts, which would create multi-edges. */
static long dup_count(const Lift *L) {
    long c = 0;
    for (int l = 0; l < L->nd; l++)
        for (int i = 0; i < L->k; i++)
            for (int l2 = 0; l2 < l; l2++)
                if (L->P[l2][i] == L->P[l][i] && L->S[l2][i] == L->S[l][i]) { c++; break; }
    return c;
}

static long total_cost(const Lift *L) { return diam_cost(L) + PEN * dup_count(L); }

static int anneal(double until) {
    random_lift(&LF);
    int k = LF.k, G = LF.G, nd = LF.nd;
    long cost = total_cost(&LF);
    double start = now();
    double span = until - start;
    if (span <= 0) return cost == 0;
    double frac = 0.0;
    for (long it = 0; cost > 0; it++) {
        if ((it & 31) == 0) {
            double tn = now();
            if (tn >= until) break;
            frac = (tn - start) / span;
        }
        double T = 25.0 * (1.0 - frac) + 0.5;
        if (k >= 2 && rndint(100) < 25) {
            int l = rndint(nd), i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int t = LF.P[l][i1];
            LF.P[l][i1] = LF.P[l][i2];
            LF.P[l][i2] = t;
            set_dart(&LF, l, i1);
            set_dart(&LF, l, i2);
            long nc = total_cost(&LF);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = LF.P[l][i1];
                LF.P[l][i1] = LF.P[l][i2];
                LF.P[l][i2] = t;
                set_dart(&LF, l, i1);
                set_dart(&LF, l, i2);
            }
        } else {
            int l = rndint(nd), i = rndint(k);
            int old = LF.S[l][i], nw = rndint(G);
            if (nw == old) continue;
            LF.S[l][i] = nw;
            set_dart(&LF, l, i);
            long nc = total_cost(&LF);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                LF.S[l][i] = old;
                set_dart(&LF, l, i);
            }
        }
    }
    return cost == 0;
}

static void lift_to_graph(Graph *g) {
    int k = LF.k, G = LF.G, N = 2 * k * G;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= k * G; }
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < LF.nd; l++) add_edge(g, v, LF.nbr[l][v]);
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

    static Graph best, cand;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    long moore = moore_bound();
    int fails = 0;
    if (D >= 2) {
        while (now() < t_end && fails < 5000) {
            double left = t_end - now();
            int k = rndint(5) < 4 ? 4 + rndint(5) : 2 + rndint(2);
            long base = best.n / (2 * k);
            long G = base + 1 + rndint(3);
            long N = 2L * k * G;
            if (N > moore || N > MAXN || G > MAXN) { fails++; continue; }
            if (!make_group((int)G, &grp)) { fails++; continue; }
            LF.k = k;
            LF.G = (int)G;
            LF.nd = d;
            double slice = left * 0.15;
            if (slice < 0.5) slice = 0.5;
            if (slice > 10.0) slice = 10.0;
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (anneal(until)) {
                lift_to_graph(&cand);
                if (cand.n > best.n && is_valid(&cand)) best = cand;
            }
        }
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Return the new graph if it is a larger valid graph, else None."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return best
        return None

    # Exact constructions (calibration cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C bi-Cayley lift annealing, growing from the best graph so far.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
