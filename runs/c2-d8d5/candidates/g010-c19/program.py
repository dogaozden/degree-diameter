"""Bi-Cayley lift annealing in C (semidirect groups Z_m x| Z_k, base sizes 1..8), then grow-by-two repair.

The Python side only handles exact constructions and calibration cases. The search runs in C,
which evaluates each lift by bitmask BFS from the 2k fibre representatives.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 *
 * Phase 1: simulated annealing over bi-Cayley lifts. A lift has base k+k vertices,
 * d perfect matchings (layers) between the two sides, and voltages in a group G of order N
 * (G = Z_m x| Z_k2). Left multiplication is an automorphism, so the cost only needs
 * BFS from the 2k fibre representatives: (representative, vertex) pairs at distance > D.
 * Phase 2: grow by two vertices with repair annealing.
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
#define MAXK 8
#define PEN 1000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph BEST;

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

static int gcd_int(int a, int b) {
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

/* Number of unordered pairs at distance > D. Also fills badv[v] = bad pairs at v. */
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

/* ---------------- groups Z_m x| Z_k2, element (a,b) = a*k2+b ---------------- */

typedef struct {
    int N, m, k2, r;
    int rp[MAXN];   /* rp[b] = r^b mod m */
    int inv[MAXN];
} Grp;

static Grp GR;

/* (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int k2 = GR.k2, m = GR.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    return (int)((a + (long)GR.rp[b] * c) % m) * k2 + (b + e) % k2;
}

static void finish_group(void) {
    int m = GR.m, k2 = GR.k2, N = GR.N;
    GR.rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) GR.rp[b] = (int)((long)GR.rp[b - 1] * GR.r % m);
    for (int s = 0; s < N; s++) {
        int a = s / k2, b = s % k2;
        int nbk = (k2 - b) % k2;
        long t = (long)GR.rp[nbk] * a % m;
        long ap = (m - t) % m;
        GR.inv[s] = (int)ap * k2 + nbk;
    }
}

/* Uniformly sample a group (m, k2, r) of order N by reservoir sampling. */
static int pick_group(int N) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int k2 = 1; k2 <= N; k2++) {
        if (N % k2) continue;
        int m = N / k2;
        if (m == 1) {
            count++;
            if (rnd() % (uint64_t)count == 0) { bm = 1; bk = k2; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_int(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            count++;
            if (rnd() % (uint64_t)count == 0) { bm = m; bk = k2; br = r; }
        }
    }
    if (!count) return 0;
    GR.N = N; GR.m = bm; GR.k2 = bk; GR.r = br;
    finish_group();
    return 1;
}

/* ---------------- bi-Cayley lift state ---------------- */

static int BK, GN;                 /* base size per side, group order */
static int LAY[MAXD][MAXK];        /* LAY[l][i] = B-index matched to A_i in layer l */
static int SV[MAXD][MAXK];         /* voltage of dart (l, i) */
static int nb[MAXD][MAXN];         /* nb[l][v]: neighbour of v in layer l */
static uint64_t RX0[MAXN], RX1[MAXN];

/* A_{i,g} ~ B_{j, g*s}. Rebuild neighbour arrays of layer l. */
static void build_layer(int l) {
    int N = GN;
    for (int i = 0; i < BK; i++) {
        int j = LAY[l][i], s = SV[l][i];
        int A0 = i * N, B0 = (BK + j) * N;
        for (int g = 0; g < N; g++) {
            int h = gmul(g, s);
            nb[l][A0 + g] = B0 + h;
            nb[l][B0 + h] = A0 + g;
        }
    }
}

/* Sum over block representatives b of (number of vertices NOT within D of rep b). */
static long unreached(void) {
    int V = 2 * BK * GN;
    uint64_t *R = RX0, *Q = RX1;
    for (int v = 0; v < V; v++) R[v] = 0;
    for (int b = 0; b < 2 * BK; b++) R[b * GN] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < V; v++) {
            uint64_t x = R[v];
            for (int l = 0; l < d; l++) x |= R[nb[l][v]];
            Q[v] = x;
            if (x != R[v]) changed = 1;
        }
        uint64_t *t = R; R = Q; Q = t;
        if (!changed) break;
    }
    long cnt = 0;
    for (int v = 0; v < V; v++) cnt += __builtin_popcountll(R[v]);
    return (long)(2 * BK) * V - cnt;
}

/* Pairs of layers sharing the same (partner, voltage) at some A vertex: parallel edges. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < BK; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (LAY[l][i] == LAY[l2][i] && SV[l][i] == SV[l2][i]) c++;
    return c;
}

static void swap_int(int *a, int *b) { int t = *a; *a = *b; *b = t; }

static int sa_trial(long maxit, long patience, double deadline) {
    int N = GN;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < BK; i++) perm[i] = i;
        for (int i = BK - 1; i > 0; i--) swap_int(&perm[i], &perm[rndint(i + 1)]);
        for (int i = 0; i < BK; i++) { LAY[l][i] = perm[i]; SV[l][i] = rndint(N); }
        build_layer(l);
    }
    long cost = unreached() + PEN * dup_count();
    double c0 = (double)(cost > 1 ? cost : 1);
    long best = cost, last = 0;
    for (long t = 0; t < maxit && cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)maxit);
        if (temp < 0.3) temp = 0.3;
        int l = rndint(d);
        if (BK >= 2 && rnd01() < 0.25) {
            int i1 = rndint(BK), i2 = rndint(BK - 1);
            if (i2 >= i1) i2++;
            swap_int(&LAY[l][i1], &LAY[l][i2]);
            build_layer(l);
            long c2 = unreached() + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                swap_int(&LAY[l][i1], &LAY[l][i2]);
                build_layer(l);
            }
        } else {
            int i = rndint(BK);
            int old = SV[l][i], nw = rndint(N);
            if (nw == old) continue;
            SV[l][i] = nw;
            build_layer(l);
            long c2 = unreached() + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                SV[l][i] = old;
                build_layer(l);
            }
        }
    }
    return cost == 0;
}

static void graph_from_lift(Graph *g) {
    int B = BK * GN;
    g->n = 2 * B;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= B; }
    for (int a = 0; a < B; a++)
        for (int l = 0; l < d; l++) add_edge(g, a, nb[l][a]);
}

static void lift_search(double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int k = 1 + rndint(MAXK);
        long target = BEST.n + 2;
        long Nmin = (target + 2L * k - 1) / (2L * k);
        long N = Nmin + rndint((int)(Nmin / 40 + 2));
        if (N < d) N = d;
        if (2L * k * N > moore || 2L * k * N > MAXN) {
            if (++fails > 5000) return;
            continue;
        }
        if (!pick_group((int)N)) continue;
        BK = k;
        GN = (int)N;
        long V = 2L * k * N;
        long maxit = 12000 + 3000000L / V;
        long patience = maxit / 3;
        double dl = now() + 6.0;
        if (dl > until) dl = until;
        if (sa_trial(maxit, patience, dl)) {
            graph_from_lift(&cand);
            if (cand.n > BEST.n && is_valid(&cand)) copy_graph(&BEST, &cand);
        }
    }
}

/* ---------------- grow by two vertices with repair ---------------- */

static int cbad[MAXN];
static int blist[MAXN];

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
    memcpy(cbad, badv, sizeof(int) * work->n);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int nbl = 0;
        for (int w = 0; w < work->n; w++)
            if (cbad[w]) blist[nbl++] = w;
        if (nbl == 0) break;
        int v = rnd01() < 0.8 ? blist[rndint(nbl)] : rndint(work->n);
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
        long nb2 = bad_pairs(work);
        if (nb2 <= bad || rnd01() < exp((double)(bad - nb2) / T)) {
            bad = nb2;
            memcpy(cbad, badv, sizeof(int) * work->n);
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

    if (d < 1 || D < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }
    read_start(&BEST);
    if (BEST.n == 0) complete_bipartite(&BEST);
    if (D >= 2 && BEST.n < moore_bound()) {
        double split = t0 + (t_end - t0) * 0.75;
        lift_search(split);
        grow_search(&BEST, t_end);
    }
    if (!is_valid(&BEST)) complete_bipartite(&BEST);
    print_graph(&BEST);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, 0.88 * time_limit - 2.0)
    end = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
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

    # Search (C): bi-Cayley lift annealing, then grow-by-two repair.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                n_out, e_out = lib.parse_graph_text(text)
                consider(n_out, e_out)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
