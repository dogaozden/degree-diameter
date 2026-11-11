"""Bi-Cayley simulated annealing in C over semidirect products, then grow-by-two.

Python builds the exact small constructions (calibration cases return immediately)
and hands the best graph to a C engine. The C engine searches bi-Cayley graphs with
k base vertices per side over Z_m x| Z_k2, scores them by exact eccentricity
(vertex-transitive blocks), and grows the best valid graph by two vertices at a time.
"""
import itertools
import time

import lib


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
# C engine: bi-Cayley annealing (exact check via block eccentricities), then grow.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 *
 * Phase 1: bi-Cayley annealing. K base vertices per side, group G = Z_m x| Z_k2,
 *          layer l pairs A_i with B_{lay[l][i]} via voltage vol[l][i].
 *          Left multiplication is an automorphism, so the graph has diameter <= D
 *          iff every block representative has eccentricity <= D (exact cost).
 * Phase 2: grow-by-two annealing from the best graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 6144
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 8

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best;

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

/* ---------------- groups: Z_m x|_r Z_k2, element (a,b) = a*k2+b ---------------- */

typedef struct {
    int m, k2, r;
    int rp[MAXN];
} Grp;

static Grp grp;

static int gmul(int x, int y) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    return (int)(((long)a + (long)grp.rp[b] * c) % m) * k2 + (b + e) % k2;
}

static int ginv(int x) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    int ta = a % m;
    int c = (int)(((long)((m - ta) % m) * grp.rp[nb]) % m);
    return c * k2 + nb;
}

static void sample_group(int G) {
    int divs[64], nd = 0;
    for (int k2 = 1; k2 <= G && nd < 64; k2++)
        if (G % k2 == 0) divs[nd++] = k2;
    int k2 = divs[rndint(nd)];
    int m = G / k2;
    int r = 1 % m;
    if (m > 2 && rndint(2) == 0) {
        for (int t = 0; t < 50; t++) {
            int c = 1 + rndint(m - 1);
            if (gcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    grp.m = m;
    grp.k2 = k2;
    grp.r = r;
    grp.rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) grp.rp[b] = (int)((long)grp.rp[b - 1] * r % m);
}

/* ---------------- bi-Cayley state ---------------- */

static int curK, curG;
static int lay[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int nbr[MAXN][MAXD];
static int seen[MAXN];
static int bq[MAXN];
static int stampc = 0;
static Graph cand;

static void build_nbr(void) {
    int K = curK, G = curG;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = lay[l][i], s = vol[l][i], si = ginv(s);
            for (int x = 0; x < G; x++) {
                nbr[i * G + x][l] = (K + j) * G + gmul(x, s);
                nbr[(K + j) * G + x][l] = i * G + gmul(x, si);
            }
        }
}

/* Number of vertices within distance D of src. */
static int ball(int src) {
    int h = 0, t = 0;
    stampc++;
    bq[t++] = src;
    seen[src] = stampc;
    for (int lev = 0; lev < D; lev++) {
        int end = t;
        if (h == end) break;
        while (h < end) {
            int v = bq[h++];
            for (int l = 0; l < d; l++) {
                int u = nbr[v][l];
                if (seen[u] != stampc) { seen[u] = stampc; bq[t++] = u; }
            }
        }
    }
    return t;
}

/* Sum over block representatives of unreached vertices (0 iff diameter <= D). */
static long eval_cost(void) {
    int NN = 2 * curK * curG;
    long total = 0;
    for (int b = 0; b < 2 * curK; b++)
        total += NN - ball(b * curG);
    return total;
}

/* True if A_i has pairwise distinct (layer target, voltage) pairs, so the graph is simple. */
static int ok_i(int i) {
    for (int l = 0; l < d; l++)
        for (int l2 = 0; l2 < l; l2++)
            if (lay[l][i] == lay[l2][i] && vol[l][i] == vol[l2][i]) return 0;
    return 1;
}

static int init_random(void) {
    int K = curK, G = curG;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < K; i++) lay[l][i] = perm[i];
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) vol[l][i] = rndint(G);
    for (int i = 0; i < K; i++) {
        long tries = 0;
        while (!ok_i(i)) {
            if (++tries > 200000) return 0;
            vol[rndint(d)][i] = rndint(G);
        }
    }
    return 1;
}

/* Simulated annealing on the current (curK, curG, grp). Returns final cost, or -1. */
static long sa_run(double until, long max_iter, long stall) {
    int K = curK, G = curG;
    if (!init_random()) return -1;
    build_nbr();
    long cost = eval_cost();
    long c0 = cost > 0 ? cost : 1;
    long best_cost = cost, last = 0;
    for (long it = 0; it < max_iter && cost > 0; it++) {
        if ((it & 127) == 0 && now() > until) break;
        if (it - last > stall) break;
        double frac = (double)it / (double)max_iter;
        double T = 0.3 + (1.0 + 0.02 * (double)c0) * (1.0 - frac);
        long c2;
        if (K > 1 && rndint(4) == 0) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int s = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = s;
            if (!ok_i(i1) || !ok_i(i2)) {
                s = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = s;
                continue;
            }
            build_nbr();
            c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost < best_cost) { best_cost = cost; last = it; }
            } else {
                s = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = s;
                build_nbr();
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = vol[l][i], nw = rndint(G);
            if (nw == old) continue;
            vol[l][i] = nw;
            if (!ok_i(i)) { vol[l][i] = old; continue; }
            build_nbr();
            c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost < best_cost) { best_cost = cost; last = it; }
            } else {
                vol[l][i] = old;
                build_nbr();
            }
        }
    }
    return cost;
}

static void build_candidate(void) {
    int K = curK, G = curG, NN = 2 * K * G, AA = K * G;
    cand.n = NN;
    for (int v = 0; v < NN; v++) {
        cand.deg[v] = 0;
        cand.side[v] = v >= AA;
    }
    for (int v = 0; v < AA; v++)
        for (int l = 0; l < d; l++) add_edge(&cand, v, nbr[v][l]);
}

/* Bi-Cayley phase: repeatedly try to beat the current best order. */
static void bicayley_phase(Graph *bp, double until) {
    long moore = moore_bound();
    while (now() < until) {
        if (bp->n + 2 > moore) return;
        int K = 1 + rndint(MAXK);
        int need = bp->n / (2 * K) + 1;
        if (need < d) need = d;
        int G = need;
        if (rndint(3) == 0) G += rndint(need / 25 + 2);
        if (2L * K * G > moore || 2L * K * G > MAXN) continue;
        curK = K;
        curG = G;
        sample_group(G);
        double slice_end = now() + 5.0;
        if (slice_end > until) slice_end = until;
        long c = sa_run(slice_end, 150000, 10000);
        if (c == 0) {
            build_candidate();
            if (cand.n > bp->n && is_valid(&cand)) copy_graph(bp, &cand);
        }
    }
}

/* ---------------- grow-by-two annealing ---------------- */

static int grow_once(const Graph *bp, Graph *work, double until) {
    int n = bp->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, bp);
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

static void grow_search(Graph *bp, double until) {
    static Graph work;
    while (now() < until && bp->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(bp, &work, now() + slice)) copy_graph(bp, &work);
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

    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        bicayley_phase(&best, t0 + (t_end - t0) * 0.75);
        if (best.n > 0) grow_search(&best, t_end);
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
        """Replace the best graph if the new one is larger and valid."""
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

    # Bi-Cayley annealing and grow-by-two search in C, seeded with the best graph so far.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
