"""Combined program: C-native bi-Cayley voltage-lift annealing over semidirect products
Z_m x|_r Z_k2, followed by a C grow-by-two phase on the best graph found.

New in this version: the lift search runs entirely in C. Group multiplication and inverses
are computed on the fly (no n^2 tables), so large groups are cheap. Reachability uses one
bitmask per vertex over the 2k block representatives, and the annealer keeps the accepted
reach state separately from the candidate state, so block-targeted moves stay consistent
after rejections. Each lift is regular (every layer is a block permutation with voltages),
so every accepted lift has all degrees equal to d.

Every returned graph is checked with lib.is_valid. K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Lift + grow engine.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
 *
 * Phase A (lift_search): bi-Cayley lifts over Z_m x|_r Z_k2 with k block pairs per side.
 *   Layer l pairs A-block i with B-block p = lay[l][i] through voltage s: A_{i,x} ~ B_{p,x*s}.
 *   Every layer is a permutation of blocks, so the lift is d-regular. Simulated annealing
 *   minimises (unreached block pairs) + PENALTY * (duplicate darts).
 * Phase B (grow_search): insert two vertices with spare degree, then anneal swaps.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define PENALTY 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* Number of unordered pairs at distance > D; also sets badv[v]. */
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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

static Graph gbest, gwork, gcand;

/* ------------------------------------------------------------------ groups */

static int gm_m, gm_k, gm_G;
static int gm_pow[64];
static int SINV[MAXN];

/* (a,b)*(c,e) = (a + r^b c, b + e) with element code a*k + b. */
static int gmul(int x, int y) {
    int a = x / gm_k, b = x % gm_k, c = y / gm_k, e = y % gm_k;
    return ((a + gm_pow[b] * c) % gm_m) * gm_k + (b + e) % gm_k;
}

/* Inverse of (a,b) is (-r^{-b} a, -b), with r^{-b} = r^{(k-b) mod k}. */
static int ginv(int x) {
    int a = x / gm_k, b = x % gm_k;
    int nb = (gm_k - b) % gm_k;
    long t = ((long)gm_pow[nb] * a) % gm_m;
    int na = (int)((gm_m - t) % gm_m);
    return na * gm_k + nb;
}

static void set_group(int m, int k2, int r) {
    gm_m = m;
    gm_k = k2;
    gm_G = m * k2;
    gm_pow[0] = 1 % m;
    for (int t = 1; t < k2; t++) gm_pow[t] = (int)((long)gm_pow[t - 1] * r % m);
    for (int s = 0; s < gm_G; s++) SINV[s] = ginv(s);
}

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Random Z_m x|_r Z_k2 with m*k2 >= target. */
static int sample_group(int target, int *pm, int *pk2, int *pr) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int att = 0; att < 200; att++) {
        int k2 = K2S[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1 && m > 2 && rnd01() < 0.7) {
            int ok = 0;
            for (int tr = 0; tr < 60; tr++) {
                int c = 2 + rndint(m - 2);
                if (gcd_l(c, m) == 1 && powmod_l(c, k2, m) == 1 % m) { r = c; ok = 1; break; }
            }
            if (!ok) continue;
        }
        *pm = m;
        *pk2 = k2;
        *pr = r;
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ lifts */

static int LK;                       /* block pairs per side */
static int nbr[MAXD][MAXN];          /* nbr[l][v]: layer-l neighbour of v */
static int lay[MAXD][MAXK];          /* lay[l][i]: B-block matched to A-block i in layer l */
static int SV[MAXD][MAXK];           /* voltage of dart (l, i) */
static uint16_t bufA[MAXN], bufB[MAXN], tmpb[MAXN];
static uint16_t *cur = bufA, *nw = bufB;   /* accepted and candidate reach states */

/* Write layer l for A-block i (to B-block p, voltage s): A_{i,x} ~ B_{p,x*s}. */
static void set_dart(int l, int i, int p, int s) {
    int G = gm_G, si = SINV[s];
    int bi = i * G, bp = (LK + p) * G;
    for (int x = 0; x < G; x++) {
        nbr[l][bi + x] = bp + gmul(x, s);
        nbr[l][bp + x] = bi + gmul(x, si);
    }
}

/* Reach bitmask per vertex over the 2K block representatives (vertex b*G). */
static long lift_reach(uint16_t *out) {
    int G = gm_G, nb = 2 * LK, N = nb * G;
    memset(out, 0, sizeof(uint16_t) * (size_t)N);
    for (int b = 0; b < nb; b++) out[b * G] = (uint16_t)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t x = out[v];
            for (int l = 0; l < d; l++) x |= out[nbr[l][v]];
            tmpb[v] = x;
            changed |= (x != out[v]);
        }
        memcpy(out, tmpb, sizeof(uint16_t) * (size_t)N);
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += nb - __builtin_popcount((unsigned)out[v]);
    return unr;
}

/* Duplicate darts: same (i, p, s) in two layers gives the same edge set. */
static long dupcount(void) {
    long c = 0;
    for (int l = 1; l < d; l++)
        for (int i = 0; i < LK; i++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l2][i] == lay[l][i] && SV[l2][i] == SV[l][i]) { c++; break; }
    return c;
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < LK; i++) lay[l][i] = i;
        for (int i = LK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < LK; i++) {
            SV[l][i] = rndint(gm_G);
            set_dart(l, i, lay[l][i], SV[l][i]);
        }
    }
}

/* Anneal the current group's lift. Returns 1 on zero cost (state left in cur/nw/lay/SV). */
static int anneal_lift(double deadline, long iters, long patience) {
    int G = gm_G, N = 2 * LK * G;
    uint16_t full = (uint16_t)((1u << (2 * LK)) - 1);
    random_lift();
    long cost = lift_reach(cur) + PENALTY * dupcount();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long last = 0, bestc = cost;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        long c2;
        if (LK >= 2 && rnd01() < 0.25) {
            /* Move: swap the B-blocks of two A-blocks inside one layer. */
            int l = rndint(d), i1 = rndint(LK), i2 = rndint(LK - 1);
            if (i2 >= i1) i2++;
            int tp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tp;
            set_dart(l, i1, lay[l][i1], SV[l][i1]);
            set_dart(l, i2, lay[l][i2], SV[l][i2]);
            c2 = lift_reach(nw) + PENALTY * dupcount();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                uint16_t *q = cur; cur = nw; nw = q;
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tp;
                set_dart(l, i1, lay[l][i1], SV[l][i1]);
                set_dart(l, i2, lay[l][i2], SV[l][i2]);
            }
        } else {
            /* Move: change one voltage, biased toward an unreached vertex's block. */
            int l, i = 0, v = -1;
            if (rnd01() < 0.4) {
                for (int tr = 0; tr < 30; tr++) {
                    int c = rndint(N);
                    if (cur[c] != full) { v = c; break; }
                }
            }
            if (v >= 0) {
                int blk = v / G;
                l = rndint(d);
                if (blk < LK) i = blk;
                else {
                    for (int j = 0; j < LK; j++)
                        if (lay[l][j] == blk - LK) { i = j; break; }
                }
            } else {
                l = rndint(d);
                i = rndint(LK);
            }
            int old = SV[l][i], nv = rndint(G);
            if (nv == old) continue;
            SV[l][i] = nv;
            set_dart(l, i, lay[l][i], nv);
            c2 = lift_reach(nw) + PENALTY * dupcount();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                uint16_t *q = cur; cur = nw; nw = q;
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                SV[l][i] = old;
                set_dart(l, i, lay[l][i], old);
            }
        }
    }
    return cost == 0;
}

/* Build the lift graph (N = 2*LK*G vertices, all degrees d) into gcand. */
static void extract_lift(void) {
    int G = gm_G, N = 2 * LK * G;
    gcand.n = N;
    for (int v = 0; v < N; v++) {
        gcand.deg[v] = 0;
        gcand.side[v] = (unsigned char)(v < LK * G ? 0 : 1);
    }
    for (int l = 0; l < d; l++)
        for (int u = 0; u < LK * G; u++) add_edge(&gcand, u, nbr[l][u]);
}

static int pick_k(const long *trials, const long *wins) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

static void lift_search(double until) {
    long trials[MAXK + 1], wins[MAXK + 1];
    memset(trials, 0, sizeof trials);
    memset(wins, 0, sizeof wins);
    double floor_goal = 2.0 * d + 2.0;
    double goal = gbest.n * 1.05;
    if (goal < floor_goal) goal = floor_goal;
    while (now() < until) {
        if (gbest.n + 2 > MAXN) return;
        if (goal > MAXN - 64) goal = MAXN - 64;
        int k = pick_k(trials, wins);
        int target = (int)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        long N = 2L * k * m * k2;
        if (N > MAXN) continue;
        if (N <= gbest.n) {
            if (goal < gbest.n * 1.02) goal = gbest.n * 1.02;
            continue;
        }
        LK = k;
        set_group(m, k2, r);
        trials[k]++;
        if (anneal_lift(until, 8000, 2500)) {
            extract_lift();
            if (gcand.n > gbest.n && is_valid(&gcand)) {
                copy_graph(&gbest, &gcand);
                wins[k]++;
                goal = gbest.n * 1.06;
            } else {
                goal = goal * 0.99;
                if (goal < gbest.n * 1.02) goal = gbest.n * 1.02;
            }
        } else {
            goal = goal * 0.99;
            if (goal < gbest.n * 1.02) goal = gbest.n * 1.02;
        }
    }
}

/* ------------------------------------------------------------------ grow */

static int used[MAXN];
static int stamp = 0;

/* One grow-by-two attempt from best; on success work holds n+2 valid vertices. */
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

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
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
    t_end = t0 + limit * 0.93 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    gbest.n = 0;
    read_start(&gbest);

    double lift_frac = gbest.n > 3000 ? 0.6 : 0.75;
    double lift_end = t0 + lift_frac * (t_end - t0);
    lift_search(lift_end);

    if (gbest.n > 0) grow_search(t_end);
    if (gbest.n == 0 || !is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# Saturation (Python): greedily add missing bipartite edges between deficient vertices.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices; returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    """Saturate, but fall back to the input if anything goes wrong or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider_saturated(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # One C run: lift annealing (C-native), then grow-by-two from the best graph.
    budget = 0.9 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 2.0)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
