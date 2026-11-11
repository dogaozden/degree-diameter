"""Bipartite degree-diameter search: bi-Cayley lift annealing, then insertion-repair growth.

New in this version: a non-lift growth phase. Starting from the best regular lift, it inserts
new vertex pairs by edge subdivision (removing d edges and reattaching their endpoints to the
new pair, which keeps the graph d-regular and bipartite). It then repairs diameter with
degree-preserving double edge swaps. The repair cost counts (sample source, vertex) pairs at
distance > D, using 256 sampled sources packed in bitsets, so one evaluation costs about 0.3 ms.
When the sampled cost reaches 0, an exact all-pairs bitset check runs. Any failing vertices
are added to the sample, so the sample adapts. Python builds the start graphs and keeps a
valid fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search engine.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: bi-Cayley lifts over Z_m x| Z_k2 with simulated annealing on layer permutations.
 * Phase 2: insertion-repair growth on the best regular graph (see grow_attempt).
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
#define MAXK 8
#define MAXE (MAXN * MAXD / 2)
#define PEN 1000L
#define ITERS 30000
#define PATIENCE 6000
#define SAMP 256
#define SAMPW 4
#define GROW_ITERS 4000
#define GROW_STALE 1200

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

/* Regular bipartite graph with explicit edge list, used by the growth phase. */
typedef struct {
    int n, M;
    unsigned char side[MAXN];
    int adj[MAXN][MAXD];
    int adjE[MAXN][MAXD];   /* adjE[v][k] = id of the edge to adj[v][k] */
    int eu[MAXE], ev[MAXE]; /* eu = side-0 end, ev = side-1 end */
} State;

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

/* ------------------------------------------------------------------ generic graph */

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
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
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    {
        long mb = moore_bound();
        if ((long)g->n > mb) return 0;
    }
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            if (!has_edge(g, u, v)) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* Read "n m" + edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element (a, b) is the int a*k2 + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k2). */
typedef struct {
    int m, k2, r, G;
    long rp[64];        /* rp[b] = r^b mod m */
    int inv[MAXN];
} Grp;
static Grp grp;

static int gmul(int x, int y) {
    long m = grp.m;
    int k2 = grp.k2;
    long a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    return (int)(((a + grp.rp[b] * c) % m) * k2 + (b + e) % k2);
}

/* Inverse of x: (a,b)^{-1} = (-r^{-b} a, -b). */
static int ginv(int x) {
    long m = grp.m;
    int k2 = grp.k2;
    long a = x / k2, b = x % k2;
    int nb = (k2 - (int)b) % k2;
    long na = ((m - grp.rp[nb]) % m) * a % m;
    return (int)(na * k2 + nb);
}

/* Random (m, k2, r) with m*k2 >= target, m >= 2, gcd(r, m) = 1, r^k2 = 1 mod m. */
static int sample_group(long target) {
    static const int ks[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = ks[rndint(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > MAXN) continue;
        long r = 1;
        if (k2 == 1 || m == 2) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1; /* dihedral-type */
        } else {
            long found = -1;
            for (int t = 0; t < 60 && found < 0; t++) {
                long c = 2 + rndint((int)(m - 2));
                if (gcd_i((int)c, (int)m) == 1 && powmod(c, k2, m) == 1 % m) found = c;
            }
            if (found < 0) continue;
            r = found;
        }
        grp.m = (int)m;
        grp.k2 = k2;
        grp.r = (int)r;
        grp.G = (int)(m * k2);
        grp.rp[0] = 1 % m;
        for (int b = 1; b < k2; b++) grp.rp[b] = grp.rp[b - 1] * r % m;
        for (int x = 0; x < grp.G; x++) grp.inv[x] = ginv(x);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ bi-Cayley lifts */

static int K;                    /* blocks per side */
static int NNv;                  /* vertices = 2*K*G */
static int lay[MAXD][MAXK];      /* lay[l][i] = B-block paired with A-block i in layer l */
static int Sv[MAXD][MAXK];       /* voltage of dart (l, i) */
static int nbr[MAXD][MAXN];      /* nbr[l][v] = neighbour of v in layer l */

static void set_dart(int l, int i) {
    int j = lay[l][i], s = Sv[l][i];
    int Gs = grp.G;
    for (int g = 0; g < Gs; g++) {
        nbr[l][i * Gs + g] = (K + j) * Gs + gmul(g, s);
        nbr[l][(K + j) * Gs + g] = i * Gs + gmul(g, grp.inv[s]);
    }
}

static void build_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Number of same-(i, j, s) duplicate darts (multi-edges). */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && Sv[l1][i] == Sv[l2][i]) c++;
    return c;
}

/* Bitmask reach from the 2K representatives, computed for all vertices.
 * Returns the number of unreached (representative, vertex) pairs. */
static long compute_reach(uint32_t *out) {
    static uint32_t tA[MAXN], tB[MAXN];
    int N = NNv, Gs = grp.G;
    uint32_t *cur = tA, *nx = tB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * Gs] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nx[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *t = cur;
        cur = nx;
        nx = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) {
        out[v] = cur[v];
        unr += 2 * K - __builtin_popcount(cur[v]);
    }
    return unr;
}

/* Simulated annealing over layer permutations and voltages.
 * Returns 1 if the lift has diameter <= D with no multi-edges; nbr then holds it. */
static int anneal(double deadline) {
    int Gs = grp.G;
    uint32_t full = (1u << (2 * K)) - 1u;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            lay[l][i] = perm[i];
            Sv[l][i] = rndint(Gs);
        }
    }
    build_all();
    static uint32_t bufA[MAXN], bufB[MAXN];
    uint32_t *cur = bufA, *cand = bufB;
    long cost = compute_reach(cur) + PEN * dupcount();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;

    for (int t = 0; t < ITERS && cost != 0; t++) {
        if (t - last > PATIENCE) break;
        if ((t & 15) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / ITERS);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            /* layer-swap move: exchange the B-targets of two A-blocks in one layer */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = compute_reach(cand) + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *x = cur; cur = cand; cand = x;
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        /* voltage move: defect-targeted with probability 0.4, otherwise uniform */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int u = -1;
            for (int tries = 0; tries < 20; tries++) {
                int v = rndint(N_ANY_LIMIT(NNv));
                if (cur[v] != full) { u = v; break; }
            }
            if (u >= 0) {
                int blk = u / Gs;
                l = rndint(d);
                if (blk < K) {
                    i = blk;
                } else {
                    for (int q = 0; q < K; q++)
                        if (lay[l][q] == blk - K) { i = q; break; }
                }
                if (i < 0) continue;
            }
        }
        if (l < 0) { l = rndint(d); i = rndint(K); }

        int ns = rndint(Gs), os = Sv[l][i];
        if (ns == os) continue;
        Sv[l][i] = ns;
        set_dart(l, i);
        long c2 = compute_reach(cand) + PEN * dupcount();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint32_t *x = cur; cur = cand; cand = x;
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            Sv[l][i] = os;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

/* Turn the accepted lift in nbr into a graph. A-blocks are 0..K*G-1 (side 0), B-blocks follow. */
static void graph_from_lift(Graph *g) {
    int N = NNv, Gs = grp.G;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= K * Gs);
    }
    for (int v = 0; v < K * Gs; v++)
        for (int l = 0; l < d; l++) add_edge(g, v, nbr[l][v]);
}

/* Bandit over K, growing the best graph whenever a lift beats it. */
static void search_loop(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    long trials[MAXK + 1], wins[MAXK + 1];
    for (int q = 0; q <= MAXK; q++) { trials[q] = 0; wins[q] = 0; }

    while (now() < until) {
        if ((long)best->n + 2 > moore) break;
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(4);
        } else {
            double bestv = -1.0;
            k = 1;
            for (int q = 1; q <= 4; q++) {
                double v = (wins[q] + 1.0) / (trials[q] + 2.0) + 0.02 * rnd01();
                if (v > bestv) { bestv = v; k = q; }
            }
        }
        long base = best->n / (2 * k);
        long target = base + 1 + rndint((int)(base / 8 + 2));
        if (!sample_group(target)) continue;
        long N = 2L * k * grp.G;
        if (N <= best->n || N > moore || N > MAXN) continue;

        K = k;
        NNv = (int)N;
        trials[k]++;
        if (anneal(until)) {
            wins[k]++;
            graph_from_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ regular state */

static int st_slot(const State *s, int v, int u) {
    for (int k = 0; k < d; k++)
        if (s->adj[v][k] == u) return k;
    return -1;
}

static int st_has(const State *s, int u, int v) { return st_slot(s, u, v) >= 0; }

static void copy_state(State *dst, const State *src) {
    dst->n = src->n;
    dst->M = src->M;
    for (int v = 0; v < src->n; v++) {
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * d);
        memcpy(dst->adjE[v], src->adjE[v], sizeof(int) * d);
    }
    memcpy(dst->eu, src->eu, sizeof(int) * src->M);
    memcpy(dst->ev, src->ev, sizeof(int) * src->M);
}

/* Load a d-regular graph into the edge-list state. Returns 0 if it is not d-regular. */
static int state_from_graph(State *s, const Graph *g) {
    s->n = g->n;
    s->M = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] != d) return 0;
        s->side[v] = g->side[v];
        memcpy(s->adj[v], g->adj[v], sizeof(int) * d);
    }
    for (int v = 0; v < g->n; v++) {
        if (s->side[v] != 0) continue;
        for (int k = 0; k < d; k++) {
            int u = s->adj[v][k];
            int j = st_slot(s, u, v);
            if (j < 0 || s->M >= MAXE) return 0;
            int id = s->M++;
            s->eu[id] = v;
            s->ev[id] = u;
            s->adjE[v][k] = id;
            s->adjE[u][j] = id;
        }
    }
    return 1;
}

static void state_to_graph(Graph *g, const State *s) {
    g->n = s->n;
    for (int v = 0; v < s->n; v++) {
        g->deg[v] = d;
        g->side[v] = s->side[v];
        memcpy(g->adj[v], s->adj[v], sizeof(int) * d);
    }
}

/* Degree-preserving double edge swap. e1 = (a1,b1), e2 = (a2,b2) become (a1,b2), (a2,b1).
 * Calling it again on the same pair undoes the move. Returns 0 if the move is not allowed. */
static int st_swap(State *s, int e1, int e2) {
    if (e1 == e2) return 0;
    int a1 = s->eu[e1], b1 = s->ev[e1], a2 = s->eu[e2], b2 = s->ev[e2];
    if (a1 == a2 || b1 == b2) return 0;
    if (st_has(s, a1, b2) || st_has(s, a2, b1)) return 0;
    int ka1 = st_slot(s, a1, b1), kb1 = st_slot(s, b1, a1);
    int ka2 = st_slot(s, a2, b2), kb2 = st_slot(s, b2, a2);
    if (ka1 < 0 || kb1 < 0 || ka2 < 0 || kb2 < 0) return 0;
    s->adj[a1][ka1] = b2;                       /* e1 becomes (a1, b2) */
    s->adj[b1][kb1] = a2; s->adjE[b1][kb1] = e2; /* b1 now sees a2 through e2 */
    s->adj[a2][ka2] = b1; s->adjE[a2][ka2] = e2; /* e2 becomes (a2, b1) */
    s->adj[b2][kb2] = a1; s->adjE[b2][kb2] = e1; /* b2 now sees a1 through e1 */
    s->ev[e1] = b2;
    s->ev[e2] = b1;
    return 1;
}

/* Insertion by edge subdivision: pick d edges with distinct A-ends and distinct B-ends.
 * Edge (x_i, y_i) becomes (a, y_i), and the new edge (x_i, b) is added, where a is a new
 * A-vertex and b a new B-vertex. Every old vertex keeps its degree, and a and b get degree d. */
static int st_insert_pair(State *s) {
    if (s->n + 2 > MAXN || s->M + d > MAXE || s->M < d) return 0;
    int ids[MAXD];
    int ok = 0;
    for (int tries = 0; tries < 2000 && !ok; tries++) {
        for (int i = 0; i < d; i++) ids[i] = rndint(s->M);
        ok = 1;
        for (int i = 0; i < d && ok; i++)
            for (int j = 0; j < i; j++)
                if (s->eu[ids[i]] == s->eu[ids[j]] || s->ev[ids[i]] == s->ev[ids[j]]) {
                    ok = 0;
                    break;
                }
    }
    if (!ok) return 0;
    int a = s->n, b = s->n + 1;
    s->n += 2;
    s->side[a] = 0;
    s->side[b] = 1;
    for (int i = 0; i < d; i++) {
        int e = ids[i];
        int x = s->eu[e], y = s->ev[e];
        int kx = st_slot(s, x, y), ky = st_slot(s, y, x);
        int ne = s->M + i;
        s->adj[x][kx] = b; s->adjE[x][kx] = ne;
        s->adj[y][ky] = a; s->adjE[y][ky] = e;
        s->eu[e] = a;                    /* e is now (a, y) */
        s->eu[ne] = x; s->ev[ne] = b;    /* new edge (x, b) */
        s->adj[a][i] = y; s->adjE[a][i] = e;
        s->adj[b][i] = x; s->adjE[b][i] = ne;
    }
    s->M += d;
    return 1;
}

/* Sampled repair cost: for each sampled source s and each vertex v, count pairs at distance > D.
 * Packs the 256 samples into 4 words per vertex and propagates D rounds. bad[v] receives the
 * per-vertex counts when bad != NULL. */
static int samp[SAMP];
static uint64_t RX[MAXN][SAMPW], RY[MAXN][SAMPW];
static long badv[MAXN];
static long perv[MAXN];
static uint64_t XA[MAXN * MAXW], XB[MAXN * MAXW];

static long samp_cost(const State *s, long *bad) {
    int n = s->n;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < SAMPW; w++) RX[v][w] = 0;
    for (int k = 0; k < SAMP; k++) RX[samp[k]][k >> 6] |= 1ULL << (k & 63);
    uint64_t (*cur)[SAMPW] = RX, (*nx)[SAMPW] = RY;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < SAMPW; w++) {
                uint64_t x = cur[v][w];
                for (int k = 0; k < d; k++) x |= cur[s->adj[v][k]][w];
                nx[v][w] = x;
            }
        }
        uint64_t (*t)[SAMPW] = cur;
        cur = nx;
        nx = t;
    }
    long c = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < SAMPW; w++) pc += __builtin_popcountll(cur[v][w]);
        long b = SAMP - pc;
        c += b;
        if (bad) bad[v] = b;
    }
    return c;
}

/* Exact unreached pair count. per[v] receives the number of vertices at distance > D from v.
 * Returns the number of unordered bad pairs. */
static long exact_unreached(const State *s, long *per) {
    int n = s->n, W = (n + 63) / 64;
    uint64_t *cur = XA, *nx = XB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nx + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < d; k++) {
                const uint64_t *q = cur + (size_t)s->adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= q[w];
            }
        }
        uint64_t *t = cur;
        cur = nx;
        nx = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(row[w]);
        per[v] = n - c;
        tot += n - c;
    }
    return tot / 2;
}

/* Repair the state with annealing on double swaps. Returns 1 when the exact check passes. */
static int grow_attempt(State *s, double deadline) {
    int n = s->n;
    for (int k = 0; k < SAMP; k++) samp[k] = rndint(n);
    long cost = samp_cost(s, badv);
    long best_cost = cost;
    int stale = 0;
    for (int it = 0; it < GROW_ITERS; it++) {
        if (now() > deadline) break;
        if (cost == 0) {
            if (exact_unreached(s, perv) == 0) return 1;
            /* Sample too small: add sources that have bad pairs, then re-evaluate. */
            int added = 0;
            for (int tries = 0; tries < 20000 && added < 16; tries++) {
                int v = rndint(n);
                if (perv[v] > 0) { samp[rndint(SAMP)] = v; added++; }
            }
            if (added == 0) break;
            cost = samp_cost(s, badv);
            best_cost = cost;
            stale = 0;
            continue;
        }
        if (stale > GROW_STALE) break;
        double T = 2.0 * (1.0 - (double)it / GROW_ITERS) + 0.1;
        int v = rndint(n);
        for (int tries = 0; tries < 8 && badv[v] == 0; tries++) v = rndint(n);
        int e1 = s->adjE[v][rndint(d)];
        int e2 = rndint(s->M);
        if (!st_swap(s, e1, e2)) continue;
        long c2 = samp_cost(s, badv);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < best_cost) { best_cost = cost; stale = 0; }
            else stale++;
        } else {
            st_swap(s, e1, e2);   /* undo */
            stale++;
        }
    }
    return 0;
}

/* Repeatedly insert 1-3 vertex pairs into a copy of the best state and repair it. */
static void grow_phase(State *best, double until) {
    static State cur;
    long moore = moore_bound();
    while (now() < until) {
        if ((long)best->n + 2 > moore) break;
        copy_state(&cur, best);
        int p = 1 + rndint(3);
        if ((long)best->n + 2 * p > moore) p = 1;
        int okp = 1;
        for (int i = 0; i < p && okp; i++) okp = st_insert_pair(&cur);
        if (!okp) continue;
        if (grow_attempt(&cur, until)) copy_state(best, &cur);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D <= 0) { printf("1 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }
    if (d > MAXD) { printf("0 0\n"); return 0; }

    static Graph best;
    read_start(&best);
    double span = t_end - t0;
    if (D >= 2) search_loop(&best, t0 + 0.4 * span);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && d >= 2) {
        static State sb;
        if (state_from_graph(&sb, &best)) {
            grow_phase(&sb, t_end);
            static Graph out;
            state_to_graph(&out, &sb);
            if (out.n > best.n && is_valid(&out)) best = out;
        }
    }
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best exact or record graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))  # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    if start is not None and best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing larger exists

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
