"""Combined program: a C bi-Cayley lift search that finds a starting graph, then a new growth
routine that inserts vertex pairs into a valid graph and repairs them by edge annealing.

Growth routine (new): take a valid graph, subdivide an existing edge (a,b) by a new pair
(x in A, y in B) via a-y, x-b, x-y. Then anneal with degree-preserving 2-switches, adds between
deficient vertices, and "split" moves that absorb a deficit by removing an edge (a,b) and adding
a-y, x-b. Cost is the number of vertex pairs at distance > D. Failed attempts are reverted and
the batch size halves, successes double it. Python builds the K_{d,d} fallback and checks output.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (about 35% of time): bi-Cayley lifts over Z_m x|_r Z_k2 with simulated annealing.
 * Phase 2 (rest): growth by pair insertion. Insert k new (A, B) vertex pairs by splitting
 * edges, then anneal on the explicit graph. Moves: 2-switch, fill between deficient vertices,
 * split (removes edge (a,b), adds a-y and x-b to absorb two deficits). Cost = bad pairs.
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
#define PEN 1000L
#define ITERS 30000
#define PATIENCE 6000
#define GROW_STEPS 400
#define GROW_TEMP 0.7
#define GROW_KMAX 32

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void rm_edge(Graph *g, int u, int v) {
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
    int Gs = grp.G, N = NNv;
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
                int v = rndint(N);
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

/* ------------------------------------------------------------------ growth by pair insertion */

typedef struct { int u, v, add; } Op;
static Op oplog[256];
static int nops;
static int dA[MAXN], dB[MAXN], ndA, ndB;

static void op_add(Graph *g, int u, int v) {
    add_edge(g, u, v);
    oplog[nops].u = u; oplog[nops].v = v; oplog[nops].add = 1; nops++;
}

static void op_del(Graph *g, int u, int v) {
    rm_edge(g, u, v);
    oplog[nops].u = u; oplog[nops].v = v; oplog[nops].add = 0; nops++;
}

static void undo_ops(Graph *g) {
    while (nops > 0) {
        Op o = oplog[--nops];
        if (o.add) rm_edge(g, o.u, o.v);
        else add_edge(g, o.u, o.v);
    }
}

/* Lists of vertices with degree < d, split by side. */
static void scan_def(const Graph *g) {
    ndA = ndB = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] < d) {
            if (g->side[v] == 0) dA[ndA++] = v;
            else dB[ndB++] = v;
        }
    }
}

/* Random edge (a, b) with a on side 0; sampled by rejection over vertices. */
static int rand_edge(const Graph *g, int *ea, int *eb) {
    for (int t = 0; t < 400; t++) {
        int a = rndint(g->n);
        if (g->side[a] == 0 && g->deg[a] > 0) {
            *ea = a;
            *eb = g->adj[a][rndint(g->deg[a])];
            return 1;
        }
    }
    return 0;
}

/* Degree-preserving 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static int move_switch(Graph *g) {
    int a1, b1, a2, b2;
    if (!rand_edge(g, &a1, &b1) || !rand_edge(g, &a2, &b2)) return 0;
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(g, a1, b2) || has_edge(g, a2, b1)) return 0;
    op_del(g, a1, b1);
    op_del(g, a2, b2);
    op_add(g, a1, b2);
    op_add(g, a2, b1);
    return 1;
}

/* Add an edge between a deficient A vertex and a deficient B vertex (never hurts diameter). */
static int move_fill(Graph *g) {
    if (ndA == 0 || ndB == 0) return 0;
    int x = dA[rndint(ndA)], y = dB[rndint(ndB)];
    if (has_edge(g, x, y)) return 0;
    op_add(g, x, y);
    return 1;
}

/* Split: remove (a,b), add (a,y) and (x,b). Keeps a and b degrees, gives x and y one each. */
static int move_split(Graph *g) {
    if (ndA == 0 || ndB == 0) return 0;
    int x = dA[rndint(ndA)], y = dB[rndint(ndB)];
    for (int t = 0; t < 40; t++) {
        int a, b;
        if (!rand_edge(g, &a, &b)) return 0;
        if (a == x || b == y) continue;
        if (has_edge(g, a, y) || has_edge(g, x, b)) continue;
        op_del(g, a, b);
        op_add(g, a, y);
        op_add(g, x, b);
        return 1;
    }
    return 0;
}

/* Insert a new A vertex x and B vertex y by splitting a random edge (a,b). */
static void insert_pair(Graph *g) {
    int a, b;
    if (!rand_edge(g, &a, &b)) return;
    int x = g->n, y = g->n + 1;
    g->n += 2;
    g->deg[x] = 0;
    g->deg[y] = 0;
    g->side[x] = 0;
    g->side[y] = 1;
    rm_edge(g, a, b);
    add_edge(g, a, y);
    add_edge(g, x, b);
    add_edge(g, x, y);
}

/* Anneal the explicit graph until cost 0 or the step/time budget ends. Returns final cost. */
static long grow_anneal(Graph *g, int steps, double deadline) {
    long cost = bad_pairs(g);
    for (int t = 0; t < steps && cost > 0; t++) {
        if ((t & 7) == 0 && now() > deadline) break;
        scan_def(g);
        nops = 0;
        int r = rndint(100), ok;
        if (r < 50) ok = move_switch(g);
        else if (r < 75) ok = move_fill(g);
        else ok = move_split(g);
        if (!ok) { nops = 0; continue; }
        long c2 = bad_pairs(g);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / GROW_TEMP)) cost = c2;
        else undo_ops(g);
        nops = 0;
    }
    return cost;
}

/* Adding edges never increases distances, so fill every remaining deficit pair. */
static void greedy_fill(Graph *g) {
    scan_def(g);
    for (int i = 0; i < ndA; i++) {
        int x = dA[i];
        for (int j = 0; j < ndB && g->deg[x] < d; j++) {
            int y = dB[j];
            if (g->deg[y] < d && !has_edge(g, x, y)) add_edge(g, x, y);
        }
    }
}

/* Repeatedly grow the best valid graph; batch size k adapts to success and failure. */
static void grow_loop(Graph *best, double until) {
    static Graph w;
    long lim = moore_bound();
    if (lim > MAXN) lim = MAXN;
    int k = 1;
    while (now() < until) {
        if ((long)best->n + 2 > lim) break;
        copy_graph(&w, best);
        int kk = k;
        while (kk > 1 && (long)w.n + 2L * kk > lim) kk--;
        for (int i = 0; i < kk; i++) insert_pair(&w);
        long c = grow_anneal(&w, GROW_STEPS, until);
        if (c == 0) {
            greedy_fill(&w);
            if (w.n > best->n && is_valid(&w)) {
                copy_graph(best, &w);
                if (k < GROW_KMAX) k *= 2;
            }
        } else {
            k /= 2;
            if (k < 1) k = 1;
        }
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
    if (D >= 2) {
        double span = t_end - t0;
        search_loop(&best, t0 + 0.35 * span);
        grow_loop(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
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
