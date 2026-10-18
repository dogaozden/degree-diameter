"""Combined bipartite degree-diameter search, version with wider bi-Cayley lifts.

Python builds exact or known starting graphs (projective planes, Araujo-Lopez,
W(q) for D=4) and falls back to K_{d,d}. The C engine runs two phases:
1. bi-Cayley voltage lifts over semidirect products Z_m x| Z_k with simulated
   annealing. This version allows up to 8 base blocks per side (bitmasks are
   32-bit), so base graphs can be much larger than before. About 75% of the time.
2. the remaining time, alternating grow-by-two (add one vertex per side from
   d-1 edge swaps, then repair by degree-preserving swaps) with ruin-and-recreate
   (detach a random opposite-side pair, reattach to spare-degree vertices, then
   repair). Ruin-and-recreate keeps the order fixed and walks the plateau.
Every returned graph is checked with lib.is_valid, and the Python fallback is always valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Combined bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * stdout:  "n m" then m lines "u v": the best valid graph found.
 *
 * Phase 1 (about 75% of the time): bi-Cayley lifts. Vertices A_{i,g} = i*G+g and
 *   B_{j,h} = (KB+j)*G+h, with G = Z_m x| Z_k (element (a,b) = a*k+b). Each of the
 *   d layers is a perfect matching of A-blocks to B-blocks (a permutation), with a
 *   voltage s: A_{i,g} ~ B_{j, g*s}. Annealing over voltages and layer permutations;
 *   cost = unreached (block representative, vertex) pairs + penalty per duplicate dart.
 *   Block counts KB up to MAXK = 8, so reach masks are 16-bit wide (uint32 used).
 * Phase 2 (remaining time), alternating:
 *   grow-by-two: add one vertex per side from d-1 swaps, then repair by swaps;
 *   ruin-and-recreate: detach a random pair (x on side 0, y on side 1), reattach
 *   them to vertices with spare degree, then repair by swaps. Size is unchanged.
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
#define MAXM 64
#define PENALTY 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best;

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph basics */

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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Also fills badv[]. */
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

static int GM, GK, GRR;     /* group Z_m x|_r Z_k */
static int GG;              /* order m*k */
static int rpw[MAXM];       /* rpw[b] = r^b mod m */
static int invs[MAXN];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long t = (a + (long)rpw[b] * c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long na = (GM - ((long)rpw[nb] * a) % GM) % GM;
    return (int)(na * GK + nb);
}

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GRR = r; GG = m * k;
    rpw[0] = 1 % m;
    for (int b = 1; b < k; b++) rpw[b] = (int)((long)rpw[b - 1] * r % m);
    for (int x = 0; x < GG; x++) invs[x] = ginv(x);
}

/* Random Z_m x|_r Z_k with m*k about target and 2*k*m <= MAXN. Returns 1 on success. */
static int sample_group(int target) {
    static const int ks[] = {1, 1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 10, 12, 12, 14, 16, 18, 20, 24, 30, 36};
    int nk = (int)(sizeof(ks) / sizeof(ks[0]));
    int k = ks[rndint(nk)];
    if (k > MAXM) k = MAXM;
    int m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int cap = (MAXN / 2) / k;     /* ensures 2*k*m <= MAXN */
    if (m > cap) m = cap;
    if (m < 2) return 0;
    int r = 1;
    if (k == 1) {
        r = 1;
    } else if (k == 2 && rnd01() < 0.3) {
        r = (m > 2) ? m - 1 : 1;   /* dihedral-type: (m-1)^2 = 1 mod m */
    } else if (m > 2) {
        for (int t = 0; t < 60; t++) {
            int c = 2 + rndint(m - 2);
            if (gcd_i(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = c; break; }
        }
    }
    set_group(m, k, r);
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley state */

static int KB;                         /* base size k (blocks per side) */
static int layers[MAXD][MAXK];         /* layers[l][i] = B-block of A-block i */
static int Sv[MAXD][MAXK];             /* voltage of (l, i) */
static int nbr[MAXD][MAXN];
static uint32_t TA[MAXN], TB[MAXN], RCUR[MAXN], ACC[MAXN];
static int defects[MAXN];
static long keyv[MAXD * MAXK];

static void set_dart(int l, int i, int j, int s) {
    int Gs = GG, is = invs[s];
    for (int g = 0; g < Gs; g++) {
        nbr[l][i * Gs + g] = (KB + j) * Gs + gmul(g, s);
        nbr[l][(KB + j) * Gs + g] = i * Gs + gmul(g, is);
    }
}

/* out[v] bit b set iff block representative b is within distance D of v. */
static void compute_reach(uint32_t *out) {
    int N = 2 * KB * GG;
    uint32_t *cur = TA, *nxt = TB;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * KB; b++) cur[b * GG] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    memcpy(out, cur, sizeof(uint32_t) * (size_t)N);
}

static long unreached(const uint32_t *r, int N) {
    long s = 0;
    for (int v = 0; v < N; v++) s += 2 * KB - __builtin_popcount(r[v]);
    return s;
}

static long dupcount(void) {
    int L = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++)
            keyv[L++] = ((long)i * MAXK + layers[l][i]) * (long)MAXN + Sv[l][i];
    long c = 0;
    for (int a = 1; a < L; a++)
        for (int b = 0; b < a; b++)
            if (keyv[a] == keyv[b]) { c++; break; }
    return c;
}

/* Full cost of the current layers/voltages; also leaves the reach in RCUR. */
static long evaluate(void) {
    int N = 2 * KB * GG;
    compute_reach(RCUR);
    return unreached(RCUR, N) + PENALTY * dupcount();
}

/* Simulated annealing over layers and voltages. Returns 1 when cost reaches 0. */
static int anneal(int iters, int patience, double deadline) {
    int N = 2 * KB * GG;
    uint32_t full = (uint32_t)((1ull << (2 * KB)) - 1ull);
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < KB; i++) {
            layers[l][i] = perm[i];
            Sv[l][i] = rndint(GG);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) set_dart(l, i, layers[l][i], Sv[l][i]);
    long cost = evaluate();
    memcpy(ACC, RCUR, sizeof(uint32_t) * (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if (now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (KB >= 2 && rnd01() < 0.25) {
            /* layer-swap move: exchange B-targets of two A-blocks in one layer */
            int l = rndint(d);
            int i1 = rndint(KB), i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            int t1 = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = t1;
            set_dart(l, i1, layers[l][i1], Sv[l][i1]);
            set_dart(l, i2, layers[l][i2], Sv[l][i2]);
            long c2 = evaluate();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(ACC, RCUR, sizeof(uint32_t) * (size_t)N);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                int t2 = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = t2;
                set_dart(l, i1, layers[l][i1], Sv[l][i1]);
                set_dart(l, i2, layers[l][i2], Sv[l][i2]);
            }
            continue;
        }

        /* voltage move: defect-targeted with probability 0.4 */
        int l = 0, i = 0, have = 0;
        if (rnd01() < 0.4) {
            int nb = 0;
            for (int v = 0; v < N; v++)
                if (ACC[v] != full) defects[nb++] = v;
            if (nb > 0) {
                int u = defects[rndint(nb)];
                int block = u / GG;
                l = rndint(d);
                if (block < KB) {
                    i = block;
                } else {
                    int j = block - KB;
                    i = 0;
                    for (int ii = 0; ii < KB; ii++)
                        if (layers[l][ii] == j) { i = ii; break; }
                }
                have = 1;
            }
        }
        if (!have) { l = rndint(d); i = rndint(KB); }

        int old = Sv[l][i];
        int nw = rndint(GG);
        if (nw == old) continue;
        Sv[l][i] = nw;
        set_dart(l, i, layers[l][i], nw);
        long c2 = evaluate();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(ACC, RCUR, sizeof(uint32_t) * (size_t)N);
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            Sv[l][i] = old;
            set_dart(l, i, layers[l][i], old);
        }
    }
    return cost == 0;
}

static void build_bicayley(Graph *g) {
    int A = KB * GG, N = 2 * A;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= A); }
    for (int l = 0; l < d; l++)
        for (int u = 0; u < A; u++) add_edge(g, u, nbr[l][u]);
}

static int trials[MAXK + 1], wins[MAXK + 1];

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

static void bicayley_search(Graph *b, double until) {
    static Graph cand;
    while (now() < until) {
        int k = pick_k();
        int base = b->n / (2 * k);
        int span = base / 8 + 1;
        if (span < 2) span = 2;
        int target = base + 1 + rndint(span);
        if (target < 2) target = 2;
        if (!sample_group(target)) continue;
        if (2 * k * GG <= b->n || 2 * k * GG > MAXN) continue;
        KB = k;
        trials[k]++;
        if (anneal(6000, 1500, until)) {
            wins[k]++;
            build_bicayley(&cand);
            if (cand.n > b->n && is_valid(&cand)) copy_graph(b, &cand);
        }
    }
}

/* ------------------------------------------------------------ repair by swaps */

/* Degree-preserving swap annealing until the diameter is <= D.
 * Returns is_valid(work) on success, 0 on timeout. Degrees and sides are kept. */
static int repair_swaps(Graph *work, double until) {
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
        if (s == v || work->side[s] != work->side[v] || work->deg[s] == 0) continue;
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
            bad_pairs(work);   /* refresh badv for the restored graph */
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

/* ------------------------------------------------------------ grow by two */

static int used[MAXN];
static int stamp = 0;

/* Insert one vertex per side with d-1 edge swaps, then repair. */
static int grow_once(const Graph *bst, Graph *work, double until) {
    int n = bst->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, bst);
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
        if (b >= n || used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    return repair_swaps(work, until);
}

/* ------------------------------------------------------------ ruin and recreate */

/* Detach a random side-0 vertex x and side-1 vertex y, reattach both to vertices
 * with spare degree, then repair. Size is unchanged, so accepted results form a
 * random walk on valid graphs of the same order. */
static int ruin_recreate(const Graph *bst, Graph *work, double until) {
    int n = bst->n;
    copy_graph(work, bst);
    int x = -1, y = -1;
    for (int tr = 0; tr < 10000 && (x < 0 || y < 0); tr++) {
        int c = rndint(n);
        if (work->side[c] == 0 && x < 0) x = c;
        else if (work->side[c] == 1 && y < 0) y = c;
    }
    if (x < 0 || y < 0) return 0;
    while (work->deg[x] > 0) del_edge(work, x, work->adj[x][0]);
    while (work->deg[y] > 0) del_edge(work, y, work->adj[y][0]);
    for (int tr = 0, k = 0; k < d && tr < 40 * n; tr++) {
        int c = rndint(n);
        if (work->side[c] != 1 || work->deg[c] >= d || has_edge(work, x, c)) continue;
        add_edge(work, x, c);
        k++;
    }
    for (int tr = 0, k = 0; k < d && tr < 40 * n; tr++) {
        int c = rndint(n);
        if (work->side[c] != 0 || work->deg[c] >= d || has_edge(work, y, c)) continue;
        add_edge(work, y, c);
        k++;
    }
    return repair_swaps(work, until);
}

/* Alternate growth and ruin-recreate until the deadline. The current graph is
 * always valid, so the state never needs rolling back. */
static void improve(Graph *bst, double until) {
    static Graph wk;
    long turn = 0;
    while (now() < until) {
        double slice = until - now();
        if (slice > 3.0) slice = 3.0;
        if (turn % 3 != 2 && bst->n + 2 <= moore_bound() && bst->n + 2 <= MAXN) {
            if (grow_once(bst, &wk, now() + slice)) copy_graph(bst, &wk);
        } else {
            if (ruin_recreate(bst, &wk, now() + slice)) copy_graph(bst, &wk);
        }
        turn++;
    }
}

/* ------------------------------------------------------------ main */

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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (D < 2) { printf("2 1\n0 1\n"); return 0; }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double split = t0 + (t_end - t0) * 0.75;
        bicayley_search(&best, split);
        improve(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (capped for speed)."""
    for q in range(min(d - 1, 8), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Already at the Moore bound: nothing can beat it.
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 8.0)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
