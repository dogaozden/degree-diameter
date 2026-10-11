"""Combined search: lift search over two group families, then grow-by-pairs annealing.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.

The new construction in this version is a broader lift family. Each lift is a bipartite
voltage lift over a group G of order G = |A| * |Q| * |C|, where:
  - type 0 (metacyclic, as before): A = Z_m, Q = Z_k2 acting by a unit r with r^k2 = 1 mod m;
  - type 1 (new, non-metacyclic in general): A = F_p^k (elementary abelian), Q = Z_Q acting
    by a matrix M over F_p with M^Q = I, times a cyclic factor C = Z_c.
Type 1 reaches groups such as Z_2^3 x| Z_7, GL-type actions, and abelian products that
metacyclic families cannot express. Type 0 is still sampled (30%) as a safe fallback.

A base with kb vertices per side and d darts per base vertex gives a d-regular bipartite lift.
Left multiplication is an automorphism, so the diameter is <= D iff a BFS of depth D from
each of the 2kb class representatives reaches everything. Voltages and layer permutations are
annealed on the number of unreached pairs. Escalations: more annealing steps and a higher
target group order after repeated failures.

The best lift is then grown by repair annealing (grow by one or two pairs, degree-preserving
edge steals, annealing repair), with plateau walks that perturb the best graph at fixed order.
Every output is re-checked in C and in Python, and K_{d,d} or the known start is the fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): base with kb vertices per side, d darts out of each base vertex.
 *   Dart (i, j, s) joins A_{i,x} to B_{j, x*s} for group element x. The group is either
 *   metacyclic (type 0) or elementary-abelian-by-cyclic times cyclic (type 1), see groups below.
 *   Left multiplication is an automorphism, so the diameter is <= D iff a BFS of depth D from
 *   each of the 2kb class representatives reaches everything.
 * Phase 2 (grow by pairs): add g pairs of new vertices, wire them with degree-preserving edge
 *   steals, then anneal degree-preserving swaps until the diameter holds.
 *   Plateau walk: after repeated failures, perturb a copy of the best graph and repair it.
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
#define MAXK 4
#define MAXDART (MAXD * MAXK)
#define BIGCOST 1000000000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef int Mat[MAXK][MAXK];

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
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

/* ------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------ groups
 * G = (A x| Q) x C.
 * Element index: idx = (v*GQ + j)*GR + a, with v in A, j in Q, a in C. Identity = 0.
 * Multiplication: (v,j,a)(w,i,b) = (v + M^j w, j+i, a+b).
 * Type 0: A = Z_GP0 (cyclic), Q = Z_GQ, M = multiplication by r^j; GR = 1.
 * Type 1: A = F_p^k (GP0 = p^k, digitwise addition), Q = Z_GQ with matrix M, M^GQ = I; C = Z_GR.
 * AV[j*GP0 + w] stores M^j applied to w, so gmul needs one table lookup.
 */
static int GT, GP0, GQ, GR, GORD, GPRIME, GK;
static Mat GMAT;
static int AV[MAXN];

static int addN(int v, int w) {
    if (GT == 0) {
        int s = v + w;
        return s >= GP0 ? s - GP0 : s;
    }
    int r = 0, mul = 1;
    for (int i = 0; i < GK; i++) {
        int s = (v % GPRIME + w % GPRIME) % GPRIME;
        r += s * mul;
        mul *= GPRIME;
        v /= GPRIME;
        w /= GPRIME;
    }
    return r;
}

static int gmul(int x, int y) {
    int a1 = x % GR, t1 = x / GR, j1 = t1 % GQ, v1 = t1 / GQ;
    int a2 = y % GR, t2 = y / GR, j2 = t2 % GQ, v2 = t2 / GQ;
    int w = AV[j1 * GP0 + v2];
    int v = addN(v1, w);
    int j = (j1 + j2) % GQ;
    int a = (a1 + a2) % GR;
    return (v * GQ + j) * GR + a;
}

static void mat_mul(const Mat A, const Mat B, Mat C, int k, int p) {
    Mat T;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) {
            int s = 0;
            for (int l = 0; l < k; l++) s += A[i][l] * B[l][j];
            T[i][j] = s % p;
        }
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) C[i][j] = T[i][j];
}

static void mat_identity(Mat R, int k) {
    for (int i = 0; i < MAXK; i++)
        for (int j = 0; j < MAXK; j++) R[i][j] = (i == j);
    (void)k;
}

static void mat_pow(const Mat M, long e, Mat R, int k, int p) {
    Mat B;
    for (int i = 0; i < MAXK; i++)
        for (int j = 0; j < MAXK; j++) B[i][j] = M[i][j];
    mat_identity(R, k);
    while (e > 0) {
        if (e & 1) mat_mul(R, B, R, k, p);
        mat_mul(B, B, B, k, p);
        e >>= 1;
    }
}

static int is_identity_mat(const Mat M, int k) {
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            if (M[i][j] != (i == j)) return 0;
    return 1;
}

/* Fill AV from the current group description. */
static void build_action(void) {
    if (GT == 0) {
        int m = GP0;
        int pw = 1 % m;
        for (int b = 0; b < GQ; b++) {
            for (int w = 0; w < m; w++) AV[b * m + w] = (int)((long)pw * w % m);
            pw = (int)((long)pw * GMAT[0][0] % m);
        }
    } else {
        int k = GK, p = GPRIME, pk = GP0;
        Mat Mp;
        mat_identity(Mp, k);
        for (int j = 0; j < GQ; j++) {
            for (int w = 0; w < pk; w++) {
                int dig[MAXK];
                int x = w;
                for (int i = 0; i < k; i++) { dig[i] = x % p; x /= p; }
                int res = 0, mul = 1;
                for (int i = 0; i < k; i++) {
                    int s = 0;
                    for (int l = 0; l < k; l++) s += Mp[i][l] * dig[l];
                    res += (s % p) * mul;
                    mul *= p;
                }
                AV[j * pk + w] = res;
            }
            mat_mul(Mp, GMAT, Mp, k, p);
        }
    }
}

/* Type 0: random metacyclic semidirect product Z_m x| Z_k2 of order G (reservoir sampling). */
static int sample_cyclic(int G) {
    int cnt = 0, bm = 0, bk2 = 0, br = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        if (m == 1) {
            if (rndint(++cnt) == 0) { bm = 1; bk2 = k2; br = 0; }
            continue;
        }
        if (k2 == 1) {
            if (rndint(++cnt) == 0) { bm = m; bk2 = 1; br = 1; }
            continue;
        }
        for (int t = 0; t < 120; t++) {
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
            if (rndint(++cnt) == 0) { bm = m; bk2 = k2; br = r; }
        }
    }
    if (cnt == 0) return 0;
    GT = 0;
    GP0 = bm;
    GQ = bk2;
    GR = 1;
    GORD = G;
    GK = 0;
    GPRIME = 2;
    for (int i = 0; i < MAXK; i++)
        for (int j = 0; j < MAXK; j++) GMAT[i][j] = 0;
    GMAT[0][0] = br;
    build_action();
    return 1;
}

/* Type 1: (F_p^k x| Z_Q) x Z_c of order G with a random matrix M, M^Q = I. */
static int sample_nonmetacyclic(int G) {
    int fs[64], ps[64], ks[64], nf = 0;
    for (int f = 1; f <= G; f++) {
        if (G % f) continue;
        int p = 2, k = 0;
        if (f > 1) {
            int x = f;
            p = 0;
            for (int q = 2; q <= x; q++)
                if (x % q == 0) { p = q; break; }
            while (x % p == 0) { x /= p; k++; }
            if (x != 1 || k > MAXK) continue;
        }
        if (nf < 64) { fs[nf] = f; ps[nf] = p; ks[nf] = k; nf++; }
    }
    if (nf == 0) return 0;
    int idx = rndint(nf);
    int f = fs[idx], p = ps[idx], k = ks[idx];
    int rest = G / f;
    int divs[256], nd = 0;
    for (int c = 1; c <= rest && nd < 256; c++)
        if (rest % c == 0) divs[nd++] = c;
    int c = divs[rndint(nd)];
    int Q = rest / c;

    Mat M;
    mat_identity(M, k);
    if (k >= 1) {
        int ok = 0;
        for (int t = 0; t < 40 && !ok; t++) {
            Mat R;
            for (int i = 0; i < MAXK; i++)
                for (int j = 0; j < MAXK; j++)
                    M[i][j] = (i < k && j < k) ? rndint(p) : (i == j);
            mat_pow(M, Q, R, k, p);
            if (is_identity_mat(R, k)) ok = 1;
        }
        if (!ok) mat_identity(M, k);
    }
    GT = 1;
    GPRIME = p;
    GK = k;
    GP0 = f;
    GQ = Q;
    GR = c;
    GORD = G;
    for (int i = 0; i < MAXK; i++)
        for (int j = 0; j < MAXK; j++) GMAT[i][j] = M[i][j];
    build_action();
    return 1;
}

static int sample_group(int G) {
    if (rnd01() < 0.3) return sample_cyclic(G);
    if (sample_nonmetacyclic(G)) return 1;
    return sample_cyclic(G);
}

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND;                 /* base vertices per side, number of darts */
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXN];   /* DPERM[t][g] = g * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GORD; g++) DPERM[t][g] = gmul(g, DS[t]);
}

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GORD;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GORD; g++) {
            int a = DI[t] * GORD + g;
            int b = (KB + DJ[t]) * GORD + DPERM[t][g];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GORD;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GORD;   /* identity element of the group has index 0 */
        VST++;
        int head = 0, tail = 0;
        VIS[src] = VST;
        QU[tail++] = src;
        for (int depth = 0; depth < D; depth++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = QU[head++];
                for (int i = 0; i < LDEG[u]; i++) {
                    int v = LADJ[u][i];
                    if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void build_full(Graph *g) {
    int N = 2 * KB * GORD;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GORD; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GORD; x++)
            add_edge(g, DI[t] * GORD + x, (KB + DJ[t]) * GORD + DPERM[t][x]);
}

/* One annealing run over voltages and layer swaps for a random group of order G.
 * On success, out holds the full lift. */
static int lift_climb(int kb, int G, long steps, Graph *out) {
    if (!sample_group(G)) return 0;
    KB = kb;
    ND = d * kb;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < kb; i++) {
            int t = l * kb + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(GORD);
            set_dart_perm(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(GORD);
            if (nv == old) continue;
            DS[t] = nv;
            set_dart_perm(t);
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { DS[t] = old; set_dart_perm(t); }
        } else {
            if (kb < 2) continue;
            int l = rndint(d);
            int i1 = rndint(kb), i2 = rndint(kb);
            if (i1 == i2) continue;
            int t1 = l * kb + i1, t2 = l * kb + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    if (cost != 0) return 0;
    build_full(out);
    return 1;
}

static Graph LCAND;

/* Group-order escalation: after many failed attempts, the target group order rises,
 * one step per block of 40 failures, capped at 6. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
        long esc = fails > 40 ? (fails - 40) / 40 + 1 : 0;
        if (esc > 6) esc = 6;
        long G = (best->n + 2 + 2L * kb - 1) / (2L * kb) + rndint(4) + esc;
        if (G < 1) G = 1;
        if (2L * kb * G > moore || 2L * kb * G > MAXN) { fails++; continue; }
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(kb, (int)G, steps, &LCAND) &&
            LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
    }
}

/* ------------------------------------------------------------ repair annealing */

/* Degree-preserving edge-swap annealing on the number of unreached pairs.
 * Returns 1 if the graph becomes a valid diameter-D graph before 'until'. */
static int anneal_repair(Graph *w, double until) {
    long bad = bad_pairs(w);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(w->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(w->n);
        if (w->deg[v] == 0) continue;
        int u = w->adj[v][rndint(w->deg[v])];
        int s = rndint(w->n);
        if (w->side[s] != w->side[v] || s == v || w->deg[s] == 0) continue;
        int t = w->adj[s][rndint(w->deg[s])];
        if (t == u || has_edge(w, v, t) || has_edge(w, s, u)) continue;
        del_edge(w, v, u);
        del_edge(w, s, t);
        add_edge(w, v, t);
        add_edge(w, s, u);
        long nb = bad_pairs(w);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(w, v, t);
            del_edge(w, s, u);
            add_edge(w, v, u);
            add_edge(w, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(w);
}

/* ------------------------------------------------------------ plateau walk */

/* Diversification at fixed order: copy best, apply 'swaps' random degree-preserving
 * edge swaps, then repair the diameter by annealing. */
static int plateau_walk(const Graph *best, Graph *work, double until, int swaps) {
    copy_graph(work, best);
    int done = 0;
    for (long tries = 0; done < swaps && tries < (long)swaps * 60; tries++) {
        int v = rndint(work->n);
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
        done++;
    }
    return anneal_repair(work, until);
}

/* ------------------------------------------------------------ grow by pairs */

/* Adds g pairs of new vertices (x side 0, y side 1, joined to each other), so the order
 * rises by 2g. Each pair steals d-1 old edges. Then annealing repairs the diameter. */
static int grow_once(const Graph *best, Graph *work, double until, int g) {
    int n = best->n;
    if (g < 1) return 0;
    if (n + 2 * g > moore_bound() || n + 2 * g > MAXN) return 0;
    copy_graph(work, best);
    work->n = n + 2 * g;
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    for (int p = 0; p < g; p++) {
        int x = n + 2 * p, y = x + 1;
        work->deg[x] = work->deg[y] = 0;
        work->side[x] = 0;
        work->side[y] = 1;
        add_edge(work, x, y);
        used[x] = used[y] = stamp;
    }
    for (int p = 0; p < g; p++) {
        int x = n + 2 * p, y = x + 1;
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
    }
    return anneal_repair(work, until);
}

static void grow_search(Graph *best, double until) {
    static Graph work, plat;
    int fails = 0;
    while (now() < until) {
        long lim = moore_bound();
        if (lim > MAXN) lim = MAXN;
        int g = (fails % 3 == 2) ? 2 : 1;
        if (best->n + 2 * g > lim) g = 1;
        if (best->n + 2 * g > lim) break;
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice, g)) {
            copy_graph(best, &work);
            fails = 0;
        } else {
            fails++;
            if (fails % 12 == 0 && now() < until) {
                double pu = now() + 3.0;
                if (pu > until) pu = until;
                if (plateau_walk(best, &plat, pu, 20 + rndint(40)) && plat.n == best->n)
                    copy_graph(best, &plat);
            }
        }
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.85);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
