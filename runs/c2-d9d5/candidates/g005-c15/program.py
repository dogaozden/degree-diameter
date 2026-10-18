"""Combined bipartite degree-diameter search.

Python builds exact or known starting graphs (projective planes, Araujo-Lopez,
W(q) for D=4) and falls back to K_{d,d}. The C engine runs three phases:

1. Affine Haar lifts: Haar graphs of G = F_q x| H, where H is the subgroup of
   F_q^* of order c. Candidate orders are tried in ascending order above the
   current best (and above mb/8 in group order), with simulated annealing over
   the d-element connection set. Left translations are automorphisms, so the
   diameter check needs only two BFS runs.
2. Bi-Cayley voltage lifts over Z_m x| Z_k with simulated annealing, started
   from the best graph so far.
3. Grow-by-two and ruin-and-recreate, alternating, with degree-preserving swap
   repair. Every move keeps the graph valid.

Every returned graph is checked with lib.is_valid, and the Python fallback is
always valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Combined bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit [lo hi]   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * lo, hi:  range of affine-group orders (group order N, graph order 2N).
 * stdout:  "n m" then m lines "u v": the best valid graph found.
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
#define MAXM 64
#define PENALTY 1000L
#define MAXQ 256
#define MAXC 256
#define MAXCAND 8192
#define MAXGN (MAXN / 2)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best;
static Graph haar_out;

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= d); }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ affine Haar lifts */

/* G = F_q x| H, |H| = c, c | q-1. Element (a, h_j) coded as a*c + j. */
static int AF_ADD[MAXQ][MAXQ], AF_MUL[MAXQ][MAXQ], AF_NEG[MAXQ];
static int af_built_q = -1;

static int af_factor(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

/* Multiply two field elements (base-p digit vectors) modulo the monic f with lower digits m. */
static int af_polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void af_build_field(int q, int p, int k) {
    if (af_built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            AF_ADD[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (AF_ADD[a][b] == 0) AF_NEG[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (af_polymul(a, b, p, k, pw, m) == 0) ok = 0;   /* zero divisor: reducible */
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    AF_MUL[a][b] = af_polymul(a, b, p, k, pw, m);
        }
    }
    af_built_q = q;
}

static int AF_Q, AF_C, AF_N;
static int af_Hel[MAXC], af_hidx[MAXQ], af_HM[MAXC * MAXC], af_PWG[MAXQ];

static void af_setup(int q, int p, int k, int c) {
    af_build_field(q, p, k);
    AF_Q = q;
    AF_C = c;
    AF_N = q * c;
    int g = 1;
    for (int g0 = 2; g0 < q; g0++) {
        int x = 1, ord = 0;
        do { x = AF_MUL[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) { g = g0; break; }
    }
    af_PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) af_PWG[i] = AF_MUL[af_PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) af_hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        af_Hel[t] = af_PWG[(t * step) % (q - 1)];
        af_hidx[af_Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            af_HM[j * c + t] = af_hidx[AF_MUL[af_Hel[j]][af_Hel[t]]];
}

static int af_mul(int x, int y) {
    int c = AF_C;
    int a = x / c, j = x % c, b = y / c, t = y % c;
    int na = AF_ADD[a][AF_MUL[af_Hel[j]][b]];
    return na * c + af_HM[j * c + t];
}

static int af_inv(int x) {
    int c = AF_C;
    int a = x / c, j = x % c;
    int jn = (c - j) % c;
    int na = AF_NEG[AF_MUL[af_Hel[jn]][a]];
    return na * c + jn;
}

/* Haar graph: L_g ~ R_{g s}. Vertices L_g = g, R_h = N + h. */
static int af_S[MAXD], af_Sinv[MAXD], af_bestS[MAXD];
static int af_fwd[MAXD][MAXGN], af_bwd[MAXD][MAXGN];
static int af_vis[2 * MAXN], af_que[2 * MAXN];
static int af_stamp = 0;

static void af_set_s(int i, int x) {
    af_S[i] = x;
    af_Sinv[i] = af_inv(x);
    for (int g = 0; g < AF_N; g++) {
        af_fwd[i][g] = af_mul(g, x);
        af_bwd[i][g] = af_mul(g, af_Sinv[i]);
    }
}

/* Number of vertices within distance D of src. */
static int af_bfs(int src) {
    int N = AF_N;
    af_stamp++;
    int head = 0, tail = 0;
    af_que[tail++] = src;
    af_vis[src] = af_stamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = af_que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + af_fwd[i][v];
                    if (af_vis[u] != af_stamp) { af_vis[u] = af_stamp; af_que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = af_bwd[i][h];
                    if (af_vis[u] != af_stamp) { af_vis[u] = af_stamp; af_que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertex transitivity on each side: two BFS runs (from L_e and R_e) decide the diameter. */
static long af_cost(void) {
    int V = 2 * AF_N;
    return (long)(V - af_bfs(0)) + (long)(V - af_bfs(AF_N));
}

static int af_in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (af_S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over the connection set in the current group.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int af_search(double until) {
    int N = AF_N;
    const int iters = 8000;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (af_in_S(x, i));
            af_set_s(i, x);
        }
        long cost = af_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double Tm = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (af_in_S(x, d));
            int old = af_S[i];
            af_set_s(i, x);
            long c2 = af_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tm)) {
                cost = c2;
            } else {
                af_set_s(i, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void af_to_graph(Graph *g) {
    int N = AF_N;
    g->n = 2 * N;
    for (int v = 0; v < 2 * N; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= N);
    }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, N + af_fwd[i][x]);
}

typedef struct { int q, p, k, c, N; } AfCand;

/* Try affine groups with group order in [lo, hi] in ascending order, skipping
 * orders whose graph would not beat min_total. Writes the found graph to out. */
static int af_phase(double until, int lo, int hi, long min_total, Graph *out) {
    static AfCand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!af_factor(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                AfCand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        AfCand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    int found = 0;
    AfCand bestc = {0, 0, 0, 0, 0};
    for (int ci = 0; ci < nc; ci++) {
        double rem = until - now();
        if (rem < 0.3) break;
        if (2L * cand[ci].N <= min_total) continue;
        double slice = 0.15 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        af_setup(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        if (af_search(now() + slice)) {
            found = 1;
            bestc = cand[ci];
            min_total = 2L * cand[ci].N;
            memcpy(af_bestS, af_S, sizeof(int) * (size_t)d);
        }
    }
    if (!found) return 0;
    af_setup(bestc.q, bestc.p, bestc.k, bestc.c);
    for (int i = 0; i < d; i++) af_set_s(i, af_bestS[i]);
    af_to_graph(out);
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley state */

/* Group Z_m x|_r Z_k, element (a, b) coded as a*k + b. */
static int GM, GK, GRR;
static int GG;
static int rpw[MAXM];
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

static int sample_group(int target) {
    static const int ks[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    int k = ks[rndint(20)];
    int m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k == 1) {
        r = 1;
    } else if (k == 2 && rnd01() < 0.3) {
        r = (m > 2) ? m - 1 : 1;
    } else if (m > 2) {
        for (int t = 0; t < 60; t++) {
            int c = 2 + rndint(m - 2);
            if (gcd_i(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = c; break; }
        }
    }
    set_group(m, k, r);
    return 1;
}

static int KB;
static int layers[MAXD][MAXK];
static int Sv[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static unsigned char TA[MAXN], TB[MAXN], RCUR[MAXN], ACC[MAXN];
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
static void compute_reach(unsigned char *out) {
    int N = 2 * KB * GG;
    unsigned char *cur = TA, *nxt = TB;
    memset(cur, 0, (size_t)N);
    for (int b = 0; b < 2 * KB; b++) cur[b * GG] = (unsigned char)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            unsigned char x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        unsigned char *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    memcpy(out, cur, (size_t)N);
}

static long unreached(const unsigned char *r, int N) {
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

static int anneal(int iters, int patience, double deadline) {
    int N = 2 * KB * GG;
    unsigned char full = (unsigned char)((1u << (2 * KB)) - 1);
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
    compute_reach(RCUR);
    long cost = unreached(RCUR, N) + PENALTY * dupcount();
    memcpy(ACC, RCUR, (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if (now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (KB >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(KB), i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            int t1 = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = t1;
            set_dart(l, i1, layers[l][i1], Sv[l][i1]);
            set_dart(l, i2, layers[l][i2], Sv[l][i2]);
            compute_reach(RCUR);
            long c2 = unreached(RCUR, N) + PENALTY * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(ACC, RCUR, (size_t)N);
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
        compute_reach(RCUR);
        long c2 = unreached(RCUR, N) + PENALTY * dupcount();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(ACC, RCUR, (size_t)N);
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
        if (anneal(4000, 1200, until)) {
            wins[k]++;
            build_bicayley(&cand);
            if (cand.n > b->n && is_valid(&cand)) copy_graph(b, &cand);
        }
    }
}

/* ------------------------------------------------------------ repair by swaps */

static int used[MAXN];
static int stamp = 0;

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
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

/* ------------------------------------------------------------ grow by two */

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

static void grow_or_ils(Graph *bst, double until) {
    static Graph wk;
    long turn = 0;
    while (now() < until) {
        double slice = until - now();
        if (slice > 3.0) slice = 3.0;
        if (turn % 3 != 2 && bst->n + 2 <= moore_bound()) {
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
        fprintf(stderr, "usage: %s d D seed time_limit [lo hi] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = argc > 5 ? atoi(argv[5]) : 0;
    int hi = argc > 6 ? atoi(argv[6]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (D < 2) { printf("2 1\n0 1\n"); return 0; }

    read_start(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double T = t_end - t0;
    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXGN) hi = MAXGN;
    if (hi > 0 && lo <= hi && best.n < moore_bound()) {
        if (af_phase(t0 + 0.4 * T, lo, hi, best.n, &haar_out) &&
            haar_out.n > best.n && is_valid(&haar_out))
            copy_graph(&best, &haar_out);
    }

    if (best.n < moore_bound()) {
        bicayley_search(&best, t0 + 0.6 * T);
        grow_or_ils(&best, t_end);
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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
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
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
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

    mb = lib.moore_bound(d, D)
    budget = 0.86 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 1.0 and best[0] < mb:
        # Affine Haar group orders: graph order is 2N, aim for N in the record range.
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = min(mb // 3, 2048)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                             stdin_graph=best, timeout=budget + 8.0)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
