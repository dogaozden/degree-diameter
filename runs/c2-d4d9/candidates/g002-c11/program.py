"""Combined bipartite degree-diameter search.

Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) and
checks it with lib.is_valid. The C engine then runs three phases in order:

1. Haar-Cayley search: a Haar graph on a group G of order N (matrix groups PSL/PGL/SL(2,q), or
   semidirect products Z_m x| Z_k) with d generators, annealed to diameter <= D. Each success
   gives 2N vertices and climbs through group orders.
2. Lift search: a random d-regular base multigraph on p+p vertices (p <= 4) with voltages in a
   semidirect group, annealed against the orbit-reduced diameter defect. The target size adapts.
3. Grow by two: insert one vertex per side and repair with degree-preserving swaps.

Each phase starts from the best graph so far. Any result is kept only if it is valid and larger.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Combined bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXP 4

#define HNMAX 4200
#define HNVMAX (2 * HNMAX)
#define HNCAP 4000
#define SA_STEPS 8000
#define CODEMAX 130400

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

/* ================================================================
 * Finite fields and matrix groups PSL/PGL/SL(2,q) (for Haar phase)
 * ================================================================ */
typedef struct {
    int q;
    int add[32][32], mul[32][32], neg[32], inv[32];
} Field;
static Field F;

static int gf2mul(int a, int b, int k, int poly) {
    int r = 0;
    for (int i = 0; i < k; i++)
        if ((b >> i) & 1) r ^= a << i;
    for (int i = 2 * k - 2; i >= k; i--)
        if ((r >> i) & 1) r ^= poly << (i - k);
    return r;
}

static void field_init(int q) {
    memset(&F, 0, sizeof F);
    F.q = q;
    if (q == 8 || q == 16) {
        int k = (q == 8) ? 3 : 4;
        int poly = (q == 8) ? 0xB : 0x13;
        for (int i = 0; i < q; i++)
            for (int j = 0; j < q; j++) {
                F.add[i][j] = i ^ j;
                F.mul[i][j] = gf2mul(i, j, k, poly);
            }
        for (int i = 0; i < q; i++) F.neg[i] = i;
    } else {
        for (int i = 0; i < q; i++)
            for (int j = 0; j < q; j++) {
                F.add[i][j] = (i + j) % q;
                F.mul[i][j] = (i * j) % q;
            }
        for (int i = 0; i < q; i++) F.neg[i] = (q - i) % q;
    }
    for (int i = 1; i < q; i++)
        for (int j = 1; j < q; j++)
            if (F.mul[i][j] == 1) F.inv[i] = j;
}

static int MQ, MODE;
static int CODE2IDX[CODEMAX];
static int MAT[HNMAX][4];

/* Canonical code of a matrix: MODE 0 = PSL (M ~ -M), MODE 1 = SL, MODE 2 = PGL (M ~ c*M). */
static int enc(int a, int b, int c, int e) { return ((a * MQ + b) * MQ + c) * MQ + e; }

static int norm_code(int a, int b, int c, int e) {
    if (MODE == 2) {
        int f = a ? a : (b ? b : (c ? c : e));
        int iv = F.inv[f];
        a = F.mul[a][iv];
        b = F.mul[b][iv];
        c = F.mul[c][iv];
        e = F.mul[e][iv];
        return enc(a, b, c, e);
    }
    int c1 = enc(a, b, c, e);
    if (MODE == 0) {
        int c2 = enc(F.neg[a], F.neg[b], F.neg[c], F.neg[e]);
        if (c2 < c1) c1 = c2;
    }
    return c1;
}

static int matrix_group_build(int q, int mode) {
    MQ = q;
    MODE = mode;
    field_init(q);
    int Q4 = q * q * q * q;
    for (int i = 0; i < Q4; i++) CODE2IDX[i] = -1;
    int N = 0;
    for (int code = 0; code < Q4; code++) {
        int m3 = code % q;
        int m2 = (code / q) % q;
        int m1 = (code / (q * q)) % q;
        int m0 = code / (q * q * q);
        int det = F.add[F.mul[m0][m3]][F.neg[F.mul[m1][m2]]];
        if (mode == 2) {
            if (det == 0) continue;
        } else if (det != 1) {
            continue;
        }
        if (norm_code(m0, m1, m2, m3) != code) continue;
        if (N >= HNMAX) return 0;
        CODE2IDX[code] = N;
        MAT[N][0] = m0;
        MAT[N][1] = m1;
        MAT[N][2] = m2;
        MAT[N][3] = m3;
        N++;
    }
    return N;
}

static int mat_mul(int x, int y) {
    const int *X = MAT[x], *Y = MAT[y];
    int a = F.add[F.mul[X[0]][Y[0]]][F.mul[X[1]][Y[2]]];
    int b = F.add[F.mul[X[0]][Y[1]]][F.mul[X[1]][Y[3]]];
    int c = F.add[F.mul[X[2]][Y[0]]][F.mul[X[3]][Y[2]]];
    int e = F.add[F.mul[X[2]][Y[1]]][F.mul[X[3]][Y[3]]];
    return CODE2IDX[norm_code(a, b, c, e)];
}

static int mat_inv(int x) {
    const int *X = MAT[x];
    return CODE2IDX[norm_code(X[3], F.neg[X[1]], F.neg[X[2]], X[0])];
}

/* ================================================================
 * Haar-Cayley search: groups G with d generators, graph H(G,S)
 * ================================================================ */
static int GKIND = 0;          /* 0 = semidirect, 1 = matrix group */
static int GN, GE;
static int SM, SK;
static int RP[HNMAX], RPI[HNMAX];
static int S[MAXD];
static int NB_A[MAXD][HNMAX], NB_B[MAXD][HNMAX];
static int BK_A[HNMAX], BK_B[HNMAX];
static int HDIST[HNVMAX], HQUE[HNVMAX];
static int bestHalf = 0, bestM = 0;
static int BU[MAXD * HNMAX], BV[MAXD * HNMAX];

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int semidirect_setup(int N) {
    int divs[256], nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0 && nd < 256) divs[nd++] = m;
    for (int tr = 0; tr < 200; tr++) {
        int m = divs[rndint(nd)];
        int k = N / m;
        int r;
        if (m == 1) {
            r = 0;
        } else if (rnd01() < 0.1) {
            r = 1;
        } else {
            r = 1 + rndint(m - 1);
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
        }
        SM = m;
        SK = k;
        RP[0] = 1 % m;
        for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
        int rinv = 0;
        if (m > 1)
            for (int t = 1; t < m; t++)
                if ((long)r * t % m == 1) { rinv = t; break; }
        RPI[0] = 1 % m;
        for (int b = 1; b < k; b++) RPI[b] = (int)((long)RPI[b - 1] * rinv % m);
        GKIND = 0;
        GN = N;
        GE = 0;
        return 1;
    }
    return 0;
}

static int hgmul(int x, int y) {
    if (GKIND == 1) return mat_mul(x, y);
    int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
    int a2 = (int)(((long)a + (long)RP[b] * c) % SM);
    int b2 = (b + e) % SK;
    return a2 * SK + b2;
}

static int hginv(int x) {
    if (GKIND == 1) return mat_inv(x);
    int a = x / SK, b = x % SK;
    int c = (int)(((long)(SM - a) % SM) * RPI[b] % SM);
    int e = (SK - b) % SK;
    return c * SK + e;
}

/* Vertex A_x = x, B_y = GN + y. Edge A_x - B_{x s_i}. */
static void fill_perm(int i) {
    int s = S[i];
    int si = hginv(s);
    for (int x = 0; x < GN; x++) {
        NB_A[i][x] = hgmul(x, s);
        NB_B[i][x] = hgmul(x, si);
    }
}

static int in_prefix(int v, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == v) return 1;
    return 0;
}

static int in_all(int v) { return in_prefix(v, d); }

static void random_S(void) {
    for (int i = 0; i < d; i++) {
        int v;
        do v = rndint(GN); while (in_prefix(v, i));
        S[i] = v;
        fill_perm(i);
    }
}

/* BFS from src up to depth D; returns how many vertices lie within distance D. */
static int reach_within(int src) {
    int V = 2 * GN;
    for (int v = 0; v < V; v++) HDIST[v] = -1;
    int head = 0, tail = 0;
    HDIST[src] = 0;
    HQUE[tail++] = src;
    while (head < tail) {
        int v = HQUE[head++];
        if (HDIST[v] >= D) continue;
        int nd1 = HDIST[v] + 1;
        if (v < GN) {
            for (int i = 0; i < d; i++) {
                int u = GN + NB_A[i][v];
                if (HDIST[u] < 0) { HDIST[u] = nd1; HQUE[tail++] = u; }
            }
        } else {
            int y = v - GN;
            for (int i = 0; i < d; i++) {
                int u = NB_B[i][y];
                if (HDIST[u] < 0) { HDIST[u] = nd1; HQUE[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Zero iff the Haar graph has diameter <= D (G is transitive on each part). */
static int score(void) {
    int V = 2 * GN;
    return (V - reach_within(GE)) + (V - reach_within(GN + GE));
}

static void save_best(void) {
    bestHalf = GN;
    bestM = 0;
    for (int i = 0; i < d; i++)
        for (int x = 0; x < GN; x++) {
            BU[bestM] = x;
            BV[bestM] = GN + NB_A[i][x];
            bestM++;
        }
}

static int attempt(double until) {
    int N = GN;
    while (now() < until) {
        random_S();
        int f = score();
        double T0 = 0.3 + 2.0 * rnd01();
        for (int st = 0; st < SA_STEPS && f > 0; st++) {
            if ((st & 127) == 0 && now() > until) return 0;
            double T = T0 * (1.0 - (double)st / SA_STEPS) + 0.05;
            int i = rndint(d);
            int old = S[i], nw;
            do nw = rndint(N); while (in_all(nw));
            memcpy(BK_A, NB_A[i], sizeof(int) * N);
            memcpy(BK_B, NB_B[i], sizeof(int) * N);
            S[i] = nw;
            fill_perm(i);
            int f2 = score();
            int df = f2 - f;
            if (df <= 0 || rnd01() < exp(-(double)df / T)) {
                f = f2;
            } else {
                S[i] = old;
                memcpy(NB_A[i], BK_A, sizeof(int) * N);
                memcpy(NB_B[i], BK_B, sizeof(int) * N);
            }
        }
        if (f == 0) {
            save_best();
            return 1;
        }
    }
    return 0;
}

static const int MQS[12] = {5, 5, 7, 7, 8, 11, 11, 13, 13, 16, 17, 19};
static const int MMODE[12] = {0, 2, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0};
static const int MORD[12] = {60, 120, 168, 336, 504, 660, 1320, 1092, 2184, 4080, 2448, 3420};

static void haar_search(double until) {
    while (1) {
        double remaining = until - now();
        if (remaining < 0.3) break;
        int lo = bestHalf + 1;
        if (lo < d + 1) lo = d + 1;
        if (lo > HNCAP) break;
        int span = bestHalf / 6 + 20;
        int ok = 0;
        if (rnd01() < 0.4) {
            int cand[12], nc = 0;
            for (int c = 0; c < 12; c++)
                if (MORD[c] >= lo && MORD[c] <= lo + 2 * span + 100 && MORD[c] <= HNCAP)
                    cand[nc++] = c;
            if (nc > 0) {
                int c = cand[rndint(nc)];
                int n2 = matrix_group_build(MQS[c], MMODE[c]);
                if (n2 > 0) {
                    GKIND = 1;
                    GN = n2;
                    GE = CODE2IDX[norm_code(1, 0, 0, 1)];
                    ok = 1;
                }
            }
        }
        if (!ok) {
            int N = lo + rndint(span);
            if (N > HNCAP) N = HNCAP;
            if (!semidirect_setup(N)) continue;
        }
        if (GN < d + 1) continue;
        double slice = remaining * 0.08;
        if (slice < 1.0) slice = 1.0;
        if (slice > remaining) slice = remaining;
        attempt(now() + slice);
    }
}

static void build_haar_graph(Graph *g) {
    g->n = 2 * bestHalf;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= bestHalf; }
    for (int k = 0; k < bestM; k++) add_edge(g, BU[k], BV[k]);
}

/* ================================================================
 * Lift search: semidirect-group voltage lifts of small base multigraphs
 * ================================================================ */
/* Z_m x|_r Z_k as a Grp for the lift phase. */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

typedef struct { int i, j, g; } Dart;

static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = rndint(i + 1); int s = perm[i]; perm[i] = perm[j]; perm[j] = s; }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Orbit-reduced defect: BFS only from the 2p fibre representatives. */
static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

static long lift_anneal(Graph *g, int p, int N, const Grp *G, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = orbit_bad(g, p, N);
    double T = 0.8;
    for (long s = 0; bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dt[t].g = old;
        T *= 0.99995;
        if (T < 0.05) T = 0.8;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    long gap = best->n / 10 + 4;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int p = r < 5 ? 1 : r < 8 ? 2 : r < 9 ? 3 : 4;
        long goal = best->n + gap;
        if (goal > moore) goal = moore;
        int N = (int)((goal + 2 * p - 1) / (2 * p));
        if (N < d) N = d;
        if (2L * p * N > MAXN || 2L * p * N > moore) continue;
        if (!random_group(N, &G)) continue;
        double slice = now() + 2.5;
        if (slice > until) slice = until;
        long bad = lift_anneal(&cand, p, N, &G, slice);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            gap = gap * 11 / 10 + 2;
        } else {
            gap = gap * 97 / 100;
            if (gap < 2) gap = 2;
        }
    }
}

/* ================================================================
 * Grow by two: add one vertex per side and repair with swaps
 * ================================================================ */
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
    while (bad > 0) {
        if (now() > until) return 0;
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

/* ================================================================
 * main
 * ================================================================ */
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2) {
        double span = t_end - t0;
        /* Phase 1: Haar-Cayley search. */
        haar_search(t0 + span * 0.40);
        if (bestHalf > 0 && 2 * bestHalf > best.n) {
            static Graph hg;
            build_haar_graph(&hg);
            if (is_valid(&hg)) copy_graph(&best, &hg);
        }
        /* Phase 2: lift search from the current best. */
        if (best.n < moore_bound())
            lift_search(&best, t0 + span * 0.80);
        /* Phase 3: grow by two. */
        if (best.n > 0 && best.n + 2 <= moore_bound())
            grow_search(&best, t_end);
    }

    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);
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

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
