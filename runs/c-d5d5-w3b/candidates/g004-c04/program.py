"""Two-stage program for the d=5, D=5 target.

Stage 1 is a new construction: a random search over bipartite Cayley graphs on
semidirect products Z_m x|_r Z_k (k even). The connection set is a union of
involutions and inverse pairs, all lying in the odd coset of the index-2 subgroup.
Vertex transitivity means the diameter check needs one BFS from the identity.
Stage 2 is the previous lift and grow-by-two engine, started from the best graph
from stage 1, so the result never drops below the earlier construction.
"""
import time

import lib

CAYLEY_SOURCE = r'''
/* Bipartite Cayley search over Z_m x|_r Z_k (k even).
 * Elements x = a*k + b. Product (a,b)(c,e) = (a + r^b c mod m, b+e mod k).
 * Connection set S is inverse-closed, consists of odd-b elements, and |S| = d.
 * The graph has the group as vertex set, with edges x -- x*s. Sides are b mod 2.
 * Diameter <= D is checked by one BFS from the identity (vertex transitivity).
 * Stdin is ignored. Stdout: best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define STEPS 2000

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 1234567ULL;
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

static long moore_c(void) {
    if (D <= 0 || d <= 0) return 1;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ group */

static int GN, GM, GK;
static int RP[MAXN], RIP[MAXN];

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GN = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    int rinv = 0;
    for (int t = 0; t < m; t++)
        if ((long)r * t % m == 1 % m) { rinv = t; break; }
    RIP[0] = 1 % m;
    for (int b = 1; b < k; b++) RIP[b] = (int)((long)RIP[b - 1] * rinv % m);
}

static int mulg(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int A = (int)(((long)a + (long)RP[b] * c) % GM);
    int B = (b + e) % GK;
    return A * GK + B;
}

static int invg(int x) {
    int a = x / GK, b = x % GK;
    int A = (int)(((long)(GM - a) % GM) * RIP[b] % GM);
    int B = (GK - b) % GK;
    return A * GK + B;
}

/* Uniformly random (m, k, r) with m*k = N, k even, gcd(r,m)=1, r^k = 1 mod m. */
static int pick_group(int N) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (k % 2) continue;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (cnt == 0) return 0;
    set_group(bm, bk, br);
    return 1;
}

/* Odd elements (b odd): involutions and non-involutions. */
static int INVL[MAXN], NINV;
static int PAIRL[MAXN], NPAIR;

static void classify(void) {
    NINV = NPAIR = 0;
    for (int x = 0; x < GN; x++) {
        if ((x % GK) % 2 == 0) continue;
        int y = invg(x);
        if (y == x) INVL[NINV++] = x;
        else PAIRL[NPAIR++] = x;
    }
}

/* ------------------------------------------------------------ connection set */

static int ue[MAXD], ut[MAXD], nu;   /* units: ut 0 = involution, 1 = inverse pair */
static int inS[MAXN];
static int gens[MAXD], ng;

static void build_gens(void) {
    ng = 0;
    for (int u = 0; u < nu; u++) {
        gens[ng++] = ue[u];
        if (ut[u] == 1) gens[ng++] = invg(ue[u]);
    }
}

static int orbit_free(int type, int x) {
    if (inS[x]) return 0;
    if (type == 1 && inS[invg(x)]) return 0;
    return 1;
}

static void orbit_mark(int type, int x, int v) {
    inS[x] = v;
    if (type == 1) inS[invg(x)] = v;
}

static int pick_elem(int type) {
    int *L = type == 0 ? INVL : PAIRL;
    int n = type == 0 ? NINV : NPAIR;
    if (n == 0) return -1;
    for (int t = 0; t < 300; t++) {
        int x = L[rndint(n)];
        if (orbit_free(type, x)) return x;
    }
    return -1;
}

static int choose_j(void) {
    int cand[MAXD + 1], nc = 0;
    for (int j = d % 2; j <= d; j += 2) {
        int p = (d - j) / 2;
        if (j > 0 && NINV == 0) continue;
        if (p > 0 && NPAIR == 0) continue;
        cand[nc++] = j;
    }
    if (nc == 0) return -1;
    return cand[rndint(nc)];
}

static int init_state(void) {
    int j = choose_j();
    if (j < 0) return 0;
    int p = (d - j) / 2;
    memset(inS, 0, sizeof(int) * (size_t)GN);
    nu = 0;
    for (int i = 0; i < j; i++) {
        int x = pick_elem(0);
        if (x < 0) return 0;
        ue[nu] = x; ut[nu] = 0; nu++;
        orbit_mark(0, x, 1);
    }
    for (int i = 0; i < p; i++) {
        int x = pick_elem(1);
        if (x < 0) return 0;
        ue[nu] = x; ut[nu] = 1; nu++;
        orbit_mark(1, x, 1);
    }
    return 1;
}

/* Unreached elements from the identity within D steps. 0 means diameter <= D. */
static int dist_[MAXN], qbuf[MAXN], stampv[MAXN];
static int curstamp = 0;

static int cost_of(void) {
    build_gens();
    curstamp++;
    int head = 0, tail = 0;
    qbuf[tail++] = 0;
    stampv[0] = curstamp;
    dist_[0] = 0;
    while (head < tail) {
        int x = qbuf[head++];
        if (dist_[x] >= D) continue;
        for (int i = 0; i < ng; i++) {
            int y = mulg(x, gens[i]);
            if (stampv[y] != curstamp) {
                stampv[y] = curstamp;
                dist_[y] = dist_[x] + 1;
                qbuf[tail++] = y;
            }
        }
    }
    return GN - tail;
}

static int climb(int steps) {
    int c = cost_of();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) break;
        int u = rndint(nu);
        int type = ut[u], old = ue[u];
        orbit_mark(type, old, 0);
        int x = pick_elem(type);
        if (x < 0) { orbit_mark(type, old, 1); continue; }
        ue[u] = x;
        orbit_mark(type, x, 1);
        int c2 = cost_of();
        if (c2 <= c || rnd01() < 0.02) {
            c = c2;
        } else {
            orbit_mark(type, x, 0);
            ue[u] = old;
            orbit_mark(type, old, 1);
        }
    }
    return c == 0;
}

/* ------------------------------------------------------------ graph and check */

static int badj[MAXN][MAXD];
static int dg[MAXN];
static int sadj[MAXN][MAXD];
static int sdg[MAXN];
static int sN = 0;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

static void build_graph(void) {
    build_gens();
    for (int x = 0; x < GN; x++) {
        dg[x] = ng;
        for (int i = 0; i < ng; i++) badj[x][i] = mulg(x, gens[i]);
    }
}

static long bad_pairs_c(int n) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *s = cur + (size_t)badj[v][i] * W;
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

static int full_valid(void) {
    int n = GN;
    for (int x = 0; x < n; x++) {
        if (dg[x] > d) return 0;
        int side = (x % GK) % 2;
        for (int i = 0; i < dg[x]; i++) {
            int y = badj[x][i];
            if (y < 0 || y >= n || y == x) return 0;
            if ((y % GK) % 2 == side) return 0;
            int found = 0;
            for (int j = 0; j < dg[y]; j++)
                if (badj[y][j] == x) found = 1;
            if (!found) return 0;
            for (int j = 0; j < i; j++)
                if (badj[x][j] == y) return 0;
        }
    }
    return bad_pairs_c(n) == 0;
}

static void save_best(int n) {
    sN = n;
    for (int x = 0; x < n; x++) {
        sdg[x] = dg[x];
        memcpy(sadj[x], badj[x], sizeof(int) * (size_t)dg[x]);
    }
}

static void print_best(void) {
    if (sN == 0) { printf("0 0\n"); return; }
    long m = 0;
    for (int x = 0; x < sN; x++)
        for (int i = 0; i < sdg[x]; i++)
            if (x < sadj[x][i]) m++;
    printf("%d %ld\n", sN, m);
    for (int x = 0; x < sN; x++)
        for (int i = 0; i < sdg[x]; i++)
            if (x < sadj[x][i]) printf("%d %d\n", x, sadj[x][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.96;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    long Nl = moore_c();
    if (Nl > MAXN) Nl = MAXN;
    int Nmax = (int)Nl;
    Nmax -= Nmax % 2;
    int bestN = 0;

    while (now() < t_end) {
        int span = (Nmax - bestN) / 2;
        if (span <= 0) break;
        int pick = (rnd01() < 0.5) ? 1 : 1 + rndint(span);
        int N = bestN + 2 * pick;
        if (N > Nmax) continue;
        if (!pick_group(N)) continue;
        classify();
        if (!init_state()) continue;
        if (climb(STEPS)) {
            build_graph();
            if (full_valid()) {
                bestN = N;
                save_best(N);
            }
        }
    }
    print_best();
    return 0;
}
'''

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): bi-Cayley lifts over groups Z_m x| Z_k2 with k vertices per side.
 *   A_{i,g} ~ B_{j,g*s} for each dart (i,j,s). Left multiplication is an automorphism,
 *   so diameter <= D is checked by BFS from the 2k representatives only.
 *   Hill-climb on voltages. Phase 1 stops early when it stalls.
 * Phase 2 (grow by two): add one vertex per side using stolen edges, then anneal
 *   degree-preserving swaps until the diameter bound holds.
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
#define MAXG 1024
#define MAXK 3

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static long moore;

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

static long compute_moore(void) {
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Bitset reachability, D rounds. */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element (a,b) = a*k2+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK, GR;
static int RP[MAXG];
static int MT[MAXG * MAXG];   /* MT[x*N+y] = x*y */

static void set_group(int N, int m, int k2, int r) {
    GM = m; GK = k2; GR = r;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < N; y++) {
            int c = y / k2, e = y % k2;
            MT[x * N + y] = (int)(((long)a + (long)RP[b] * c) % m) * k2 + (b + e) % k2;
        }
    }
}

/* Uniform random (m, k2, r) with m*k2 = N, gcd(r,m) = 1, r^k2 = 1 mod m. */
static void random_group(int N) {
    long cnt = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    set_group(N, bm, bk, br);
}

/* ------------------------------------------------------------------ lifts */

static int K_, N_;          /* k vertices per side, group order */
static int nd_;             /* number of darts = d * k */
static int dI[MAXD * MAXK], dJ[MAXD * MAXK], dS[MAXD * MAXK];

static int adjL[MAXN][MAXD];
static int degL[MAXN];
static int visL[MAXN];
static int qL[MAXN];
static int stampL = 0;

/* Cost = 1e6 * duplicate darts + total unreached (representative, vertex) pairs. */
static long lift_cost(void) {
    int k = K_, N = N_, n = 2 * k * N;
    long pen = 0;
    for (int t = 0; t < nd_; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < nd_; t++)
        for (int g = 0; g < N; g++) {
            int a = dI[t] * N + g;
            int b = (k + dJ[t]) * N + MT[g * N + dS[t]];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
    long unreached = 0;
    int reps[2 * MAXK], nr = 0;
    for (int i = 0; i < k; i++) reps[nr++] = i * N;
    for (int j = 0; j < k; j++) reps[nr++] = (k + j) * N;
    for (int r = 0; r < nr; r++) {
        stampL++;
        int head = 0, tail = 0;
        int src = reps[r];
        visL[src] = stampL;
        qL[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qL[head++];
                for (int i = 0; i < degL[u]; i++) {
                    int v = adjL[u][i];
                    if (visL[v] != stampL) { visL[v] = stampL; qL[tail++] = v; }
                }
            }
        }
        unreached += n - tail;
    }
    return pen * 1000000L + unreached;
}

static void build_lift(Graph *g) {
    int k = K_, N = N_;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, (k + dJ[t]) * N + MT[x * N + dS[t]]);
}

/* Hill-climb on the darts of a fresh random lift. Returns 1 if cost reaches 0. */
static int lift_attempt(int steps, double until) {
    int k = K_, N = N_;
    nd_ = d * k;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(N);
        }
    }
    long c = lift_cost();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        if (k > 1 && rnd01() < 0.15) {
            int l = rndint(d), a = rndint(k), b = rndint(k);
            if (a == b) continue;
            int t1 = l * k + a, t2 = l * k + b;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.01) c = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rndint(nd_);
            int old = dS[t];
            dS[t] = rndint(N);
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.01) c = c2;
            else dS[t] = old;
        }
    }
    return c == 0;
}

static Graph best;

/* Random lifts one group at a time. Stops at `until`, or early once no improvement
   has come for half of the window: then the time is better spent growing `best`. */
static void lift_phase(double until) {
    static Graph cand;
    static const int kc[6] = {1, 1, 1, 2, 2, 3};
    double start = now();
    double stall = 0.5 * (until - start);
    double last_gain = start;
    int fails = 0;
    while (now() < until && best.n < moore) {
        if (now() - last_gain > stall) return;
        int k = kc[rndint(6)];
        long target = best.n + 2;
        long Nl = (target + 2 * k - 1) / (2 * k) + rndint(3);
        if (Nl < 1 || Nl > MAXG || 2 * k * Nl > moore || 2 * k * Nl > MAXN) {
            if (++fails > 5000) return;
            continue;
        }
        int N = (int)Nl;
        K_ = k;
        N_ = N;
        random_group(N);
        /* Deep hill-climb per random group: most lifts stall well above cost 0,
           so a longer search per group finds valid voltages where restarts do not. */
        if (lift_attempt(25000, until)) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) {
                copy_graph(&best, &cand);
                last_gain = now();
            }
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *base, Graph *work, double until) {
    int n = base->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
    copy_graph(work, base);
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
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
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

/* Each attempt restarts annealing from the current best, so a longer slice gives
   one attempt enough time to converge instead of many short attempts that die early. */
static void grow_search(double until) {
    static Graph work;
    while (now() < until && best.n + 2 <= moore) {
        double left = until - now();
        double slice = left < 8.0 ? left : (left / 2 > 8.0 ? left / 2 : 8.0);
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
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
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.96;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        /* Lift search gets up to 75% of the budget and stops early on stall;
           grow-by-two takes whatever time remains. */
        lift_phase(t0 + (t_end - t0) * 0.75);
        grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Overall deadline leaves margin for two C compiles (first call only) and the final check.
    deadline = t0 + 0.86 * time_limit - 1.0

    # Stage 1: bipartite Cayley search (new construction).
    if d >= 3 and D >= 2:
        budget = 0.4 * (deadline - time.monotonic()) - 0.5
        if budget >= 1.0:
            try:
                text = lib.run_c(CAYLEY_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=best, timeout=budget + 4)
                consider(lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                pass

    # Stage 2: lift and grow engine, started from the best graph so far.
    budget = (deadline - time.monotonic()) - 0.5
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 4)
            consider(lib.parse_graph_text(text))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
