"""Two-stage search for bipartite degree-diameter graphs.

Stage 1 (new): bipartite Cayley-type graphs. Vertices a_x and b_x for x in a group G of order N,
with a_x adjacent to b_{x s} for s in a d-element set S. Left multiplication is an automorphism,
so the diameter check needs only two BFS runs (from a_e and b_e). Simulated annealing over S
runs on random semidirect products Z_m x| Z_k of order near the current best.

Stage 2 (fallback): the previous combined engine (lift search, grow-by-two annealing, ruin and
recreate) starts from the best graph found so far, so the result is never worse than the start.

Every candidate is checked in C and again with lib.is_valid before it is accepted."""
import itertools
import time

import lib

CAYLEY_SOURCE = r'''
/* Bipartite Cayley-type search over semidirect products Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit start_n
 * Output: "n m" plus edges of a valid graph with n > start_n, or "0 0". */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 512
#define MAXV (2 * MAXN)
#define MAXD 16

static int d, D;
static double t_end;

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

/* Group Z_GM x|_GR Z_GK, order N = GM*GK, element a*GK + b, identity 0. */
static int N, GM, GK, GR;
static int RP[MAXN];
static int MT[MAXN][MAXN];
static int INV[MAXN];

static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK + (b + e) % GK;
}

static void build_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    N = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[x][y] = gmul_raw(x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

/* Pick a uniformly random semidirect product of order n (cyclic included). */
static int random_group(int n) {
    static int cm[4096], ck[4096], cr[4096];
    int c = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (c < 4096) { cm[c] = 1; ck[c] = k; cr[c] = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (c < 4096) { cm[c] = m; ck[c] = k; cr[c] = r; c++; }
        }
    }
    if (!c) return 0;
    int p = rndint(c);
    build_group(cm[p], ck[p], cr[p]);
    return 1;
}

/* Connection set S (d distinct group elements) and its inverses SI. */
static int S[MAXD], SI[MAXD];
static int dist_[MAXV], q_[MAXV];

static inline int nbr(int v, int j) {
    return v < N ? N + MT[v][S[j]] : MT[v - N][SI[j]];
}

/* Number of vertices at distance > D from src. */
static int unreached(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    q_[t++] = src;
    while (h < t) {
        int v = q_[h++];
        if (dist_[v] >= D) continue;
        for (int j = 0; j < d; j++) {
            int u = nbr(v, j);
            if (dist_[u] < 0) {
                dist_[u] = dist_[v] + 1;
                q_[t++] = u;
            }
        }
    }
    return V - t;
}

/* By left-multiplication symmetry, these two sources cover all pairs. */
static int cost(void) { return unreached(0) + unreached(N); }

static int in_upto(int x, int upto) {
    for (int j = 0; j < upto; j++) if (S[j] == x) return 1;
    return 0;
}

static int in_S(int x) { return in_upto(x, d); }

/* Anneal S (replace one element at a time) until cost 0 or the budget runs out. */
static int anneal(int iters) {
    for (int j = 0; j < d; j++) {
        int x;
        do x = rndint(N); while (in_upto(x, j));
        S[j] = x;
    }
    for (int j = 0; j < d; j++) SI[j] = INV[S[j]];
    int c = cost();
    double T0 = 1.0, T1 = 0.05;
    for (int it = 0; it < iters && c > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int j = rndint(d);
        int old = S[j];
        int x;
        do x = rndint(N); while (in_S(x));
        S[j] = x;
        SI[j] = INV[x];
        int nc = cost();
        if (nc <= c || rnd01() < exp((c - nc) / T)) {
            c = nc;
        } else {
            S[j] = old;
            SI[j] = INV[old];
        }
    }
    return c == 0;
}

/* Full check, then print. Prints nothing and returns 0 if the graph is invalid. */
static int verify_print(void) {
    int V = 2 * N;
    for (int j = 0; j < d; j++) {
        SI[j] = INV[S[j]];
        for (int k = 0; k < j; k++) if (S[j] == S[k]) return 0;
    }
    for (int src = 0; src < V; src++)
        if (unreached(src)) return 0;
    printf("%d %d\n", V, N * d);
    for (int x = 0; x < N; x++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", x, N + MT[x][S[j]]);
    return 1;
}

static int bestN = 0, bestM, bestK, bestR;
static int bestS[MAXD];

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long startn = atol(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + limit * 0.93;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    long sum = 0, p = 1;
    for (int i = 0; i < D; i++) {
        sum += p;
        p *= (d - 1);
        if (sum > 1000000) break;
    }
    /* Each side has at most sum vertices (Moore bound 2*sum). */
    long Nmax = sum;
    if (Nmax > MAXN) Nmax = MAXN;
    long lo = startn / 2 + 1;
    if (lo < d + 1) lo = d + 1;

    while (now() < t_end) {
        if (lo > Nmax) break;
        long cand = lo + rndint(6);
        if (cand > Nmax) cand = Nmax;
        if (!random_group((int)cand)) continue;
        int ok = 0;
        for (int a = 0; a < 4 && !ok && now() < t_end; a++) ok = anneal(30000);
        if (ok) {
            bestN = N;
            bestM = GM;
            bestK = GK;
            bestR = GR;
            memcpy(bestS, S, sizeof(S));
            lo = bestN + 1;
        }
    }

    if (bestN > 0) {
        build_group(bestM, bestK, bestR);
        memcpy(S, bestS, sizeof(S));
        if (verify_print()) return 0;
    }
    printf("0 0\n");
    return 0;
}
'''

PARENT_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Voltage lifts over semidirect groups Z_m x|_r Z_k, base multigraphs on p <= 4 vertices per
 *    side. The diameter objective is orbit-reduced: BFS from the 2p fibre representatives only.
 * 2. Grow by two: insert one vertex per side and anneal degree-preserving edge swaps.
 *    The swap endpoint is chosen from the set of vertices lying in bad pairs.
 * 3. Ruin and recreate: when growth stalls, delete a few edges, refill deficits, repair by
 *    annealing, and move to the resulting same-order graph (plateau walk). Every 8 failures,
 *    the lift search is retried from the current best.
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
#define MAXP 4

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

static long edge_count(const Graph *g) {
    long s = 0;
    for (int v = 0; v < g->n; v++) s += g->deg[v];
    return s / 2;
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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D.
 * Also fills badv[v] = number of vertices at distance > D from v. */
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

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
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

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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

/* Orbit-reduced diameter objective for a regular-fibre lift.
 * The group acts by left multiplication on every fibre, so it is enough to BFS from the
 * 2p representatives b*N. Returns the number of (representative, vertex) pairs at distance > D. */
static int dist_buf[MAXN], queue_buf[MAXN];

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

/* Hill-climb the voltages of one random base multigraph over the group G. */
static int lift_fast_try(Graph *g, int p, int N, const Grp *G, int steps, double until) {
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
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad == 0;
}

/* Search lifts of size 2pN strictly larger than the current best. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int Nmin = (int)((target + 2 * p - 1) / (2 * p));
        int N = Nmin + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2 * p * N > MAXN) continue;
        if (!random_group(N, &G)) continue;
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_fast_try(&cand, p, N, &G, 20000, until) && is_valid(&cand) &&
                cand.n > best->n) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* Bad-pair roulette: uniformly random vertex that lies in some bad pair. */
static int pick_bad_vertex(const Graph *g) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list[c++] = v;
    if (c == 0) return rndint(g->n);
    return list[rndint(c)];
}

/* Anneal degree-preserving swaps until the graph has diameter <= D.
 * Returns 1 on success, 0 if the deadline passed first. */
static int anneal(Graph *w, double until) {
    long bad = bad_pairs(w);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = pick_bad_vertex(w);
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
            bad_pairs(w);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return 1;
}

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
    if (!anneal(work, until)) return 0;
    return is_valid(work);
}

/* Ruin and recreate: delete a few random edges of src, refill the deficits with random
 * non-adjacent cross pairs, then repair diameter by annealing. */
static int ruin_recreate(const Graph *src, Graph *w, double until) {
    copy_graph(w, src);
    int n = w->n;
    int R = 2 + rndint(4);
    for (int r = 0; r < R; r++) {
        int v = rndint(n);
        if (!w->deg[v]) continue;
        int u = w->adj[v][rndint(w->deg[v])];
        del_edge(w, v, u);
    }
    for (int tries = 0; tries < 20000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || w->deg[a] >= d) continue;
        int b = rndint(n);
        if (w->side[b] != 1 || w->deg[b] >= d || has_edge(w, a, b)) continue;
        add_edge(w, a, b);
    }
    if (!anneal(w, until)) return 0;
    return is_valid(w) && edge_count(w) >= edge_count(src);
}

static void grow_search(Graph *best, double until) {
    static Graph work, cand;
    int fails = 0;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) {
            copy_graph(best, &work);
            fails = 0;
            continue;
        }
        fails++;
        if (fails % 8 == 0) {
            double lu = now() + 1.0 < until ? now() + 1.0 : until;
            fast_lift_search(best, lu);
            if (best->n + 2 > moore_bound()) break;
        }
        double rr_until = now() + 1.0 < until ? now() + 1.0 : until;
        if (ruin_recreate(best, &cand, rr_until)) copy_graph(best, &cand);
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
    t_end = t0 + limit * 0.94;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        fast_lift_search(&best, t0 + (t_end - t0) * 0.6);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    def remaining():
        return 0.92 * time_limit - (time.monotonic() - t0) - 2.5

    # Stage 1: bipartite Cayley-type search over semidirect products.
    b1 = 0.6 * remaining()
    if b1 > 1.0:
        try:
            text = lib.run_c(CAYLEY_SOURCE, [d, D, seed, round(b1, 2), best[0]],
                             timeout=b1 + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    # Stage 2: the previous combined engine, seeded with the best graph so far.
    b2 = remaining()
    if b2 > 1.0:
        try:
            text = lib.run_c(PARENT_SOURCE, [d, D, seed, round(b2, 2)],
                             stdin_graph=best, timeout=b2 + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    return best
