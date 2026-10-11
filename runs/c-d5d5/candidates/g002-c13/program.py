"""Bold variant: exact bi-Cayley lifts over explicit non-metacyclic groups.

Stage 1 (new): for a list of concrete groups G (permutation groups, matrix groups,
affine groups, direct products), the C engine searches k-vertex-per-side bi-Cayley
graphs with A_{i,g} ~ B_{j,g*s} (voltage darts s in G). Left multiplication is an
automorphism, so diameter is checked by BFS from the k A-representatives and the
k B-representatives only. Groups are tried from small to large order.

Stage 2 (legacy fallback): the previous semidirect-product lift and grow-by-two
engine, started from the best graph of stage 1, so a valid graph is never lost.
"""
import itertools
import time

import lib

# ----------------------------------------------------------------- C: bi-Cayley search

C_BICAYLEY = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 2400
#define MAXD 32
#define MAXK 4
#define MAXDART (MAXD * MAXK)
#define MAXG 32
#define MAXE (MAXV * MAXD / 2 + 8)

typedef struct { int k, N; int *T; } Grp;

static int d, D;
static long moore;
static int G;
static Grp grp[MAXG];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
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

/* Current lift state. Vertices: A_{i,g} = i*N+g, B_{j,g} = (K+j)*N+g. */
static int K, N, ND;
static const int *MT;
static int dI[MAXDART], dJ[MAXDART], dS[MAXDART];
static int adjc[MAXV][MAXD];
static int degc[MAXV];
static int vis[MAXV], vstamp = 0, qq[MAXV];

static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];

/* Cost = 1e6 * duplicate darts + total unreached (representative, vertex) pairs. */
static long cost(void) {
    int n = 2 * K * N;
    long pen = 0;
    for (int t = 0; t < ND; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    for (int v = 0; v < n; v++) degc[v] = 0;
    for (int t = 0; t < ND; t++) {
        for (int g = 0; g < N; g++) {
            int a = dI[t] * N + g;
            int b = (K + dJ[t]) * N + MT[g * N + dS[t]];
            adjc[a][degc[a]++] = b;
            adjc[b][degc[b]++] = a;
        }
    }
    long unreached = 0;
    int reps[2 * MAXK], nr = 0;
    for (int i = 0; i < K; i++) reps[nr++] = i * N;
    for (int j = 0; j < K; j++) reps[nr++] = (K + j) * N;
    for (int r = 0; r < nr; r++) {
        vstamp++;
        int head = 0, tail = 0, src = reps[r];
        vis[src] = vstamp;
        qq[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qq[head++];
                for (int i = 0; i < d; i++) {
                    int v = adjc[u][i];
                    if (vis[v] != vstamp) {
                        vis[v] = vstamp;
                        qq[tail++] = v;
                    }
                }
            }
        }
        unreached += n - tail;
    }
    return pen * 1000000L + unreached;
}

/* Random base: d layers, each a permutation of the K A-vertices onto the K B-vertices. */
static void random_darts(void) {
    ND = d * K;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(N);
        }
    }
}

static int climb(double until, int steps) {
    random_darts();
    long c = cost();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        if (K > 1 && rnd01() < 0.25) {
            int l = rndint(d), a = rndint(K), b = rndint(K);
            if (a == b) continue;
            int t1 = l * K + a, t2 = l * K + b;
            int tmp = dJ[t1];
            dJ[t1] = dJ[t2];
            dJ[t2] = tmp;
            long c2 = cost();
            if (c2 <= c || rnd01() < 0.02) c = c2;
            else {
                tmp = dJ[t1];
                dJ[t1] = dJ[t2];
                dJ[t2] = tmp;
            }
        } else {
            int t = rndint(ND);
            int old = dS[t];
            dS[t] = rndint(N);
            long c2 = cost();
            if (c2 <= c || rnd01() < 0.02) c = c2;
            else dS[t] = old;
        }
    }
    return c == 0;
}

static void record_best(void) {
    int n = 2 * K * N, m = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < N; g++) {
            bestU[m] = dI[t] * N + g;
            bestV[m] = (K + dJ[t]) * N + MT[g * N + dS[t]];
            m++;
        }
    bestN = n;
    bestM = m;
}

static void run_group(int gi, double until) {
    K = grp[gi].k;
    N = grp[gi].N;
    MT = grp[gi].T;
    long n = 2L * K * N;
    if (n > moore || n > MAXV || n <= bestN) return;
    while (now() < until) {
        if (climb(until, 6000)) {
            record_best();
            return;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();
    double t_end = now() + limit * 0.92;

    /* stdin: header "n m", then m pairs; the pairs form a flat int stream. */
    int hn, hm;
    if (scanf("%d %d", &hn, &hm) != 2 || hm < 1) {
        printf("0 0\n");
        return 0;
    }
    long total = 2L * hm;
    int *flat = malloc(sizeof(int) * (size_t)total);
    if (!flat) {
        printf("0 0\n");
        return 0;
    }
    for (long i = 0; i < total; i++)
        if (scanf("%d", &flat[i]) != 1) {
            printf("0 0\n");
            return 0;
        }
    long p = 0;
    G = flat[p++];
    if (G < 1 || G > MAXG) {
        printf("0 0\n");
        return 0;
    }
    for (int gi = 0; gi < G; gi++) {
        if (p + 2 > total) {
            printf("0 0\n");
            return 0;
        }
        int k = flat[p++];
        int Nn = flat[p++];
        if (k < 1 || k > MAXK || Nn < 1 || Nn > MAXV) {
            printf("0 0\n");
            return 0;
        }
        if (p + (long)Nn * Nn > total) {
            printf("0 0\n");
            return 0;
        }
        grp[gi].k = k;
        grp[gi].N = Nn;
        grp[gi].T = malloc(sizeof(int) * (size_t)Nn * Nn);
        for (int i = 0; i < Nn * Nn; i++) grp[gi].T[i] = flat[p++];
    }

    for (int gi = 0; gi < G; gi++) {
        double rem = t_end - now();
        if (rem <= 0) break;
        run_group(gi, now() + rem / (G - gi));
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int m = 0; m < bestM; m++) printf("%d %d\n", bestU[m], bestV[m]);
    return 0;
}
'''

# ----------------------------------------------------------------- C: legacy engine

C_LEGACY = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): bi-Cayley lifts over groups Z_m x| Z_k2 with k vertices per side.
 *   A_{i,g} ~ B_{j,g*s} for each dart (i,j,s). Left multiplication is an automorphism,
 *   so diameter <= D is checked by BFS from the 2k representatives only.
 *   Hill-climb on voltages (and occasionally on the target matching of a layer).
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

static void lift_phase(double until) {
    static Graph cand;
    static const int kc[6] = {1, 1, 1, 2, 2, 3};
    int fails = 0;
    while (now() < until && best.n < moore) {
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
        if (lift_attempt(4000, until)) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
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

static void grow_search(double until) {
    static Graph work;
    while (now() < until && best.n + 2 <= moore) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        lift_phase(t0 + (t_end - t0) * 0.75);
        grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# ----------------------------------------------------------------- Python: groups

_MAX_VERTS = 1200


def _mm(A, B, n, p):
    """Product of n x n matrices (row-major tuples) over Z_p."""
    return tuple(sum(A[i * n + k] * B[k * n + j] for k in range(n)) % p
                 for i in range(n) for j in range(n))


def _invertible(M, n, p):
    """True if the n x n matrix M (row-major tuple) is invertible over Z_p, p prime."""
    A = [[M[i * n + j] for j in range(n)] for i in range(n)]
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, n) if A[i][c] % p), None)
        if piv is None:
            return False
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [(x * inv) % p for x in A[r]]
        for i in range(n):
            if i != r and A[i][c] % p:
                f = A[i][c]
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(n)]
        r += 1
    return True


def _perm_group(n, pred):
    """Permutations of range(n) satisfying pred, composed as functions."""
    elems = [p for p in itertools.permutations(range(n)) if pred(p)]
    return elems, (lambda p, q: tuple(p[i] for i in q)), tuple(range(n))


def _even(p):
    inv = sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j])
    return inv % 2 == 0


def _cyclic(k):
    return list(range(k)), (lambda a, b: (a + b) % k), 0


def _direct(G, H):
    """Direct product of two groups given as (elements, mul, identity)."""
    (E1, m1, i1), (E2, m2, i2) = G, H
    elems = [(x, y) for x in E1 for y in E2]
    return elems, (lambda u, v: (m1(u[0], v[0]), m2(u[1], v[1]))), (i1, i2)


def _sl2(p):
    """SL(2,p) as 2x2 row-major tuples."""
    elems = [M for M in itertools.product(range(p), repeat=4)
             if (M[0] * M[3] - M[1] * M[2]) % p == 1]
    return elems, (lambda A, B: _mm(A, B, 2, p)), (1, 0, 0, 1)


def _gl32():
    """GL(3,2), order 168 (= PSL(2,7))."""
    elems = [M for M in itertools.product(range(2), repeat=9) if _invertible(M, 3, 2)]
    return elems, (lambda A, B: _mm(A, B, 3, 2)), (1, 0, 0, 0, 1, 0, 0, 0, 1)


def _asl23():
    """Affine group ASL(2,3) = Z_3^2 : SL(2,3), order 216."""
    A_els = _sl2(3)[0]
    elems = [(A, b) for A in A_els for b in itertools.product(range(3), repeat=2)]

    def mul(x, y):
        A, b = x
        C, c = y
        Ac = ((A[0] * c[0] + A[1] * c[1]) % 3, (A[2] * c[0] + A[3] * c[1]) % 3)
        return (_mm(A, C, 2, 3), ((Ac[0] + b[0]) % 3, (Ac[1] + b[1]) % 3))

    return elems, mul, ((1, 0, 0, 1), (0, 0))


def _agl_prime(p):
    """AGL(1,p) = {x -> a x + b}, order p(p-1)."""
    elems = [(a, b) for a in range(1, p) for b in range(p)]
    return elems, (lambda x, y: ((x[0] * y[0]) % p, (x[0] * y[1] + x[1]) % p)), (1, 0)


def _agl16():
    """AGL(1,16) over GF(16), order 240."""
    F = lib.GF(16)
    elems = [(a, b) for a in range(1, 16) for b in range(16)]
    return elems, (lambda x, y: (F.mul(x[0], y[0]), F.add(F.mul(x[0], y[1]), x[1]))), (1, 0)


# (name, k vertices per side, builder). Vertex count of the lift is 2*k*|G|.
_FAMILIES = [
    ("GL32", 1, _gl32),
    ("A5", 3, lambda: _perm_group(5, _even)),
    ("A5xZ3", 1, lambda: _direct(_perm_group(5, _even), _cyclic(3))),
    ("A4xZ15", 1, lambda: _direct(_perm_group(4, _even), _cyclic(15))),
    ("ASL23", 1, _asl23),
    ("S5xZ2", 1, lambda: _direct(_perm_group(5, lambda p: True), _cyclic(2))),
    ("AGL16", 1, _agl16),
    ("SL25xZ2", 1, lambda: _direct(_sl2(5), _cyclic(2))),
    ("AGL17", 1, lambda: _agl_prime(17)),
    ("S5", 2, lambda: _perm_group(5, lambda p: True)),
    ("SL25", 2, lambda: _sl2(5)),
    ("A5xZ2", 2, lambda: _direct(_perm_group(5, _even), _cyclic(2))),
]


def _table(elems, mul, ident):
    """Multiplication table (row-major flat list) with the identity at index 0."""
    els = [ident] + [e for e in elems if e != ident]
    idx = {e: i for i, e in enumerate(els)}
    T = []
    for x in els:
        T.extend(idx[mul(x, y)] for y in els)
    return len(els), T


def _pack(groups):
    """Flat integer stream G, then per group k, N, table; sent as the 'edges' of a graph text."""
    flat = [len(groups)]
    for k, N, T in groups:
        flat += [k, N]
        flat += T
    if len(flat) % 2:
        flat.append(0)
    return (0, [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)])


def _bicayley_stage(d, D, seed, lo, hi, seconds):
    """Run the bi-Cayley engine over the explicit groups; return (n, edges) or None."""
    if seconds < 1.0:
        return None
    fams = []
    for name, k, make in _FAMILIES:
        elems, mul, ident = make()
        n = 2 * k * len(elems)
        if lo < n <= min(hi, _MAX_VERTS):
            fams.append((n, k, elems, mul, ident))
    if not fams:
        return None
    fams.sort(key=lambda t: t[0])
    groups = []
    for n, k, elems, mul, ident in fams:
        try:
            N, T = _table(elems, mul, ident)
        except KeyError:
            continue  # not closed: skip this family
        groups.append((k, N, T))
    if not groups:
        return None
    text = lib.run_c(C_BICAYLEY, [d, D, seed, round(seconds, 2)],
                     stdin_graph=_pack(groups), timeout=seconds + 5)
    return lib.parse_graph_text(text)


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
    moore = lib.moore_bound(d, D)

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    if best[0] >= moore:
        return best

    avail = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if avail < 2.0:
        return best
    b1 = 0.6 * avail
    b2 = avail - b1

    try:
        consider(_bicayley_stage(d, D, seed, best[0], moore, b1))
    except Exception:
        pass

    try:
        text = lib.run_c(C_LEGACY, [d, D, seed, round(b2, 2)],
                         stdin_graph=best, timeout=b2 + 5)
        consider(lib.parse_graph_text(text))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
