"""Two-stage program. Stage 1 is a new construction family: bi-Cayley lifts over random
permutation groups (closure enumerated, arbitrary non-metacyclic groups such as PSL(2,7)
allowed), searched by annealing on the connection darts. Stage 2 hands the best graph to
the parent engine (lift search plus grow-by-two annealing) for the remaining budget. The
K_{d,d} / known-construction start remains the fallback, and every candidate is checked
with lib.is_valid before it is kept."""
import time

import lib

C_NEW = r'''
/* Bold alternative family: bi-Cayley lifts over arbitrary finite permutation groups.
 * G = closure of a few random permutations (degree 4..12), order N, with a full
 * multiplication table. K sides of cosets: A_{i,g} ~ B_{j,g*s} for darts (i,j,s).
 * Each A_i gets d darts (one per layer) and each B_j receives exactly d darts, since each
 * layer is a permutation. Left multiplication is an automorphism, so diameter <= D only
 * needs BFS from the 2K representatives. Output is re-checked in full before use.
 * Usage: prog d D seed time_limit   (stdin ignored). stdout: "n m" then edges.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 1024
#define MAXDEG 32
#define MAXK 3
#define MAXP 12
#define MAXORD 400
#define HSIZE 2048
#define MAXE 16384

typedef unsigned long long u64;

static int d, D;
static double t_end;
static long moore;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 0x2545F4914F6CDD1DULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ------------------------------------------------------------ permutation groups */

static int np_, ngen;
static int GP[4][MAXP];
static u64 Ecode[MAXORD];
static int NG;
static int MT[MAXORD * MAXORD];

static u64 hkey[HSIZE];
static int hval[HSIZE];
static int hstamp[HSIZE];
static int hcur = 1;

static unsigned hslot(u64 key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 40) & (HSIZE - 1);
}

static int hfind(u64 key) {
    unsigned h = hslot(key);
    while (hstamp[h] == hcur) {
        if (hkey[h] == key) return hval[h];
        h = (h + 1) & (HSIZE - 1);
    }
    return -1;
}

static void hput(u64 key, int val) {
    unsigned h = hslot(key);
    while (hstamp[h] == hcur) h = (h + 1) & (HSIZE - 1);
    hstamp[h] = hcur;
    hkey[h] = key;
    hval[h] = val;
}

static u64 encode(const int *p) {
    u64 c = 0;
    for (int i = 0; i < np_; i++) c |= (u64)p[i] << (4 * i);
    return c;
}

static void decode(u64 c, int *p) {
    for (int i = 0; i < np_; i++) p[i] = (int)((c >> (4 * i)) & 15);
}

/* Closure of the generators under right multiplication. Returns the order, or 0 if
   the group exceeds maxord (the caller then rejects it). */
static int closure(int maxord) {
    int a[MAXP], c[MAXP], id[MAXP];
    hcur++;
    for (int i = 0; i < np_; i++) id[i] = i;
    Ecode[0] = encode(id);
    hput(Ecode[0], 0);
    NG = 1;
    for (int x = 0; x < NG; x++) {
        decode(Ecode[x], a);
        for (int s = 0; s < ngen; s++) {
            for (int i = 0; i < np_; i++) c[i] = a[GP[s][i]];
            u64 k = encode(c);
            if (hfind(k) < 0) {
                if (NG >= maxord) return 0;
                Ecode[NG] = k;
                hput(k, NG);
                NG++;
            }
        }
    }
    return NG;
}

/* MT[x*NG+y] = index of element x composed with element y (c[i] = a[b[i]]). */
static void build_mt(void) {
    int a[MAXP], b[MAXP], c[MAXP];
    for (int x = 0; x < NG; x++) {
        decode(Ecode[x], a);
        for (int y = 0; y < NG; y++) {
            decode(Ecode[y], b);
            for (int i = 0; i < np_; i++) c[i] = a[b[i]];
            MT[x * NG + y] = hfind(encode(c));
        }
    }
}

static void random_perm(int *p, int n) {
    for (int i = 0; i < n; i++) p[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1), t = p[i];
        p[i] = p[j];
        p[j] = t;
    }
}

static int random_group(int maxord) {
    np_ = 4 + rndint(9);   /* degree 4..12 */
    ngen = 2 + rndint(2);  /* 2 or 3 generators */
    for (int s = 0; s < ngen; s++) random_perm(GP[s], np_);
    return closure(maxord);
}

/* ------------------------------------------------------------ lifts */

static int K, N;                       /* sides per part, group order */
static int dJ[MAXDEG][MAXK], dS[MAXDEG][MAXK];
static int adjn[MAXV][MAXDEG], degn[MAXV];
static int visv[MAXV], qv[MAXV];
static int vstamp = 0;

/* Cost = 1e6 * duplicate darts + unreached (representative, vertex) pairs. */
static long lift_cost(void) {
    int n = 2 * K * N;
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (dJ[l][i] == dJ[l2][i] && dS[l][i] == dS[l2][i]) dup++;
    for (int v = 0; v < n; v++) degn[v] = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = dJ[l][i], s = dS[l][i];
            for (int g = 0; g < N; g++) {
                int a = i * N + g, b = (K + j) * N + MT[g * N + s];
                adjn[a][degn[a]++] = b;
                adjn[b][degn[b]++] = a;
            }
        }
    long unreached = 0;
    int reps[2 * MAXK], nr = 0;
    for (int i = 0; i < K; i++) reps[nr++] = i * N;
    for (int j = 0; j < K; j++) reps[nr++] = (K + j) * N;
    for (int r = 0; r < nr; r++) {
        vstamp++;
        int head = 0, tail = 0, src = reps[r];
        visv[src] = vstamp;
        qv[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qv[head++];
                for (int t = 0; t < degn[u]; t++) {
                    int v = adjn[u][t];
                    if (visv[v] != vstamp) {
                        visv[v] = vstamp;
                        qv[tail++] = v;
                    }
                }
            }
        }
        unreached += n - tail;
    }
    return dup * 1000000L + unreached;
}

static void random_darts(void) {
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            dJ[l][i] = perm[i];
            dS[l][i] = rndint(N);
        }
    }
}

/* Annealing over darts. Returns the final cost; 0 means a valid lift candidate. */
static long anneal(int steps, double until) {
    random_darts();
    long c = lift_cost();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int l = rndint(d);
        if (K > 1 && rnd01() < 0.3) {
            int a = rndint(K), b = rndint(K);
            if (a == b) continue;
            int t = dJ[l][a];
            dJ[l][a] = dJ[l][b];
            dJ[l][b] = t;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.02) c = c2;
            else {
                t = dJ[l][a];
                dJ[l][a] = dJ[l][b];
                dJ[l][b] = t;
            }
        } else {
            int i = rndint(K), old = dS[l][i];
            dS[l][i] = rndint(N);
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.02) c = c2;
            else dS[l][i] = old;
        }
    }
    return c;
}

/* ------------------------------------------------------------ best graph */

static int bn, bm;
static int bu[MAXE], bv[MAXE];
static int cadj[MAXV][MAXDEG], cdeg[MAXV];
static int cvis[MAXV], cq[MAXV];
static int cstamp = 0;

/* Full validation: simple, bipartite by side labels, degree <= d, diameter <= D. */
static int check_graph(int n, int m, const int *eu, const int *ev, const int *side) {
    if (n <= 0 || n > MAXV || m > MAXE) return 0;
    for (int v = 0; v < n; v++) cdeg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || side[u] == side[v]) return 0;
        if (cdeg[u] >= d || cdeg[v] >= d) return 0;
        cadj[u][cdeg[u]++] = v;
        cadj[v][cdeg[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        for (int i = 0; i < cdeg[v]; i++)
            for (int j = 0; j < i; j++)
                if (cadj[v][i] == cadj[v][j]) return 0;
    for (int src = 0; src < n; src++) {
        cstamp++;
        int head = 0, tail = 0;
        cvis[src] = cstamp;
        cq[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = cq[head++];
                for (int t = 0; t < cdeg[u]; t++) {
                    int v = cadj[u][t];
                    if (cvis[v] != cstamp) {
                        cvis[v] = cstamp;
                        cq[tail++] = v;
                    }
                }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

/* Store the current lift (adjn must match the current darts) if valid and larger. */
static int lift_to_best(void) {
    int n = 2 * K * N;
    static int eu[MAXE], ev[MAXE], side[MAXV];
    int m = 0;
    for (int v = 0; v < n; v++) side[v] = v >= K * N;
    for (int a = 0; a < K * N; a++)
        for (int t = 0; t < degn[a]; t++) {
            if (m >= MAXE) return 0;
            eu[m] = a;
            ev[m] = adjn[a][t];
            m++;
        }
    if (n <= bn) return 0;
    if (!check_graph(n, m, eu, ev, side)) return 0;
    for (int e = 0; e < m; e++) {
        bu[e] = eu[e];
        bv[e] = ev[e];
    }
    bn = n;
    bm = m;
    return 1;
}

static void print_best(void) {
    printf("%d %d\n", bn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", bu[e], bv[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXDEG || D < 2 || 2 * d > MAXV) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    /* Fallback start: K_{d,d}, valid for D >= 2. */
    bn = 2 * d;
    bm = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            bu[bm] = a;
            bv[bm] = d + b;
            bm++;
        }

    long maxN = moore / 2;
    if (maxN > MAXORD) maxN = MAXORD;
    while (now() < t_end && bn < moore) {
        int g = random_group((int)maxN);
        if (g < 2) continue;
        N = NG;
        int built = 0;
        for (K = 1; K <= MAXK; K++) {
            long nv = 2L * K * N;
            if (nv > moore || nv <= bn || nv > MAXV) continue;
            if (!built) {
                build_mt();
                built = 1;
            }
            for (int att = 0; att < 2 && now() < t_end && bn < moore; att++) {
                long c = anneal(3000, t_end);
                if (c == 0) {
                    lift_cost();          /* refresh adjacency to the accepted darts */
                    lift_to_best();
                }
            }
        }
    }
    print_best();
    return 0;
}
'''

C_PARENT = r'''
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
        try:
            if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except Exception:
            pass

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    bound = lib.moore_bound(d, D)
    if best[0] >= bound:
        return best

    # Keep a margin for C compilation (not counted by the C clock) and process exit.
    usable = 0.85 * time_limit

    def remaining():
        return usable - (time.monotonic() - t0)

    # Stage 1: new family, bi-Cayley lifts over random permutation groups.
    b1 = 0.45 * remaining() - 1.0
    if b1 >= 1.0:
        try:
            text = lib.run_c(C_NEW, [d, D, seed, round(b1, 2)], timeout=b1 + 3)
            consider(lib.parse_graph_text(text))
        except (RuntimeError, ValueError):
            pass

    # Stage 2: parent engine grows whatever stage 1 produced (or the start graph).
    b2 = remaining() - 1.0
    if b2 >= 1.0 and best[0] < bound:
        try:
            text = lib.run_c(C_PARENT, [d, D, seed + 1, round(b2, 2)],
                             stdin_graph=best, timeout=b2 + 3)
            consider(lib.parse_graph_text(text))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
