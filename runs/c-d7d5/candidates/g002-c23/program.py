"""Combined program: exact constructions in Python, then one C engine that runs
bi-Cayley annealing, voltage-lift hill-climbing and grow-by-two from the best graph so far."""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search engine.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (a valid start graph), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases (times are fractions of the internal budget):
 *   A. Bi-Cayley annealing: layered permutations and voltages over Z_m x| Z_k.
 *      The cost counts unreached (representative, vertex) pairs by BFS from the
 *      2K identity representatives, which is exact by left-multiplication symmetry.
 *   B. Voltage-lift hill-climbing over random d-regular base multigraphs.
 *   C. Grow by two: add one vertex per side, then anneal degree-preserving swaps.
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
#define MAXK 8
#define PEN 1000LL

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double deadline;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* Number of unordered pairs at distance > D. Zero means diameter <= D (connected). */
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
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a,b) is coded a*k + b; (a,b)(c,e) = (a + r^b c, b + e). */
static int GM = 1, GK = 1, GG = 1;
static int pw[MAXN];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)((a + (long long)pw[b] * c) % GM);
    return na * GK + (b + e) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
}

/* Random r with r^k = 1 mod m and gcd(r,m) = 1, or -1 if none was found. */
static int pick_r(int m, int k2) {
    if (k2 == 1 || m <= 2 || rndint(3) == 0) return 1;
    for (int t = 0; t < 300; t++) {
        int r = 2 + rndint(m - 2);
        if (gcdi(r, m) == 1 && powmod(r, k2, m) == 1 % m) return r;
    }
    return -1;
}

/* Uniformly random semidirect group of order N (reservoir over (m, r) choices). */
static int random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcdi(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                bm = m; bk = k; br = r;
            }
        }
    }
    if (count == 0) return 0;
    set_group(bm, bk, br);
    return 1;
}

/* ------------------------------------------------------------ phase A: bi-Cayley annealing */

static int BK = 1;
static int bperm[MAXD][MAXK], bvol[MAXD][MAXK];
static int sperm[MAXD][MAXK], svol[MAXD][MAXK];
static int NB[MAXN * MAXD], NC[MAXN], VIS[MAXN], QU[MAXN];
static int vstamp = 0;

static void bc_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < BK; i++) bperm[l][i] = i;
        for (int i = BK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = bperm[l][i];
            bperm[l][i] = bperm[l][j];
            bperm[l][j] = t;
        }
        for (int i = 0; i < BK; i++) bvol[l][i] = rndint(GG);
    }
}

/* Unreached (representative, vertex) pairs within D steps, plus a penalty for duplicate darts. */
static long long bc_cost(void) {
    int K = BK, G = GG, N = 2 * K * G, nd = d * K;
    long long dup = 0;
    for (int x = 0; x < nd; x++)
        for (int y = x + 1; y < nd; y++) {
            int l1 = x / K, i1 = x % K, l2 = y / K, i2 = y % K;
            if (i1 == i2 && bperm[l1][i1] == bperm[l2][i2] && bvol[l1][i1] == bvol[l2][i2])
                dup++;
        }
    memset(NC, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = bperm[l][i], s = bvol[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                NB[a * d + NC[a]++] = b;
                NB[b * d + NC[b]++] = a;
            }
        }
    if (vstamp > 1000000000) {
        memset(VIS, 0, sizeof VIS);
        vstamp = 0;
    }
    long long total = 0;
    for (int q = 0; q < 2 * K; q++) {
        int src = q < K ? q * G : (K + (q - K)) * G;
        vstamp++;
        int head = 0, tail = 0;
        QU[tail++] = src;
        VIS[src] = vstamp;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = QU[head++];
                for (int t = 0; t < d; t++) {
                    int v = NB[u * d + t];
                    if (VIS[v] != vstamp) {
                        VIS[v] = vstamp;
                        QU[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total + PEN * dup;
}

static void bc_mutate(void) {
    if (rnd01() < 0.6) {
        int l = rndint(d), i = rndint(BK);
        bvol[l][i] = rndint(GG);
    } else {
        int l = rndint(d), i1 = rndint(BK), i2 = rndint(BK);
        int t = bperm[l][i1];
        bperm[l][i1] = bperm[l][i2];
        bperm[l][i2] = t;
    }
}

static int bc_anneal(int iters) {
    bc_init();
    long long cost = bc_cost();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 255) == 0 && now() > deadline) return 0;
        memcpy(sperm, bperm, sizeof bperm);
        memcpy(svol, bvol, sizeof bvol);
        bc_mutate();
        long long c2 = bc_cost();
        double temp = 2.0 * (1.0 - (double)it / iters) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            memcpy(bperm, sperm, sizeof bperm);
            memcpy(bvol, svol, sizeof bvol);
        }
    }
    return cost == 0;
}

static void bc_graph(Graph *g) {
    int K = BK, G = GG;
    g->n = 2 * K * G;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= K * G;
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = bperm[l][i], s = bvol[l][i];
            for (int gg = 0; gg < G; gg++)
                add_edge(g, i * G + gg, (K + j) * G + gmul(gg, s));
        }
}

static void bicayley_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    deadline = until;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int K = 1 + rndint(4);
        long base = best->n / (2L * K) + 1;
        long G = base + rndint((int)(base / 16 + 1));
        long N = 2L * K * G;
        if (N > moore || N > MAXN) continue;
        int cands[64], nc = 0;
        for (int x = 1; x <= 30 && x <= G; x++)
            if (G % x == 0) cands[nc++] = x;
        int k2 = cands[rndint(nc)];
        int m = (int)(G / k2);
        int r = pick_r(m, k2);
        if (r < 0) continue;
        set_group(m, k2, r);
        BK = K;
        if (bc_anneal(4000)) {
            bc_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------ phase B: voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
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
                if (linked) {
                    seen[u] = 1;
                    nseen++;
                    stack[top++] = u;
                }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void lift_build(Graph *g, int p, const Dart *dt, int nd) {
    int N = GG;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= p * N;
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j) {
    for (;;) {
        int g = rndint(GG), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
}

static int lift_try(Graph *g, int p, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j);
                nd++;
            }
    lift_build(g, p, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > deadline) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j);
        lift_build(g, p, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    lift_build(g, p, dt, nd);
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    deadline = until;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (best->n > 0) target += rndint(2 + best->n / 20);
        if (target > moore) return;
        long N = (target + 2 * p - 1) / (2 * p) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group((int)N)) continue;
        int steps = 200 + (int)(400000 / (2L * p * N));
        if (lift_try(&cand, p, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------ phase C: grow by two */

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

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    static Graph best;
    read_start(&best);
    int had = best.n > 0;
    if (!had) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double total = t_end - t0;
        double fA = had ? 0.25 : 0.45;
        bicayley_search(&best, t0 + fA * total);
        lift_search(&best, t0 + (fA + 0.2) * total);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _moore_pg(d):
    """Incidence graph of PG(2, d-1): a Moore graph for D = 3, when d-1 is a prime power."""
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez record graph for D = 3 when d-2 is a prime power >= 3."""
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def known_start(d, D):
    """Best exact construction Python builds directly for (d, D), or None."""
    if D != 3:
        return None
    return _moore_pg(d) or _araujo(d)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    if D == 2:
        return best

    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    budget = min(remaining, time_limit - 8.0)
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                         stdin_graph=best, timeout=budget + 8.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
