"""Combined program: bi-Cayley group search, then voltage-lift and grow-by-two refinement.

Phases inside the C engine:
  A. Bi-Cayley graphs over metacyclic groups Z_m x| Z_k (nonabelian first). Scan N upward
     from a lower bound and keep the largest order that succeeds. Left multiplication is an
     automorphism, so the diameter check needs only BFS from A_1 and B_1.
  B. Voltage lifts of small d-regular base multigraphs over random groups of order near the
     target, hill-climbing on voltages. Half the draws aim at the record goal.
  C. Grow by two: insert one vertex per side and anneal degree-preserving swaps.
Every graph is checked by a full bitset diameter test before it is kept. Python keeps the
best of the start graph and the C result, and checks everything with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Combined bipartite degree-diameter search.
 * usage: prog d D seed time_limit [goal] [nlo]   < start_graph
 * stdin:  "n m" then m lines "u v" (valid start), or "0 0".
 * stdout: "n m" then m lines "u v": the best valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXV (2 * MAXG)
#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXGRP 8192

static int d, D;
static double t_end;
static long goal_n = 0;

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

/* ------------------------------------------------------------------ graph basics */

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
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

/* Full validity: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ groups Z_m x|_r Z_k */

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct { int m, k, r; } Grp;

static Grp GL[MAXGRP];
static int GTOT, GNAB;          /* GL[0..GNAB-1] nonabelian, the rest abelian */
static int RP[MAXN];            /* RP[b] = r^b mod m for the current group */
static int CUR_M, CUR_K;
static int MT[MAXG * MAXG];     /* multiplication table (bi-Cayley only) */
static int INV[MAXG];

static void enum_groups(int N) {
    GTOT = 0;
    GNAB = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) {
                if (pass == 1 && GTOT < MAXGRP) {
                    GL[GTOT].m = 1; GL[GTOT].k = k; GL[GTOT].r = 0; GTOT++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (GTOT < MAXGRP) {
                    GL[GTOT].m = m; GL[GTOT].k = k; GL[GTOT].r = r; GTOT++;
                }
            }
        }
        if (pass == 0) GNAB = GTOT;
    }
}

static void set_group(Grp G) {
    CUR_M = G.m;
    CUR_K = G.k;
    RP[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) RP[b] = (int)((long)RP[b - 1] * G.r % G.m);
}

static int gmul(int x, int y) {
    int k = CUR_K, m = CUR_M;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return (int)(((long)a + (long)RP[b] * c) % m) * k + (b + e) % k;
}

/* Multiplication and inverse tables for the current group (order CUR_M * CUR_K <= MAXG - 1). */
static void build_mt(void) {
    int n = CUR_M * CUR_K;
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++) MT[x * n + y] = gmul(x, y);
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ------------------------------------------------------------------ bi-Cayley search */

static int BN;                  /* current bi-Cayley group order */
static int dist_[MAXV], queue_[MAXV];

/* 1 iff every vertex of the bi-Cayley graph is within D of src.
 * A_x = x, B_h = BN + h; A_x ~ B_{x s}; B_h ~ A_{h s^-1}. */
static int reach_all(const int *S, int src) {
    int n = BN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

/* Random connection set S = {0, s_1, ..., s_{d-1}} of distinct elements. */
static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

static int bc_found = 0, bc_N = 0;
static Grp bc_G;
static int bc_S[MAXD];

static int bc_search_n(int N, double until) {
    enum_groups(N);
    if (GTOT == 0) return 0;
    int S[MAXD];
    BN = N;
    while (now() < until) {
        for (int gi = 0; gi < GTOT; gi++) {
            if (now() >= until) break;
            set_group(GL[gi]);
            build_mt();
            for (int t = 0; t < 300; t++) {
                pick_set(N, S);
                if (reach_all(S, 0) && reach_all(S, N)) {
                    bc_found = 1;
                    bc_N = N;
                    bc_G = GL[gi];
                    memcpy(bc_S, S, sizeof(int) * (size_t)d);
                    return 1;
                }
            }
        }
    }
    return 0;
}

static void bc_phase(int nlo, int nmax, double until) {
    double total = until - now();
    double slice = total / 20.0;
    if (slice < 0.3) slice = 0.3;
    if (slice > 2.0) slice = 2.0;
    for (int N = nlo; N <= nmax && now() < until; N++) {
        double u = now() + slice;
        if (u > until) u = until;
        bc_search_n(N, u);
    }
}

static void bc_to_graph(Graph *g) {
    int n = bc_N;
    set_group(bc_G);
    build_mt();
    g->n = 2 * n;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= n; }
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, n + MT[x * n + bc_S[i]]);
}

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph with p vertices per side (sum of d permutation
 * matrices), retried until connected. M[i][j] = number of darts i -> j. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
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
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

/* A voltage in 0..N-1 not used by another dart on the same base pair; -1 if none. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    int g0 = rndint(N);
    for (int k = 0; k < N; k++) {
        int g = (g0 + k) % N, clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
    return -1;
}

/* Hill-climb over voltages of a random base graph over group G. On success g is a valid lift. */
static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    set_group(*G);
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                int v = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                if (v < 0) return 0;
                dt[nd].i = i; dt[nd].j = j; dt[nd].g = v;
                nd++;
            }
    build_lift(g, p, N, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        int v = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        if (v < 0) return 0;
        dt[t].g = v;
        build_lift(g, p, N, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    build_lift(g, p, N, dt, nd);
    return 1;
}

/* Random group of order N, nonabelian with probability about 0.7. */
static int random_group_for(int N, Grp *G) {
    enum_groups(N);
    if (GTOT == 0) return 0;
    int idx;
    if (GNAB > 0 && rndint(10) < 7) idx = rndint(GNAB);
    else idx = rndint(GTOT);
    *G = GL[idx];
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (goal_n > target && rndint(2) == 0) target = goal_n;
        if (target > moore) return;
        long base_N = (target + 2 * p - 1) / (2 * p);
        long jitter = 2 + base_N / 16;
        long N = base_N + rndint((int)jitter);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group_for((int)N, &G)) continue;
        int steps = 200 + (int)(400000 / (2L * p * N));
        if (lift_try(&cand, p, (int)N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ grow by two */

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

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal] [nlo] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    goal_n = argc > 5 ? atol(argv[5]) : 0;
    long nlo_arg = argc > 6 ? atol(argv[6]) : 0;

    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);

    long moore = moore_bound();
    if (D >= 2 && d >= 2 && best.n < moore) {
        long nmax = moore / 2;
        if (nmax > MAXG - 1) nmax = MAXG - 1;
        long nlo = nlo_arg;
        if (nlo < d + 1) nlo = d + 1;
        if (nlo < best.n / 2 + 1) nlo = best.n / 2 + 1;
        if (nlo <= nmax) bc_phase((int)nlo, (int)nmax, t0 + (t_end - t0) * 0.5);
        if (bc_found) {
            static Graph bcg;
            bc_to_graph(&bcg);
            if (bcg.n > best.n && is_valid(&bcg)) copy_graph(&best, &bcg);
        }
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Known record orders, passed to the C engine as a search goal.
RECORD_GOAL = {(3, 9): 506}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    nlo = max(d + 1, best[0] // 2 + 1, int(0.4 * moore) // 2)
    goal = RECORD_GOAL.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), goal, nlo],
                         stdin_graph=start, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
