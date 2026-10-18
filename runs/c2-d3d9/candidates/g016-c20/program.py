"""Combined search: bi-Cayley graphs over nonabelian metacyclic groups (scanned upward
from the record region), then voltage lifts as a fallback, then grow-by-two with
annealing and tabu repair. Python builds the best known start graph and keeps the best
valid result. Every output is checked with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start graph), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases:
 *  1. Bi-Cayley graphs over Z_m x|_r Z_k of order N. Vertices A_x, B_x; A_x ~ B_{xs}, s in S.
 *     Left multiplication is transitive on each side, so two BFS runs (from A_e and B_e)
 *     decide the diameter. N is scanned upward. Connection sets are enumerated exhaustively
 *     when there are few of them, and sampled otherwise. Nonabelian groups come first.
 *  2. Voltage lifts over the same groups (hill-climb on voltages), if phase 1 added nothing.
 *  3. Grow by two: insert one vertex per side, then repair bad pairs with annealing
 *     followed by tabu search.
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
#define CAY_MAX 1000
#define MAXGRP 4096
#define CAY_LIM 40000
#define TABU_LEN 32
#define TABU_K 12
#define TABU_STALL 400

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

/* Number of unordered pairs at distance > D. Also fills badv[v]. */
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

/* Full validity check: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups;

static void push_grp(int m, int k, int r) {
    if (ngroups < MAXGRP) {
        groups[ngroups].m = m;
        groups[ngroups].k = k;
        groups[ngroups].r = r;
        ngroups++;
    }
}

/* All groups of order n: nonabelian (r != 1) first, then abelian. */
static void enum_groups(int n) {
    ngroups = 0;
    for (int pass = 0; pass < 2; pass++)
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1) push_grp(1, k, 0);
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) == nonab) push_grp(m, k, r);
            }
        }
}

static int MT[CAY_MAX * CAY_MAX]; /* MT[x*NN + y] = x*y in the current group */
static int INV[CAY_MAX];
static int NN;

static void build_group(Grp G) {
    int n = G.m * G.k;
    static int rp[CAY_MAX];
    NN = n;
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

static double binom(int a, int b) {
    if (b < 0 || b > a) return 0;
    double r = 1;
    for (int i = 0; i < b; i++) r = r * (a - i) / (i + 1);
    return r;
}

/* Advance a strictly increasing k-combination of values in [1, maxv]. */
static int next_comb(int *c, int k, int maxv) {
    int i = k - 1;
    while (i >= 0 && c[i] == maxv - (k - 1 - i)) i--;
    if (i < 0) return 0;
    c[i]++;
    for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
    return 1;
}

static void pick_random(int n, int *S) {
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

/* ------------------------------------------------------------------ bi-Cayley check */

static int dist_[2 * CAY_MAX], queue_[2 * CAY_MAX];

/* 1 iff every vertex is within D of src. A_x = x, B_h = NN + h, A_x ~ B_{x s}. */
static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
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

static Graph cay_cand;

/* Build the explicit bi-Cayley graph for the current group and set S, and keep it if valid and larger. */
static void make_cand(int n, const int *S, Graph *best) {
    cay_cand.n = 2 * n;
    for (int v = 0; v < cay_cand.n; v++) { cay_cand.deg[v] = 0; cay_cand.side[v] = v >= n; }
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++) add_edge(&cay_cand, x, n + MT[x * n + S[i]]);
    if (cay_cand.n > best->n && is_valid(&cay_cand)) copy_graph(best, &cay_cand);
}

/* Look for a good connection set for order n (over all groups, up to until). */
static int search_n(int n, double until, Graph *best) {
    enum_groups(n);
    int k = d - 1;
    if (n - 1 < k || ngroups == 0) return 0;
    int exhaustive = binom(n - 1, k) <= CAY_LIM;
    int S[MAXD], c[MAXD];
    for (int gi = 0; gi < ngroups; gi++) {
        if (now() > until) return 0;
        build_group(groups[gi]);
        int found = 0;
        if (exhaustive) {
            for (int i = 0; i < k; i++) c[i] = i + 1;
            long it = 0;
            do {
                S[0] = 0;
                for (int i = 0; i < k; i++) S[i + 1] = c[i];
                if (reach_all(S, 0) && reach_all(S, n)) { found = 1; break; }
                if ((++it & 1023) == 0 && now() > until) break;
            } while (next_comb(c, k, n - 1));
        } else {
            for (long t = 0; t < CAY_LIM; t++) {
                if ((t & 1023) == 0 && now() > until) break;
                pick_random(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) { found = 1; break; }
            }
        }
        if (found) {
            make_cand(n, S, best);
            return 1;
        }
    }
    return 0;
}

static void cayley_phase(Graph *best, double until) {
    long moore = moore_bound();
    long nmax = moore / 2;
    if (nmax > CAY_MAX - 1) nmax = CAY_MAX - 1;
    long nlo = best->n / 2 + 1;
    long floor_n = (long)(0.45 * (double)moore) / 2;
    if (nlo < floor_n) nlo = floor_n;
    if (nlo < d + 1) nlo = d + 1;
    double total = until - now();
    double slice = total / 20.0;
    if (slice < 0.3) slice = 0.3;
    if (slice > 3.0) slice = 3.0;
    for (long n = nlo; n <= nmax && now() < until; n++) {
        double ul = now() + slice;
        if (ul > until) ul = until;
        search_n((int)n, ul, best);
    }
}

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart; /* base A_i -> base B_j with voltage g */

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + MT[x * NN + dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int lift_try(Graph *g, int p, int N, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    return bad == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph lift_cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || N > CAY_MAX - 1 || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        enum_groups(N);
        if (ngroups == 0) continue;
        build_group(groups[rndint(ngroups)]);
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&lift_cand, p, N, steps) && lift_cand.n > best->n && is_valid(&lift_cand))
            copy_graph(best, &lift_cand);
    }
}

/* ------------------------------------------------------------------ tabu repair */

static int tabu_a[TABU_LEN], tabu_b[TABU_LEN];
static int tabu_cnt = 0, tabu_pos = 0;

static void push_tabu(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    tabu_a[tabu_pos] = a;
    tabu_b[tabu_pos] = b;
    tabu_pos = (tabu_pos + 1) % TABU_LEN;
    if (tabu_cnt < TABU_LEN) tabu_cnt++;
}

static int is_tabu(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    for (int i = 0; i < tabu_cnt; i++)
        if (tabu_a[i] == a && tabu_b[i] == b) return 1;
    return 0;
}

/* Random degree-preserving double-edge swap. */
static int rand_swap(Graph *g) {
    for (int tries = 0; tries < 100; tries++) {
        int v = rndint(g->n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int s = rndint(g->n);
        if (g->side[s] != g->side[v] || s == v || g->deg[s] == 0) continue;
        int t = g->adj[s][rndint(g->deg[s])];
        if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) continue;
        del_edge(g, v, u);
        del_edge(g, s, t);
        add_edge(g, v, t);
        add_edge(g, s, u);
        return 1;
    }
    return 0;
}

static int tabu_repair(Graph *work, double until) {
    long bad = bad_pairs(work);
    long best_bad = bad, stall = 0;
    tabu_cnt = 0;
    tabu_pos = 0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int v = -1;
        for (int tries = 0; tries < 50; tries++) {
            int c = rndint(work->n);
            if (badv[c] > 0 && work->deg[c] > 0) { v = c; break; }
        }
        if (v < 0) {
            v = rndint(work->n);
            if (work->deg[v] == 0) continue;
        }
        int u = work->adj[v][rndint(work->deg[v])];
        long nb_best = -1;
        int bs = -1, bt = -1;
        for (int k = 0; k < TABU_K; k++) {
            int s = rndint(work->n);
            if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
            int t = work->adj[s][rndint(work->deg[s])];
            if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
            del_edge(work, v, u);
            del_edge(work, s, t);
            add_edge(work, v, t);
            add_edge(work, s, u);
            long nb = bad_pairs(work);
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
            if ((is_tabu(v, t) || is_tabu(s, u)) && nb >= best_bad) continue;
            if (nb_best < 0 || nb < nb_best) { nb_best = nb; bs = s; bt = t; }
        }
        if (nb_best >= 0) {
            del_edge(work, v, u);
            del_edge(work, bs, bt);
            add_edge(work, v, bt);
            add_edge(work, bs, u);
            push_tabu(v, u);
            push_tabu(bs, bt);
        }
        bad = bad_pairs(work);
        if (bad < best_bad) {
            best_bad = bad;
            stall = 0;
        } else if (++stall > TABU_STALL) {
            for (int p = 0; p < 3; p++) rand_swap(work);
            tabu_cnt = 0;
            bad = bad_pairs(work);
            best_bad = bad;
            stall = 0;
        }
    }
    return is_valid(work);
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
    double t_sa = now() + 0.5 * (until - now());
    long bad = bad_pairs(work);
    double T = 1.0;
    while (bad > 0 && now() < t_sa) {
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
    if (bad > 0 && !tabu_repair(work, until)) return 0;
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
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD || d == 1 || D == 1) {
        printf("2 1\n0 1\n");   /* K_{1,1}: optimal whenever d >= 1 and D == 1, or d == 1 */
        return 0;
    }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double T = t_end - t0;
        long before = best.n;
        cayley_phase(&best, t0 + 0.6 * T);
        if (best.n == before) lift_search(&best, t0 + 0.75 * T);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 or d == 1:
        return (2, [(0, 1)])   # K_{1,1} is optimal here
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if best[0] >= lib.moore_bound(d, D) or d > 32:
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
