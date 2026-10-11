"""Bi-Cayley / voltage-lift search with a fallback chain (Python builds the start, C searches).

New construction for the weakest case (d=4, D=5). The parent searched random metacyclic
groups with voltage hill-climbing. This version treats the graph as a lift over a small base
with p fibres per side and a metacyclic group Z_m x| Z_k of order N. It uses fast implicit BFS
(no graph is built during search) and an annealing search over the voltages of d*p darts.
Each candidate is scored by the number of vertex pairs farther than D apart, using BFS from
the 2p fibre identities only (the group acts by left multiplication, so this is exact).
Validity is checked in C and again in Python before any graph is returned. The start is the
best algebraic graph, so every case still returns a valid graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
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
#define MAXP 3
#define MAXG 160
#define MAXGRP 2048

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

/* Number of unordered pairs at distance > D; fills badv[v]. */
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

/* ---- Groups Z_m x| Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k) ---- */
typedef struct { int m, k, r; } GrpP;
static GrpP GL[MAXGRP];
static int nGL;
static int MT[MAXG][MAXG];
static int INV[MAXG];

static int list_groups(int N) {
    nGL = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (nGL < MAXGRP) { GL[nGL].m = 1; GL[nGL].k = k; GL[nGL].r = 0; nGL++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (nGL < MAXGRP) { GL[nGL].m = m; GL[nGL].k = k; GL[nGL].r = r; nGL++; }
        }
    }
    return nGL;
}

static void build_group(const GrpP *G, int N) {
    int rp[MAXG];
    int m = G->m, k = G->k;
    for (int b = 0; b < k; b++)
        rp[b] = (b == 0) ? (1 % m) : (int)((long)rp[b - 1] * G->r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

/* ---- Lifts with p fibres per side, d darts per fibre. Dart t joins A(di,x) to B(dj,x*dg). ---- */
static int fa_g[MAXP][MAXD], fa_j[MAXP][MAXD];
static int fb_g[MAXP][MAXD], fb_i[MAXP][MAXD];
static int bfs_dist[2 * MAXP * MAXG];
static int bfs_q[2 * MAXP * MAXG];

/* Sum over the 2p fibre identities of the number of vertices farther than D (0 iff valid). */
static long bc_eval(int p, int N, const int *di, const int *dj, const int *dg, int nd) {
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        int i = di[t], j = dj[t], g = dg[t];
        fa_g[i][ca[i]] = g;
        fa_j[i][ca[i]] = j;
        ca[i]++;
        fb_g[j][cb[j]] = INV[g];
        fb_i[j][cb[j]] = i;
        cb[j]++;
    }
    int V = 2 * p * N, PN = p * N;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < V; v++) bfs_dist[v] = -1;
        int head = 0, tail = 0;
        bfs_dist[src] = 0;
        bfs_q[tail++] = src;
        while (head < tail) {
            int v = bfs_q[head++];
            int dv = bfs_dist[v];
            if (dv >= D) continue;
            if (v < PN) {
                int i = v / N, x = v % N;
                for (int k = 0; k < d; k++) {
                    int u = (p + fa_j[i][k]) * N + MT[x][fa_g[i][k]];
                    if (bfs_dist[u] < 0) { bfs_dist[u] = dv + 1; bfs_q[tail++] = u; }
                }
            } else {
                int w = v - PN, j = w / N, y = w % N;
                for (int k = 0; k < d; k++) {
                    int u = fb_i[j][k] * N + MT[y][fb_g[j][k]];
                    if (bfs_dist[u] < 0) { bfs_dist[u] = dv + 1; bfs_q[tail++] = u; }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static void make_base(int p, int M[MAXP][MAXP]) {
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
}

/* Lay out darts from the base multigraph with random voltages, distinct within each (i,j). */
static int init_darts(int p, int N, int M[MAXP][MAXP], int *di, int *dj, int *dg) {
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                if (nd >= MAXP * MAXD) return 0;
                di[nd] = i; dj[nd] = j; dg[nd] = -1; nd++;
            }
    for (int t = 0; t < nd; t++) {
        int ok = 0;
        for (int tries = 0; tries < 1000 && !ok; tries++) {
            int g = rndint(N), clash = 0;
            for (int t2 = 0; t2 < t; t2++)
                if (di[t2] == di[t] && dj[t2] == dj[t] && dg[t2] == g) { clash = 1; break; }
            if (!clash) { dg[t] = g; ok = 1; }
        }
        if (!ok) return 0;
    }
    return nd;
}

/* Anneal voltages until bad == 0 or time runs out. Returns 1 on success. */
static int sa_run(int p, int N, const int *di, const int *dj, int *dg, int nd,
                  long steps, double until) {
    long cur = bc_eval(p, N, di, dj, dg, nd);
    for (long s = 0; s < steps; s++) {
        if (cur == 0) return 1;
        if ((s & 511) == 0 && now() > until) return 0;
        double T = 0.05 + 2.0 * (1.0 - (double)s / (double)steps);
        int t = rndint(nd);
        int ng = -1;
        for (int tries = 0; tries < 50; tries++) {
            int g = rndint(N), ok = 1;
            for (int t2 = 0; t2 < nd; t2++)
                if (t2 != t && di[t2] == di[t] && dj[t2] == dj[t] && dg[t2] == g) { ok = 0; break; }
            if (ok) { ng = g; break; }
        }
        if (ng < 0 || ng == dg[t]) continue;
        int old = dg[t];
        dg[t] = ng;
        long nb = bc_eval(p, N, di, dj, dg, nd);
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
        else dg[t] = old;
    }
    return cur == 0;
}

static void build_bc(Graph *g, int p, int N, int nd, const int *di, const int *dj, const int *dg) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, (p + dj[t]) * N + MT[x][dg[t]]);
}

/* Repeatedly try lifts of order just above the current best. */
static void bc_search(Graph *best, double until) {
    static Graph cand;
    static int di[MAXP * MAXD], dj[MAXP * MAXD], dg[MAXP * MAXD];
    long moore = moore_bound();
    while (now() < until) {
        if (best->n + 2 > moore) break;
        int p = 1 + rndint(3);
        int N = best->n / (2 * p) + 1;
        if (rndint(3) == 0) N += rndint(3);
        if (N < d) N = d;
        if (N > MAXG || 2L * p * N > moore || 2L * p * N > MAXN) {
            if (p == 1 && N > MAXG) break;
            continue;
        }
        if (list_groups(N) <= 0) continue;
        int gi = rndint(nGL);
        build_group(&GL[gi], N);
        int M[MAXP][MAXP];
        make_base(p, M);
        int nd = init_darts(p, N, M, di, dj, dg);
        if (nd != p * d) continue;
        double lim = now() + 2.0;
        if (lim > until) lim = until;
        if (sa_run(p, N, di, dj, dg, nd, 150000, lim)) {
            build_bc(&cand, p, N, nd, di, dj, dg);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---- Local swap annealing on a full graph (used by the growth stage) ---- */
static int pick_bad_vertex(const Graph *g) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list[c++] = v;
    if (c == 0) return -1;
    return list[rndint(c)];
}

static int anneal(Graph *work, double until) {
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v;
        if (rnd01() < 0.8) {
            v = pick_bad_vertex(work);
            if (v < 0) v = rndint(work->n);
        } else {
            v = rndint(work->n);
        }
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
            bad_pairs(work);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
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
    return anneal(work, until);
}

static int ruin_regrow(const Graph *cur, Graph *out, double until) {
    int n = cur->n;
    if (n < 4 || n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    static int rem[MAXN], map[MAXN], seen[MAXN], q[MAXN];
    int K0 = 1 + rndint(3), K1 = 1 + rndint(3);
    memset(rem, 0, sizeof(int) * n);
    memset(seen, 0, sizeof(int) * n);
    int root = rndint(n);
    int head = 0, tail = 0, c0 = 0, c1 = 0;
    q[tail++] = root;
    seen[root] = 1;
    while (head < tail && (c0 < K0 || c1 < K1)) {
        int v = q[head++];
        if (cur->side[v] == 0 && c0 < K0) { rem[v] = 1; c0++; }
        else if (cur->side[v] == 1 && c1 < K1) { rem[v] = 1; c1++; }
        for (int i = 0; i < cur->deg[v]; i++) {
            int u = cur->adj[v][i];
            if (!seen[u]) { seen[u] = 1; q[tail++] = u; }
        }
    }
    if (c0 < K0 || c1 < K1) return 0;

    int N = 0;
    for (int v = 0; v < n; v++)
        if (!rem[v]) map[v] = N++;
    int total = N + (K0 + 1) + (K1 + 1);
    if (total != n + 2 || total > MAXN) return 0;
    out->n = total;
    for (int v = 0; v < total; v++) { out->deg[v] = 0; out->side[v] = 0; }
    for (int v = 0; v < n; v++)
        if (!rem[v]) out->side[map[v]] = cur->side[v];
    int id = N;
    for (int k = 0; k < K0 + 1; k++) out->side[id++] = 0;
    for (int k = 0; k < K1 + 1; k++) out->side[id++] = 1;

    for (int v = 0; v < n; v++) {
        if (rem[v]) continue;
        for (int i = 0; i < cur->deg[v]; i++) {
            int u = cur->adj[v][i];
            if (rem[u] || u < v) continue;
            add_edge(out, map[v], map[u]);
        }
    }

    long s0 = 0, s1 = 0;
    for (int v = 0; v < total; v++) {
        int def = d - out->deg[v];
        if (def < 0) return 0;
        if (out->side[v] == 0) s0 += def;
        else s1 += def;
    }
    if (s0 != s1) return 0;

    long need = s0, guard = 0;
    while (need > 0) {
        if (++guard > 2000000L) return 0;
        int a = rndint(total);
        if (out->side[a] != 0 || out->deg[a] >= d) continue;
        int b = rndint(total);
        if (out->side[b] != 1 || out->deg[b] >= d) continue;
        if (has_edge(out, a, b)) continue;
        add_edge(out, a, b);
        need--;
    }
    return anneal(out, until);
}

static void grow_search(Graph *best, double until) {
    static Graph cur, work;
    copy_graph(&cur, best);
    while (now() < until && cur.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        int first_ruin = rnd01() < 0.5;
        int ok = 0;
        for (int a = 0; a < 2 && !ok && now() < until; a++) {
            int use_ruin = (a == 0) ? first_ruin : !first_ruin;
            double dl = now() + slice;
            if (dl > until) dl = until;
            if (use_ruin) ok = ruin_regrow(&cur, &work, dl);
            else ok = grow_once(&cur, &work, dl);
        }
        if (ok) {
            copy_graph(&cur, &work);
            if (cur.n > best->n) copy_graph(best, &cur);
        }
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n < moore_bound()) {
        bc_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
