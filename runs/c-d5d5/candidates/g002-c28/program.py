"""Combined program: orbit-reduced group lifts (layered annealing), voltage lifts,
prune-and-refill, and grow-by-two, all in one C engine that starts from K_{d,d}
(or a Python-built start graph when one exists).

Phases inside C:
  1. orbit_search: layered group lifts Z_m x| Z_k, annealed on unreached pairs from
     2k representatives (left-multiplication is an automorphism, so this is exact).
  2. lift_search: random base-graph voltage lifts with hill-climbing.
  3. prune_search: anneal a slightly larger lift, prune worst vertices, refill, 2-switch.
  4. orbit_search again from the improved graph.
  5. grow_search: insert one vertex per side and anneal edge swaps.
Every accepted graph is checked by a full bitset diameter test before replacing the best.
"""
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
#define MAXP 4

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

static void remove_vertex(Graph *g, int v) {
    while (g->deg[v] > 0) {
        int u = g->adj[v][0];
        del_edge(g, v, u);
    }
    int last = g->n - 1;
    if (v != last) {
        for (int i = 0; i < g->deg[last]; i++) {
            int u = g->adj[last][i];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == last) { g->adj[u][j] = v; break; }
        }
        g->deg[v] = g->deg[last];
        g->side[v] = g->side[last];
        memcpy(g->adj[v], g->adj[last], sizeof(int) * g->deg[last]);
    }
    g->deg[last] = 0;
    g->n--;
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

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

/* ------------------------------------------------------------------ voltage lifts */

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

static int random_darts(int p, int N, Dart *dt) {
    int M[MAXP][MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    return nd;
}

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    Dart dt[MAXD * MAXP];
    int nd = random_darts(p, N, dt);
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    return 1;
}

static long lift_anneal(Graph *g, int p, int N, const Grp *G, int steps) {
    Dart dt[MAXD * MAXP];
    int nd = random_darts(p, N, dt);
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad_pairs(g);
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
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ prune and refill */

static void fill_pass(Graph *g) {
    static int LA[MAXN], LB[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] >= d) continue;
        if (g->side[v] == 0) LA[na++] = v; else LB[nb++] = v;
    }
    for (int i = na - 1; i > 0; i--) { int j = rndint(i + 1); int t = LA[i]; LA[i] = LA[j]; LA[j] = t; }
    for (int i = nb - 1; i > 0; i--) { int j = rndint(i + 1); int t = LB[i]; LB[i] = LB[j]; LB[j] = t; }
    for (int i = 0; i < na; i++) {
        int a = LA[i];
        for (int j = 0; j < nb && g->deg[a] < d; j++) {
            int b = LB[j];
            if (g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
        }
    }
}

static void switch_move(Graph *g, long *bad, double T) {
    int n = g->n;
    int v = rndint(n);
    if (g->deg[v] == 0) return;
    int u = g->adj[v][rndint(g->deg[v])];
    int s = rndint(n);
    if (s == v || g->side[s] != g->side[v] || g->deg[s] == 0) return;
    int t = g->adj[s][rndint(g->deg[s])];
    if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) return;
    del_edge(g, v, u);
    del_edge(g, s, t);
    add_edge(g, v, t);
    add_edge(g, s, u);
    long nb = bad_pairs(g);
    if (nb <= *bad || rnd01() < exp((double)(*bad - nb) / T)) {
        *bad = nb;
    } else {
        del_edge(g, v, t);
        del_edge(g, s, u);
        add_edge(g, v, u);
        add_edge(g, s, t);
    }
}

static int worst_on(const Graph *g, int side) {
    if (rnd01() < 0.2) {
        for (int tries = 0; tries < 1000; tries++) {
            int v = rndint(g->n);
            if (g->side[v] == side) return v;
        }
    }
    int best = -1;
    long bv = -1;
    int ties = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->side[v] != side) continue;
        if ((long)badv[v] > bv) { bv = badv[v]; best = v; ties = 1; }
        else if ((long)badv[v] == bv) { ties++; if (rndint(ties) == 0) best = v; }
    }
    return best;
}

static void prune_round(const Graph *start, Graph *best, double until) {
    static Graph w;
    copy_graph(&w, start);
    long bad = bad_pairs(&w);
    while (bad > 0 && now() < until && w.n - 2 > best->n) {
        fill_pass(&w);
        bad = bad_pairs(&w);
        if (bad == 0) break;
        for (int it = 0; it < 300 && bad > 0; it++) switch_move(&w, &bad, 0.6);
        if (bad == 0) break;
        bad = bad_pairs(&w);
        int a = worst_on(&w, 0), b = worst_on(&w, 1);
        if (a < 0 || b < 0 || a == b) break;
        int hi = a > b ? a : b, lo = a > b ? b : a;
        remove_vertex(&w, hi);
        remove_vertex(&w, lo);
        bad = bad_pairs(&w);
    }
    fill_pass(&w);
    bad = bad_pairs(&w);
    if (bad == 0 && w.n > best->n && is_valid(&w)) copy_graph(best, &w);
}

static void prune_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    if (best->n == 0) return;
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 9 ? 3 : 4;
        int extra = 2 * (2 + rndint(6));
        long target = (long)best->n + extra;
        int N = (int)((target + 2 * p - 1) / (2 * p));
        if (N < d) N = d;
        if (2L * p * N > (long)best->n + 40 || 2 * p * N > MAXN || 2L * p * N > 2 * moore) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 300 + 200000 / (2 * p * N);
        lift_anneal(&cand, p, N, &G, steps);
        prune_round(&cand, best, until);
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

/* ------------------------------------------------------------------ orbit-reduced layered lifts */

/* Vertices A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, group Z_m x| Z_k2.
 * d layers, each a permutation pi_l of the k base indices; dart (i, pi_l(i), s)
 * joins A_{i,g} to B_{pi_l(i), g*s}. Every vertex has degree exactly d. Left
 * multiplication is an automorphism, transitive on each side, so a BFS from the
 * 2k base representatives decides the diameter exactly. */

#define OMAXG 1024
#define OMAXK 4
#define OMAXT (MAXD * OMAXK)
#define OMAXN 2048
#define BIGC 1000000000L

static int OGM[OMAXG * OMAXG];
static int OGO = 0;
static int ODI[OMAXT], ODJ[OMAXT], ODS[OMAXT];
static int OADJ[OMAXN * MAXD];
static int OCNT[OMAXN];
static int OVIS[OMAXN];
static int OQ[OMAXN];
static int OSTAMP = 0;
static const int OKCH[6] = {1, 1, 2, 2, 3, 4};

static void ogroup_build(int m, int k2, int r) {
    int G = m * k2;
    long pw[16];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (pw[b - 1] * r) % m;
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e2 = y % k2;
            long aa = (a + pw[b] * c) % m;
            OGM[x * G + y] = (int)aa * k2 + (b + e2) % k2;
        }
    }
    OGO = G;
}

static void ogroup_choose(int G) {
    int cand[12], nc = 0;
    for (int k2 = 1; k2 <= 12; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    int k2 = cand[rndint(nc)];
    int m = G / k2;
    int r = 1;
    if (k2 > 1 && m > 1) {
        for (int t = 0; t < 200; t++) {
            int c = 1 + rndint(m - 1);
            if (gcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    ogroup_build(m, k2, r);
}

static void odarts_random(int k, int d_) {
    int perm[OMAXK];
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            ODI[t] = i;
            ODJ[t] = perm[i];
            int s = rndint(OGO);
            for (int tries = 0; tries < 200; tries++) {
                int clash = 0;
                for (int u = 0; u < t; u++)
                    if (ODI[u] == i && ODJ[u] == perm[i] && ODS[u] == s) { clash = 1; break; }
                if (!clash) break;
                s = rndint(OGO);
            }
            ODS[t] = s;
        }
    }
}

static long orbit_eval(int k, int d_, int D_) {
    int G = OGO, N = 2 * k * G, T = k * d_;
    for (int a = 0; a < T; a++)
        for (int b = a + 1; b < T; b++)
            if (ODI[a] == ODI[b] && ODJ[a] == ODJ[b] && ODS[a] == ODS[b]) return BIGC;
    for (int v = 0; v < N; v++) OCNT[v] = 0;
    for (int t = 0; t < T; t++) {
        int i = ODI[t], j = ODJ[t], s = ODS[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + OGM[g * G + s];
            if (OCNT[a] >= d_ || OCNT[b] >= d_) return BIGC;
            OADJ[a * MAXD + OCNT[a]++] = b;
            OADJ[b * MAXD + OCNT[b]++] = a;
        }
    }
    for (int v = 0; v < N; v++) if (OCNT[v] != d_) return BIGC;

    long total = 0;
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        OSTAMP++;
        if (OSTAMP == 0x7fffffff) { memset(OVIS, 0, sizeof(OVIS)); OSTAMP = 1; }
        int head = 0, tail = 0;
        OQ[tail++] = src;
        OVIS[src] = OSTAMP;
        for (int lev = 0; lev < D_ && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                int u = OQ[head];
                for (int c = 0; c < d_; c++) {
                    int v = OADJ[u * MAXD + c];
                    if (OVIS[v] != OSTAMP) { OVIS[v] = OSTAMP; OQ[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long orbit_anneal(int k, int d_, int D_, long iters, double until) {
    int G = OGO, T = k * d_;
    long cur = orbit_eval(k, d_, D_);
    double temp0 = 0.5 * G + 1.0;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        double frac = (double)it / (double)iters;
        double temp = temp0 * (1.0 - frac) + 0.3;
        if (rndint(2) == 0) {
            int t = rndint(T);
            int old = ODS[t];
            int ns = rndint(G);
            if (ns == old) continue;
            ODS[t] = ns;
            long c2 = orbit_eval(k, d_, D_);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else ODS[t] = old;
        } else {
            int l = rndint(d_);
            int i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int t1 = l * k + i1, t2 = l * k + i2;
            int tmp = ODJ[t1]; ODJ[t1] = ODJ[t2]; ODJ[t2] = tmp;
            long c2 = orbit_eval(k, d_, D_);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else { tmp = ODJ[t1]; ODJ[t1] = ODJ[t2]; ODJ[t2] = tmp; }
        }
    }
    return cur;
}

static void orbit_to_graph(Graph *g, int k, int d_) {
    int G = OGO, T = k * d_, N = 2 * k * G;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= k * G; }
    for (int t = 0; t < T; t++)
        for (int x = 0; x < G; x++)
            add_edge(g, ODI[t] * G + x, (k + ODJ[t]) * G + OGM[x * G + ODS[t]]);
}

static void orbit_search(Graph *best, double until) {
    static Graph cand;
    int step = 8, fails = 0;
    while (now() < until) {
        int k = OKCH[rndint(6)];
        long nmin = (long)best->n + step;
        long gmin = (nmin + 2L * k - 1) / (2L * k);
        if (gmin < 2) gmin = 2;
        long G = gmin + rndint((int)(1 + gmin / 12));
        long gcap = OMAXN / (2L * k);
        if (gcap > OMAXG) gcap = OMAXG;
        if (G > gcap) G = gcap;
        if (G < 2 || 2L * k * G <= best->n) {
            if (++fails >= 8) {
                fails = 0;
                step = step / 2;
                if (step < 2) step = 2;
            }
            continue;
        }
        ogroup_choose((int)G);
        odarts_random(k, d);
        long c = orbit_anneal(k, d, D, 20000, until);
        if (c == 0) {
            orbit_to_graph(&cand, k, d);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
            fails = 0;
            step *= 2;
            int cap = 16 + best->n / 8;
            if (step > cap) step = cap;
        } else if (++fails >= 4) {
            fails = 0;
            step /= 2;
            if (step < 2) step = 2;
        }
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

    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    double span = t_end - t0;
    if (best.n < moore_bound()) {
        orbit_search(&best, t0 + span * 0.55);
        if (best.n > 0) lift_search(&best, t0 + span * 0.65);
        if (best.n > 0) prune_search(&best, t0 + span * 0.80);
        if (best.n > 0) orbit_search(&best, t0 + span * 0.90);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
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
    if D <= 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # Moore graph already; just exercise the engine briefly
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 6)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass   # keep the valid fallback
    return best
