"""Starter program: Python builds the best known start graph, the C engine searches from it.

New in this version:
  * Python: "oval star" construction for D = 3. Take PG(2,q), pick an oval O (q+1 points,
    or q+2 for even q) and add one new vertex per oval point (joined to the q+1 lines through
    that point) and one new vertex per oval line (joined to the q+1 points on that line).
    Every old vertex gains at most 2 degrees, so the maximum degree is q+3. For d = 16 this
    gives q = 13 and 2(q^2+q+1) + 2(q+1) = 394 vertices.
  * C: spare-degree greedy growth. New vertices pick neighbours that have spare degree and
    maximise newly covered distance-(D-1) balls (bitset coverage). Deletion-based filling is
    used only if spare degree is not enough. A spare-add move joins two spare vertices during
    annealing.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid starting graph (degrees may be below d),
 *          or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search:
 *   1. Voltage lifts over semidirect products Z_m x| Z_k (short time when a start is given).
 *   2. Grow by two: new vertices x (side 0) and y (side 1) join x-y, then take neighbours
 *      with spare degree by greedy ball coverage. If that leaves the pair too far apart,
 *      degree-neutral deletions fill the rest. Annealing repairs the remaining bad pairs
 *      with degree-preserving swaps and spare-degree additions.
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
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
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
static uint64_t BUFX[MAXN * MAXW], BUFY[MAXN * MAXW];
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
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

/* Radius-r balls: row v of the result has bit w set iff dist(v, w) <= r.
 * Returns BUFX or BUFY; the result is overwritten by the next call. */
static uint64_t *balls_r(const Graph *g, int r) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = BUFX, *nxt = BUFY;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int k = 0; k < r; k++) {
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
    return cur;
}

/* ------------------------------------------------------------------ input / output */

/* Read "n m" + edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Pick a uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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

typedef struct { int i, j, g; } Dart; /* base A-vertex i -> base B-vertex j, voltage g */

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

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
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

/* ------------------------------------------------------------------ growth pieces */

/* Greedy spare-degree attachment for the new pair x (side 0) and y (side 1), already joined.
 * x picks side-1 neighbours with spare degree, each maximising newly covered vertices within
 * D-1 steps. Then y picks side-0 neighbours the same way, using the covered set of x. */
static void spare_fill(Graph *work, int x, int y) {
    int n = work->n, W = (n + 63) / 64;
    static uint64_t cov[MAXW];
    int r = D - 1;

    uint64_t *B = balls_r(work, r);
    memcpy(cov, B + (size_t)y * W, sizeof(uint64_t) * W);
    while (work->deg[x] < d) {
        int best = -1, bestscore = 0;
        for (int b = 0; b < n; b++) {
            if (work->side[b] != 1 || b == y || work->deg[b] >= d || has_edge(work, x, b)) continue;
            int s = 0;
            const uint64_t *row = B + (size_t)b * W;
            for (int w = 0; w < W; w++) s += __builtin_popcountll(row[w] & ~cov[w]);
            if (s > bestscore || (s == bestscore && s > 0 && rndint(2))) { bestscore = s; best = b; }
        }
        if (best < 0 || bestscore <= 0) break;
        add_edge(work, x, best);
        const uint64_t *row = B + (size_t)best * W;
        for (int w = 0; w < W; w++) cov[w] |= row[w];
    }

    B = balls_r(work, r);
    memcpy(cov, B + (size_t)x * W, sizeof(uint64_t) * W);
    while (work->deg[y] < d) {
        int best = -1, bestscore = 0;
        for (int a = 0; a < n; a++) {
            if (work->side[a] != 0 || a == x || work->deg[a] >= d || has_edge(work, y, a)) continue;
            int s = 0;
            const uint64_t *row = B + (size_t)a * W;
            for (int w = 0; w < W; w++) s += __builtin_popcountll(row[w] & ~cov[w]);
            if (s > bestscore || (s == bestscore && s > 0 && rndint(2))) { bestscore = s; best = a; }
        }
        if (best < 0 || bestscore <= 0) break;
        add_edge(work, y, best);
        const uint64_t *row = B + (size_t)best * W;
        for (int w = 0; w < W; w++) cov[w] |= row[w];
    }
}

/* Degree-neutral filling for the rest of x and y: each step deletes an old edge a-b,
 * then joins x-b and y-a. Old vertices keep their degrees. */
static void deletion_fill(Graph *work, int x, int y) {
    static int used[MAXN];
    static int stamp = 0;
    int n0 = work->n - 2;
    stamp++;
    used[x] = used[y] = stamp;
    for (int i = 0; i < work->deg[x]; i++) used[work->adj[x][i]] = stamp;
    for (int i = 0; i < work->deg[y]; i++) used[work->adj[y][i]] = stamp;
    int need = d - work->deg[x];
    if (d - work->deg[y] < need) need = d - work->deg[y];
    for (int k = 0, tries = 0; k < need && tries < 100000; tries++) {
        int a = rndint(n0);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (b >= n0 || used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

/* Anneal until bad == 0 or time runs out. Moves: degree-preserving swap around a bad vertex,
 * or (with spare degree) an edge added between two vertices on opposite sides. */
static int anneal(Graph *work, long bad, double until) {
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);

        if (rnd01() < 0.3 && work->deg[v] < d) {
            int w = -1;
            for (int tries = 0; tries < 30; tries++) {
                int c = rndint(work->n);
                if (c != v && work->side[c] != work->side[v] && work->deg[c] < d &&
                    !has_edge(work, v, c)) { w = c; break; }
            }
            if (w < 0) continue;
            add_edge(work, v, w);
            long nb = bad_pairs(work);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else del_edge(work, v, w);
        } else {
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
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return 1;
}

/* Insert one new vertex per side into a copy of best and repair. Returns 1 if the result
 * is valid with best->n + 2 vertices. */
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

    spare_fill(work, x, y);
    long bad = bad_pairs(work);
    if (bad > 0) {
        deletion_fill(work, x, y);
        bad = bad_pairs(work);
    }
    if (!anneal(work, bad, until)) return 0;
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

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        double lift_share = had_start ? 0.03 : 0.6;
        lift_search(&best, t0 + (t_end - t0) * lift_share);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _largest_prime_power_at_most(x):
    """Largest prime power q with 3 <= q <= x, or None."""
    for v in range(x, 2, -1):
        if lib.is_prime_power(v):
            return v
    return None


def _oval_star_graph(q):
    """Oval-star construction for D = 3, max degree q+3 (order 2(q^2+q+1) + 2|O|).

    Start from the PG(2,q) incidence graph (points 0..m-1 on side A, lines m..2m-1 on side B).
    Let O be an oval (conic (1,t,t^2) plus (0,0,1), plus the nucleus (0,1,0) when q is even):
    |O| = q+1 (q odd) or q+2 (q even), and it is an arc, so each line holds at most 2 points of O
    and each point lies on at most 2 lines of O.
      * For each point P in O, add a new side-A vertex joined to the q+1 lines through P.
      * For each line L in O, add a new side-B vertex joined to the q+1 points on L.
    Every old vertex gains at most 2 degrees. Diameter is 3, because any two points share a
    line, and any new vertex reaches every old vertex within 3 steps.
    """
    F = lib.GF(q)
    pts = lib.projective_points(q)
    m = len(pts)
    n0, base = lib.projective_plane_incidence(q)
    oval = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if q % 2 == 0:
        oval.append((0, 1, 0))

    def dot(u, v):
        return F.add(F.add(F.mul(u[0], v[0]), F.mul(u[1], v[1])), F.mul(u[2], v[2]))

    edges = list(base)
    nxt = n0
    for P in oval:                      # new side-A vertices (point stars)
        x = nxt
        nxt += 1
        for j, L in enumerate(pts):
            if dot(P, L) == 0:
                edges.append((x, m + j))
    for L in oval:                      # new side-B vertices (line stars)
        y = nxt
        nxt += 1
        for i, P in enumerate(pts):
            if dot(P, L) == 0:
                edges.append((i, y))
    return nxt, edges


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def _start_candidates(d, D):
    """Known constructions for (d, D) that Python can build directly."""
    out = []
    if D != 3:
        return out
    if lib.is_prime_power(d - 1):
        out.append(_try(lib.projective_plane_incidence, d - 1))  # Moore graph: optimal
    q = _largest_prime_power_at_most(d - 3)
    if q is not None:
        out.append(_try(_oval_star_graph, q))                    # degree q+3 <= d
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(_try(lib.araujo_lopez_graph, d - 2))          # record graphs of order 2(q^2+q+5)
    return [c for c in out if c is not None]


def known_start(d, D):
    """Largest valid known construction for (d, D), or None."""
    best = None
    for cand in _start_candidates(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (best is None or cand[0] > best[0]):
            best = cand
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    start = known_start(d, D)
    if start is not None and start[0] > best[0]:
        best = start
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=best, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
