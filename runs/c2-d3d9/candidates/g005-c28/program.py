"""Bipartite degree-diameter search, version 2.

Starting point: the parent's C engine (Cayley-group search and voltage lifts) runs first,
so every case still gets its algebraic result. The new stage is a different search family:
simulated annealing over unstructured d-regular bipartite graphs. It grows the best graph
by inserting one vertex per side, then repairs diameter with edge switches. Each switch
preserves degrees and bipartiteness, and the cost is the number of vertex pairs farther
than D apart. Bad pairs are biased toward vertices that currently have them.

The Python side is unchanged in spirit: known constructions are used when they exist,
every output is checked with lib.is_valid, and the best valid graph is returned.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, version 2.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases (each only runs if the previous one did not improve):
 *   1. Bipartite Cayley graphs over metacyclic groups (sweep N downward from the Moore limit).
 *   2. Voltage lifts over Z_m x| Z_k (hill-climb on voltages).
 *   3. Simulated-annealing growth: insert two vertices (one per side) using a matching of
 *      d edges, then anneal edge switches that keep every degree and bipartiteness, until
 *      the diameter is at most D. Bad pairs are tracked per vertex and biased on.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXP 4
#define CAY_MAX 1000

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
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
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
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

/* ------------------------------------------------------------------ bipartite Cayley graphs */

static int *cmul = NULL;
static int *cinv = NULL;
static int cN = 0;
static int cS[MAXD], cSinv[MAXD];
static int cdist[2 * CAY_MAX], cq[2 * CAY_MAX];
static Graph cand_g;

static int build_group(int m, int k, int r) {
    int N = m * k;
    int *rp = malloc(sizeof(int) * (size_t)k);
    cmul = realloc(cmul, sizeof(int) * (size_t)N * N);
    cinv = realloc(cinv, sizeof(int) * (size_t)N);
    if (!rp || !cmul || !cinv) { free(rp); return 0; }
    for (int b = 0; b < k; b++) rp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            cmul[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (cmul[x * N + y] == 0) { cinv[x] = y; break; }
    cN = N;
    free(rp);
    return 1;
}

static int random_set(int N) {
    cS[0] = 0;
    int c = 1;
    for (int tries = 0; c < d; tries++) {
        if (tries > 100000) return 0;
        int x = 1 + rndint(N - 1), dup = 0;
        for (int i = 0; i < c; i++)
            if (cS[i] == x) { dup = 1; break; }
        if (!dup) cS[c++] = x;
    }
    for (int i = 0; i < d; i++) cSinv[i] = cinv[cS[i]];
    return 1;
}

static int cayley_ok(int N) {
    int V = 2 * N;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) cdist[v] = -1;
        int head = 0, tail = 0;
        cdist[s0] = 0;
        cq[tail++] = s0;
        while (head < tail) {
            int v = cq[head++];
            if (cdist[v] >= D) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + cmul[v * N + cS[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = cmul[y * N + cSinv[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void cayley_phase(Graph *best, double until) {
    long moore = moore_bound();
    long Nmax = moore / 2;
    if (Nmax > CAY_MAX) Nmax = CAY_MAX;
    long Nmin = best->n / 2 + 1;
    if (Nmin < d) Nmin = d;
    if (Nmin < 2) Nmin = 2;
    static int gm[1024], gk[1024], gr[1024];
    for (int N = (int)Nmax; N >= (int)Nmin; N--) {
        if (now() > until) break;
        int G = 0;
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) {
                if (G < 1024) { gm[G] = 1; gk[G] = k; gr[G] = 0; G++; }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
                if (G < 1024) { gm[G] = m; gk[G] = k; gr[G] = r; G++; }
            }
        }
        if (G == 0) continue;
        int found = 0;
        for (int batch = 0; batch < 15 && !found; batch++) {
            if (now() > until) break;
            int gi = rndint(G);
            if (!build_group(gm[gi], gk[gi], gr[gi])) return;
            for (int t = 0; t < 200 && !found; t++)
                if (random_set(N) && cayley_ok(N)) found = 1;
        }
        if (found) {
            cand_g.n = 2 * N;
            for (int v = 0; v < cand_g.n; v++) { cand_g.deg[v] = 0; cand_g.side[v] = v >= N; }
            for (int x = 0; x < N; x++)
                for (int i = 0; i < d; i++) add_edge(&cand_g, x, N + cmul[x * N + cS[i]]);
            if (is_valid(&cand_g) && cand_g.n > best->n) *best = cand_g;
            return;
        }
    }
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
    return bad == 0;
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
            *best = cand;
    }
}

/* ------------------------------------------------------------------ simulated annealing growth */

static int cur_bad[MAXN]; /* per-vertex bad counts of the current (accepted) state */

/* Anneal edge switches on g until bad_pairs == 0 (returns iterations) or time runs out (-1).
 * A switch takes a1-b1, a2-b2 to a1-b2, a2-b1. It keeps all degrees and bipartiteness.
 * The first edge is chosen at a vertex that is far from something (70% of the time). */
static long anneal(Graph *g, double until) {
    long bad = bad_pairs(g);
    memcpy(cur_bad, badv, sizeof(int) * (size_t)g->n);
    long it = 0;
    const double Tmax = 2.0, Tmin = 0.05;
    const long L = 6000;
    while (bad > 0) {
        it++;
        if ((it & 7) == 0 && now() > until) return -1;
        double T = Tmax * pow(Tmin / Tmax, (double)(it % L) / (double)L);
        int n = g->n;
        int v = rndint(n);
        if (rnd01() < 0.7)
            for (int t = 0; t < 40; t++) {
                int w = rndint(n);
                if (cur_bad[w] > 0) { v = w; break; }
            }
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int a1 = g->side[v] == 0 ? v : u;
        int b1 = g->side[v] == 0 ? u : v;
        int a2 = rndint(n);
        if (g->side[a2] != 0 || g->deg[a2] == 0) continue;
        int b2 = g->adj[a2][rndint(g->deg[a2])];
        if (a1 == a2 || b1 == b2 || has_edge(g, a1, b2) || has_edge(g, a2, b1)) continue;
        del_edge(g, a1, b1);
        del_edge(g, a2, b2);
        add_edge(g, a1, b2);
        add_edge(g, a2, b1);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) {
            bad = nb;
            memcpy(cur_bad, badv, sizeof(int) * (size_t)n);
        } else {
            del_edge(g, a1, b2);
            del_edge(g, a2, b1);
            add_edge(g, a1, b1);
            add_edge(g, a2, b2);
        }
    }
    return it;
}

/* Insert vertices x (side A) and y (side B). Remove a matching of d edges a_i-b_i, then add
 * x-b_i and y-a_i. Every degree stays the same, and x and y reach degree d. */
static int grow_once(const Graph *best, Graph *work) {
    static int mark[MAXN];
    static int stamp = 0;
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    *work = *best;
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    stamp++;
    int ea[MAXD], eb[MAXD], k = 0;
    for (int tries = 0; k < d && tries < 20000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || work->deg[a] == 0 || mark[a] == stamp) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (mark[b] == stamp) continue;
        mark[a] = mark[b] = stamp;
        ea[k] = a; eb[k] = b; k++;
    }
    if (k < d) return 0;
    for (int i = 0; i < k; i++) {
        del_edge(work, ea[i], eb[i]);
        add_edge(work, x, eb[i]);
        add_edge(work, y, ea[i]);
    }
    return 1;
}

static void sa_grow(Graph *best, double until) {
    static Graph work;
    double slice = 0.3;
    int fails = 0;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        if (!grow_once(best, &work)) {
            if (++fails > 500) break;
            continue;
        }
        double left = until - now();
        double s = slice < left ? slice : left;
        if (s <= 0) break;
        long r = anneal(&work, now() + s);
        if (r >= 0 && is_valid(&work)) {
            *best = work;
            slice = 0.3;
            fails = 0;
        } else {
            slice *= 1.3;
            if (slice > 30.0) slice = 30.0;
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

    if (D < 1) { printf("1 0\n"); return 0; }
    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        long before = best.n;
        double span = t_end - t0;
        if (d >= 2) cayley_phase(&best, t0 + span * 0.25);
        if (best.n == before) lift_search(&best, t0 + span * 0.40);
        if (best.n < moore_bound()) sa_grow(&best, t_end);
    }

    if (!is_valid(&best)) {
        /* single edge: valid for D >= 1 */
        best.n = 2;
        best.deg[0] = best.deg[1] = 0;
        best.side[0] = 0;
        best.side[1] = 1;
        add_edge(&best, 0, 1);
    }
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
    start = None
    try:
        start = known_start(d, D)
    except (ValueError, StopIteration):
        start = None

    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
        if not lib.is_valid(best[0], best[1], d, D):
            best = (1, [])

    # Leave room for compiling the C source on the first run.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
