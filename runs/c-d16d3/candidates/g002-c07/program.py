"""Starter program: Python builds the best known start graph, the C engine searches from it.

New in this version:
  * C routine try_add_side(): a new vertex on side s is valid (for D = 3) iff its neighbourhood
    T hits the neighbourhood of every existing vertex on side s and every member of T has spare
    degree. Finding such a T is a min-conflicts / annealing hitting-set search.
  * C routine lns(): large-neighbourhood search for D = 3. Delete 1-3 random vertices, then
    re-insert as many vertices as possible through try_add_side, keep the result if valid and not
    smaller (sideways moves allowed), and remember the largest valid graph.
  * Python twin_fill(): greedy twin cloning. A clone copies a vertex's neighbourhood, so distances
    and bipartiteness survive for every D. It is applied to the start graph and to the C output.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search:
 *   1. If there is no start graph: voltage lifts over semidirect products Z_m x| Z_k.
 *   2. D = 3: large-neighbourhood search. Ruin (delete 1-3 vertices) and recreate by adding
 *      vertices through try_add_side(). For D = 3 a new vertex on side s with neighbourhood T is
 *      valid whenever the old graph was valid and T hits N(x) for every x on side s.
 *   3. Other D: grow by two with annealed edge swaps.
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
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
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

/* ------------------------------------------------------------------ grow by two (general D) */

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

/* ------------------------------------------------------------------ transversal addition (D = 3)
 *
 * Let g be valid with D = 3. Add a new vertex v on side s with neighbourhood T (on side 1-s).
 * Every old vertex x on side s has distance <= 2 to v iff N(x) meets T. For a vertex b on the
 * other side that is not in T, some x in N(b) lies on side s, and x has a neighbour t in T,
 * so v-t-x-b has length 3. Hence the result is valid iff T is a transversal of {N(x)} and
 * every member of T still has spare degree.
 *
 * try_add_side() searches for such a T with |T| <= d by greedy start plus annealed swaps that
 * minimise the number of uncovered side-s vertices. On success it appends the vertex.
 */

static int cov[MAXN];
static unsigned char inT[MAXN];
static int candv[MAXN];
static int Tset[MAXD];

static int try_add_side(Graph *g, int s, int iters) {
    int n = g->n, nc = 0, ns = 0;
    if (n + 1 >= MAXN || n < 2) return 0;
    for (int v = 0; v < n; v++) {
        if (g->side[v] == s) { cov[v] = 0; ns++; }
        else if (g->deg[v] < d) candv[nc++] = v;
    }
    if (nc == 0 || ns == 0) return 0;
    int U = ns;
    int kk = d < nc ? d : nc;
    int took = 0;
    /* greedy: repeatedly take the candidate covering the most uncovered vertices */
    for (int k = 0; k < kk; k++) {
        int pick = -1, bestgain = -1, ties = 0;
        for (int c = 0; c < nc; c++) {
            int v = candv[c];
            if (inT[v]) continue;
            int gain = 0;
            for (int i = 0; i < g->deg[v]; i++)
                if (cov[g->adj[v][i]] == 0) gain++;
            if (gain > bestgain) { bestgain = gain; pick = v; ties = 1; }
            else if (gain == bestgain && rndint(++ties) == 0) pick = v;
        }
        if (pick < 0) break;
        inT[pick] = 1;
        Tset[took++] = pick;
        for (int i = 0; i < g->deg[pick]; i++)
            if (cov[g->adj[pick][i]]++ == 0) U--;
    }
    /* annealing on swaps: replace one T member by one outside candidate */
    for (int it = 0; U > 0 && it < iters && took > 0; it++) {
        double temp = 0.5 * (1.0 - (double)it / iters) + 0.03;
        int i = rndint(took);
        int t = Tset[i];
        int c = -1;
        for (int tries = 0; tries < 6 && c < 0; tries++) {
            int cc = candv[rndint(nc)];
            if (!inT[cc]) c = cc;
        }
        if (c < 0) continue;
        int oldU = U;
        for (int j = 0; j < g->deg[t]; j++)
            if (--cov[g->adj[t][j]] == 0) U++;
        for (int j = 0; j < g->deg[c]; j++)
            if (cov[g->adj[c][j]]++ == 0) U--;
        int delta = U - oldU;
        if (delta <= 0 || rnd01() < exp(-delta / temp)) {
            inT[t] = 0;
            inT[c] = 1;
            Tset[i] = c;
        } else {
            for (int j = 0; j < g->deg[c]; j++)
                if (--cov[g->adj[c][j]] == 0) U++;
            for (int j = 0; j < g->deg[t]; j++)
                if (cov[g->adj[t][j]]++ == 0) U--;
        }
    }
    int ok = (U == 0);
    if (ok) {
        int v = n;
        g->n = n + 1;
        g->side[v] = (unsigned char)s;
        g->deg[v] = 0;
        for (int k = 0; k < took; k++) {
            int t = Tset[k];
            g->adj[v][g->deg[v]++] = t;
            g->adj[t][g->deg[t]++] = v;
        }
    }
    for (int k = 0; k < took; k++) inT[Tset[k]] = 0;
    return ok;
}

/* Delete the vertices flagged in dead[], then renumber the rest compactly. */
static void remove_vertices(Graph *g, const unsigned char *dead) {
    static int map[MAXN];
    static Graph tmp;
    int m = 0;
    for (int v = 0; v < g->n; v++) map[v] = dead[v] ? -1 : m++;
    tmp.n = m;
    for (int v = 0; v < g->n; v++) {
        if (dead[v]) continue;
        int nv = map[v];
        tmp.side[nv] = g->side[v];
        tmp.deg[nv] = 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (!dead[u]) tmp.adj[nv][tmp.deg[nv]++] = map[u];
        }
    }
    copy_graph(g, &tmp);
}

/* Large-neighbourhood search for D = 3: ruin 1-3 vertices, recreate with transversal additions. */
static void lns(Graph *best, double until) {
    static Graph cur, cand;
    static unsigned char dead[MAXN];
    copy_graph(&cur, best);
    while (now() < until) {
        int n0 = cur.n;
        copy_graph(&cand, &cur);
        int k = 1 + rndint(3);
        memset(dead, 0, sizeof dead);
        for (int r = 0; r < k; r++) dead[rndint(n0)] = 1;
        remove_vertices(&cand, dead);
        int adds = 0, fails = 0;
        while (fails < 2 && adds < k + 4) {
            int s = rndint(2);
            if (try_add_side(&cand, s, 4000)) { adds++; fails = 0; }
            else if (try_add_side(&cand, 1 - s, 4000)) { adds++; fails = 0; }
            else fails++;
        }
        if (cand.n >= n0 && is_valid(&cand)) {
            copy_graph(&cur, &cand);
            if (cur.n > best->n) copy_graph(best, &cur);
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

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && !had_start && best.n < moore_bound())
        lift_search(&best, t0 + (t_end - t0) * (D == 3 ? 0.4 : 0.6));
    if (best.n == 0) complete_bipartite(&best);
    if (D == 3) {
        lns(&best, t_end);
    } else if (D >= 2 && best.n < moore_bound()) {
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


def conic_blowup(d, D):
    """Twin-blow-up of PG(2,q) with q = d-3 odd, using a conic and a dual conic.

    Each point of a conic S and each line of a dual conic T is duplicated once. Copies are
    twins of the originals, so the diameter stays 3. Gives 2(q^2+q+1) + 2(q+1) vertices,
    which is 394 for q = 13 (d = 16).
    """
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:            # u is a point (< m), v = m + line index
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def twin_fill(n, edges, d):
    """Greedy twin cloning: copy a vertex whose neighbours all have spare degree.

    A clone has the same neighbourhood as its original and lies on the same side. Its distances
    to every other vertex equal those of the original, so the diameter bound and bipartiteness
    both survive, for every D. Returns (n, edges) with as many clones as spare degrees allow.
    """
    adj = [list(a) for a in lib.adjacency(n, edges)]
    deg = [len(a) for a in adj]
    grew = True
    while grew:
        grew = False
        for v in range(len(adj)):
            while adj[v] and all(deg[u] < d for u in adj[v]):
                w = len(adj)
                adj.append(list(adj[v]))
                deg.append(len(adj[v]))
                for u in adj[v]:
                    adj[u].append(w)
                    deg[u] += 1
                grew = True
    out = [(u, w) for u in range(len(adj)) for w in adj[u] if u < w]
    return len(adj), out


def safe_fill(g, d, D):
    """twin_fill(g), kept only if it is strictly larger and valid. Otherwise returns g."""
    try:
        n2, e2 = twin_fill(g[0], g[1], d)
        if n2 > g[0] and lib.is_valid(n2, e2, d, D):
            return (n2, e2)
    except Exception:
        pass
    return g


def starts(d, D):
    """Candidate structured start graphs (each already built, validity checked later)."""
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = None
    for cand in starts(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (start is None or cand[0] > start[0]):
            start = cand
    if start is not None:
        start = safe_fill(start, d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid structured or K_{d,d} fallback
    fin = safe_fill(best, d, D)
    if lib.is_valid(*fin, d, D):
        return fin
    return best
