"""Combined program: Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez,
or K_{d,d}) and checks it with lib.is_valid. Then two C stages run:

1. GROUP LIFTS (new family): Haar-type voltage lifts over many finite groups of order 12..128,
   including non-metacyclic ones (Q8, A4, S4, SL(2,3), GL(2,3), Heisenberg mod 3, direct
   products). The lift is a bipartite graph with 2p fibres of size N, with edges
   A(i,x) ~ B(j, g*x). Right multiplication is an automorphism, so the diameter test needs
   BFS from only the 2p fibre identities. Hill-climb over voltages finds a diameter-D lift
   with more than the current best vertex count.
2. PARENT SEARCH: orbit-reduced voltage lifts, then grow-by-two annealing from the best graph.

Every stage is validated in C and again in Python with lib.is_valid. The best valid graph
seen so far is always returned, so the fallback is never worse than the algebraic start.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit            < start_graph      (parent mode)
 *          prog d D seed time_limit groups floor < group_stream    (group-lift mode)
 * Parent stdin: "n m" then m lines "u v", or "0 0" for none.
 * Group stdin: a dummy header "0 m", then the integers
 *   K, then for each group: N and N*N multiplication entries (identity must be element 0).
 * stdout: "n m" then m lines "u v": the largest valid graph found.
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
#define MAXG 200
#define MAXGN 128

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
static int badsave[MAXN];

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D.
 * Also fills badv[v] = number of vertices at distance > D from v. */
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

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
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

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
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

/* Orbit-reduced diameter objective for a regular-fibre lift.
 * The group acts by left multiplication on every fibre, so the distance between (a, x) and
 * (b, y) equals the distance between (a, e) and (b, x^-1 y). Hence it is enough to BFS from the
 * 2p representatives b*N (element 0 of each fibre). Returns the number of (representative,
 * vertex) pairs at distance > D, which is zero exactly when the lift has diameter <= D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Hill-climb the voltages of one random base multigraph over the group G. */
static int lift_fast_try(Graph *g, int p, int N, const Grp *G, int steps, double until) {
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
    long bad = orbit_bad(g, p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad == 0;
}

/* Search lifts of size 2pN strictly larger than the current best. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int Nmin = (int)((target + 2 * p - 1) / (2 * p));
        int N = Nmin + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2 * p * N > MAXN) continue;
        if (!random_group(N, &G)) continue;
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_fast_try(&cand, p, N, &G, 20000, until) && is_valid(&cand) &&
                cand.n > best->n) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* Bad-pair roulette: a uniformly random vertex lying in some bad pair (per the most recent
 * badv[] values). Returns -1 if there is none. */
static int pick_bad_vertex(const Graph *g) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list[c++] = v;
    if (c == 0) return -1;
    return list[rndint(c)];
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
    long bad = bad_pairs(work);  /* badv[] now describes the current state */
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
        /* Save the per-vertex bad counts of the current state, so a rejected swap can
         * restore them without another all-pairs computation. */
        memcpy(badsave, badv, sizeof(int) * (size_t)work->n);
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
            memcpy(badv, badsave, sizeof(int) * (size_t)work->n);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

/* Each failed attempt lengthens the next slice (x1.5, capped at x4); a success resets it. */
static void grow_search(Graph *best, double until) {
    static Graph work;
    double boost = 1.0;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        slice *= boost;
        if (slice > left) slice = left;
        if (grow_once(best, &work, now() + slice)) {
            copy_graph(best, &work);
            boost = 1.0;
        } else if (boost < 4.0) {
            boost *= 1.5;
        }
    }
}

/* ---------------- group lifts ----------------
 * Lift over a finite group G (order N, identity element 0): fibre elements A(i,x), B(j,y),
 * darts (i,j,g) give edges A(i,x) ~ B(j, g*x). Right multiplication by k is an automorphism,
 * so the diameter test needs BFS only from the 2p fibre identities (orbit_bad). */
static unsigned char GM[MAXG][MAXGN][MAXGN];
static int GN[MAXG];
static int NG = 0;

static int read_groups(void) {
    int K;
    NG = 0;
    if (scanf("%d", &K) != 1) return 0;
    for (int k = 0; k < K; k++) {
        if (NG >= MAXG) break;
        int N;
        if (scanf("%d", &N) != 1) break;
        if (N < 1 || N > MAXGN) break;
        int ok = 1;
        for (int a = 0; a < N; a++)
            for (int b = 0; b < N; b++) {
                int v = 0;
                if (scanf("%d", &v) != 1) return NG;
                if (v < 0 || v >= N) { ok = 0; v = 0; }
                GM[NG][a][b] = (unsigned char)v;
            }
        for (int a = 0; a < N && ok; a++)
            if (GM[NG][0][a] != a || GM[NG][a][0] != a) ok = 0;
        for (int x = 0; x < N && ok; x++) {
            int found = 0;
            for (int y = 0; y < N; y++)
                if (GM[NG][x][y] == 0) { found = 1; break; }
            if (!found) ok = 0;
        }
        if (ok) { GN[NG] = N; NG++; }
    }
    return NG;
}

static void gbuild(Graph *g, int p, int N, int gi, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x,
                     p * N + dt[t].j * N + GM[gi][dt[t].g][x]);
}

static int gtry(Graph *g, int p, int gi, Dart *dt, int steps, double until) {
    int N = GN[gi];
    int M[MAXP][MAXP];
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
    gbuild(g, p, N, gi, dt, nd);
    long bad = orbit_bad(g, p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        gbuild(g, p, N, gi, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    gbuild(g, p, N, gi, dt, nd);
    return bad == 0;
}

/* Find group lifts with at least `want` vertices; each success raises the requirement. */
static void group_search(Graph *best, long want, double until) {
    static Graph cand;
    static Dart gdt[MAXD * MAXP];
    long moore = moore_bound();
    if (NG <= 0) return;
    while (now() < until) {
        int gi = rndint(NG);
        int N = GN[gi];
        int p = 1 + rndint(MAXP);
        long nv = 2L * p * N;
        if (nv < want || nv > moore || nv > MAXN || N < d) continue;
        if (gtry(&cand, p, gi, gdt, 4000, until) && cand.n >= want && is_valid(&cand)) {
            copy_graph(best, &cand);
            want = best->n + 2;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [groups floor] < input\n", argv[0]);
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

    if (argc >= 7 && strcmp(argv[5], "groups") == 0) {
        long floor_n = atol(argv[6]);
        int dummy = 0, mm = 0;
        if (scanf("%d %d", &dummy, &mm) != 2) mm = 0;
        (void)dummy;
        (void)mm;
        if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }
        complete_bipartite(&best);
        read_groups();
        if (D >= 2 && NG > 0) group_search(&best, floor_n + 2, t_end);
        if (!is_valid(&best)) complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }

    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        fast_lift_search(&best, t0 + (t_end - t0) * 0.6);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
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


# ------------------------------------------------------------ finite group library

def _table_from(elems, op):
    """Multiplication table (order, T) with the identity relabelled to index 0."""
    e = next(x for x in elems if all(op(x, y) == y for y in elems))
    order = [e] + [x for x in elems if x != e]
    idx = {x: i for i, x in enumerate(order)}
    table = [[idx[op(x, y)] for y in order] for x in order]
    return len(order), table


def _pmul(p, q):
    return tuple(p[i] for i in q)


def _even(p):
    inv = sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j])
    return inv % 2 == 0


def _qmul(p, q):
    a1, b1, c1, d1 = p
    a2, b2, c2, d2 = q
    return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
            a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
            a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)


def _heis(x, y):
    a, b, c = x
    a2, b2, c2 = y
    return ((a + a2) % 3, (b + b2) % 3, (c + c2 + a * b2) % 3)


def _mmul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % 3, (a * f + b * h) % 3,
            (c * e + d * g) % 3, (c * f + d * h) % 3)


def _det3(M):
    a, b, c, d = M
    return (a * d - b * c) % 3


def _factor_library():
    """Small groups as (order, table): cyclic, dihedral, elementary abelian, nonabelian
    named groups, and semidirect products Z_m x| Z_k."""
    F = []
    for n in range(2, 65):
        F.append(_table_from(list(range(n)), lambda x, y, n=n: (x + y) % n))
    for n in range(3, 41):
        def dop(x, y, n=n):
            r1, s1 = x
            r2, s2 = y
            return ((r1 + (r2 if s1 == 0 else -r2)) % n, (s1 + s2) % 2)
        F.append(_table_from([(r, s) for r in range(n) for s in (0, 1)], dop))
    for k in (2, 3, 4, 5):
        F.append(_table_from(list(itertools.product(range(2), repeat=k)),
                             lambda x, y: tuple((a + b) % 2 for a, b in zip(x, y))))
    F.append(_table_from(list(itertools.product(range(3), repeat=2)),
                         lambda x, y: tuple((a + b) % 3 for a, b in zip(x, y))))
    F.append(_table_from(list(itertools.product(range(3), repeat=3)), _heis))
    base = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    F.append(_table_from([tuple(s * x for x in u) for u in base for s in (1, -1)], _qmul))
    perms = list(itertools.permutations(range(4)))
    F.append(_table_from(perms, _pmul))
    F.append(_table_from([p for p in perms if _even(p)], _pmul))
    mats = list(itertools.product(range(3), repeat=4))
    F.append(_table_from([M for M in mats if _det3(M) == 1], _mmul))
    F.append(_table_from([M for M in mats if _det3(M) != 0], _mmul))
    for m in range(2, 14):
        for k in range(2, 9):
            if not 6 <= m * k <= 64:
                continue
            for r in range(1, m):
                try:
                    order, mul, _ = lib.semidirect_group(m, k, r)
                except ValueError:
                    continue
                F.append(_table_from(list(range(order)), mul))
    return F


def _product(A, B):
    """Direct product of two tables; element (g, h) is coded as g * |H| + h."""
    n1, T1 = A
    n2, T2 = B
    N = n1 * n2
    T = [[0] * N for _ in range(N)]
    for a in range(N):
        g1, h1 = divmod(a, n2)
        row = T[a]
        for b in range(N):
            g2, h2 = divmod(b, n2)
            row[b] = T1[g1][g2] * n2 + T2[h1][h2]
    return N, T


def _group_pool(seed, lo=12, hi=128, limit=90):
    rng = random.Random(seed * 7919 + 13)
    lib_groups = _factor_library()
    singles = [g for g in lib_groups if lo <= g[0] <= hi]
    rng.shuffle(singles)
    pool = singles[:40]
    tries = 0
    while len(pool) < limit and tries < 4000:
        tries += 1
        A = rng.choice(lib_groups)
        B = rng.choice(lib_groups)
        if lo <= A[0] * B[0] <= hi:
            pool.append(_product(A, B))
    rng.shuffle(pool)
    return pool[:limit]


def _group_stream(seed):
    """Encode the group pool as an lib.run_c stdin graph. The C side reads the first two
    integers as a dummy header and then the flat integer stream."""
    pool = _group_pool(seed)
    flat = [len(pool)]
    for n, T in pool:
        flat.append(n)
        for row in T:
            flat.extend(row)
    if len(flat) % 2:
        flat.append(0)
    return 0, [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def remaining():
        return 0.9 * time_limit - (time.monotonic() - t0) - 1.5

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    # Stage A: group-lift search (new construction family).
    if D >= 2 and d >= 3 and remaining() > 3.0:
        try:
            stream = _group_stream(seed)
            budget_a = 0.45 * remaining()
            text = lib.run_c(C_SOURCE, [d, D, seed, budget_a, "groups", best[0]],
                             stdin_graph=stream, timeout=budget_a + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass

    # Stage B: parent search (voltage lifts plus grow-by-two annealing) from the best graph.
    budget_b = remaining()
    if budget_b > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget_b],
                             stdin_graph=best, timeout=budget_b + 4)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
