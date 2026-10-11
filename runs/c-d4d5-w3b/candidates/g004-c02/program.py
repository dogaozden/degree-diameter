"""Group-lift search with explicit non-cyclic groups, then the semidirect lift and growth engine.

Bold change in this version: the construction family is new. Python builds many small
non-metacyclic groups as permutation groups (direct products of dihedral, symmetric,
alternating, SL(2,q), GL(2,3), Heisenberg and affine groups). It passes each group's
multiplication table to C, which hill-climbs voltage lifts with P+P base vertices over that
group, for P = 1..4. Orbit-reduced diameter checks run from the fibre representatives only.
A valid lift beats the current best only if it has more vertices. After the group phase,
the old semidirect lift search and the grow-by-two / ruin-regrow engine refine the best graph.
Every stage is validated in C and again with lib.is_valid. The fallback is always a valid
graph.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage: prog d D seed time_limit [mode] [group args] < start_graph
 *   mode "auto" (default): semidirect fast-lift search, then grow from the start graph.
 *   mode "grow": grow from the start graph only.
 *   mode "group" N P t_1 ... t_{N*N}: hill-climb voltage lifts with P+P base vertices over
 *        the group with multiplication table t (x*y at index x*N+y). Stdin is ignored.
 * stdout: "n m" then m lines "u v" for the best valid graph ("0 0" if none in group mode).
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
#define MAXGRP 128
#define TABU_RING 64
#define TABU_LEN 40

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static const int *GT = NULL;
static int GTN = 0;

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

/* ---- tabu ring: recently removed pairs may not be re-added for TABU_LEN iterations ---- */
static long tabu_key[TABU_RING];
static long tabu_exp[TABU_RING];
static int tabu_pos;

static void tabu_reset(void) {
    for (int i = 0; i < TABU_RING; i++) { tabu_key[i] = -1; tabu_exp[i] = 0; }
    tabu_pos = 0;
}

static long pair_key(int a, int b) {
    int lo = a < b ? a : b, hi = a < b ? b : a;
    return (long)lo * MAXN + hi;
}

static int tabu_active(int a, int b, long it) {
    long k = pair_key(a, b);
    for (int i = 0; i < TABU_RING; i++)
        if (tabu_key[i] == k && tabu_exp[i] > it) return 1;
    return 0;
}

static void tabu_push(int a, int b, long it) {
    tabu_key[tabu_pos] = pair_key(a, b);
    tabu_exp[tabu_pos] = it + TABU_LEN;
    tabu_pos = (tabu_pos + 1) % TABU_RING;
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (bitsets). Fills badv[v]. */
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

/* Random d-regular connected bipartite base multigraph on p + p vertices. */
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

/* Product x*y in the group: the table if one is loaded, else the semidirect rule. */
static int mulv(const Grp *G, int x, int y) {
    if (GT) return GT[x * GTN + y];
    return gmul(G, x, y);
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) joins A(i,x) to B(j, x*g). */
static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + mulv(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective. Left multiplication by any group element is an
 * automorphism of the lift, so it is enough to BFS from one vertex per fibre. Returns the
 * number of (source, vertex) pairs at distance > D; zero iff the lift has diameter <= D. */
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

/* Hill-climb the voltages of one random base multigraph over the group. */
static int lift_fast_try(Graph *g, int p, int N, const Grp *G, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
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

/* Semidirect-group lifts strictly larger than the current best. */
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

/* A random vertex that lies in some bad pair, per the latest badv[]. -1 if none. */
static int pick_bad_vertex(const Graph *g) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list[c++] = v;
    if (c == 0) return -1;
    return list[rndint(c)];
}

/* Degree-preserving swap annealing with a tabu ring. */
static int anneal(Graph *work, double until) {
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    tabu_reset();
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
        if (tabu_active(v, t, it) || tabu_active(s, u, it)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            tabu_push(v, u, it);
            tabu_push(s, t, it);
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

/* Grow by two: one new vertex per side, joined to each other, with d-1 stolen edges each. */
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

/* Ruin and regrow: delete a BFS ball, then add K0+1 side-0 and K1+1 side-1 vertices. */
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

    long need = s0;
    long guard = 0;
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

/* Alternate grow-by-two and ruin-and-regrow from the current frontier. */
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

/* Hill-climb voltage lifts over the loaded group GT until one is valid. */
static int group_search(Graph *out, int p, double until) {
    while (now() < until) {
        if (lift_fast_try(out, p, GTN, NULL, 20000, until) && is_valid(out)) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [mode] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    const char *mode = argc > 5 ? argv[5] : "auto";
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }

    if (strcmp(mode, "group") == 0) {
        int N = argc > 6 ? atoi(argv[6]) : 0;
        int P = argc > 7 ? atoi(argv[7]) : 0;
        if (N < 2 || N > MAXGRP || N <= d || P < 1 || P > MAXP || argc != 8 + N * N ||
            2 * P * N > MAXN || 2L * P * N > moore_bound()) {
            printf("0 0\n");
            return 0;
        }
        static int tab[MAXGRP * MAXGRP];
        for (int i = 0; i < N * N; i++) {
            tab[i] = atoi(argv[8 + i]);
            if (tab[i] < 0 || tab[i] >= N) { printf("0 0\n"); return 0; }
        }
        GT = tab;
        GTN = N;
        if (group_search(&best, P, t_end)) print_graph(&best);
        else printf("0 0\n");
        return 0;
    }

    read_start(&best);
    if (strcmp(mode, "grow") == 0) {
        if (best.n > 0 && best.n < moore_bound()) grow_search(&best, t_end);
    } else {
        if (D >= 2 && best.n > 0 && best.n < moore_bound()) {
            fast_lift_search(&best, t0 + (t_end - t0) * 0.6);
            if (best.n > 0) grow_search(&best, t_end);
        }
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


# ------------------------------------------------------------ permutation groups

def _comp(a, b):
    """Apply a, then b (associative, so the closure is a group)."""
    return tuple(b[i] for i in a)


def _closure(gens, cap):
    """All elements generated by gens (identity first), or None if there are more than cap."""
    k = len(gens[0])
    ident = tuple(range(k))
    elems = [ident]
    seen = {ident}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = _comp(x, g)
            if y not in seen:
                if len(elems) >= cap:
                    return None
                seen.add(y)
                elems.append(y)
    return elems


def _mat_perms(mats, p, dim):
    """Permutations of the nonzero vectors of F_p^dim induced by the matrices."""
    vecs = [v for v in itertools.product(range(p), repeat=dim) if any(v)]
    idx = {v: i for i, v in enumerate(vecs)}
    out = []
    for M in mats:
        perm = []
        for v in vecs:
            w = tuple(sum(M[i][j] * v[j] for j in range(dim)) % p for i in range(dim))
            perm.append(idx[w])
        out.append(tuple(perm))
    return out


def _direct(g1, g2):
    """Generators of the direct product, acting on disjoint blocks of points."""
    k1 = len(g1[0])
    k2 = len(g2[0])
    out = [tuple(list(p) + list(range(k1, k1 + k2))) for p in g1]
    out += [tuple(list(range(k1)) + [k1 + x for x in p]) for p in g2]
    return out


def _affine(m, mults):
    """Permutations x -> x+1 and x -> a*x (mod m) for a in mults: a subgroup of AGL(1, m)."""
    gens = [tuple((i + 1) % m for i in range(m))]
    for a in mults:
        gens.append(tuple((a * i) % m for i in range(m)))
    return gens


def _factors():
    fs = []
    for n in range(2, 14):
        fs.append((f"Z{n}", [tuple((i + 1) % n for i in range(n))]))
    for n in range(3, 14):
        fs.append((f"D{n}", [tuple((i + 1) % n for i in range(n)),
                             tuple((-i) % n for i in range(n))]))

    def sym(n):
        t = list(range(n))
        t[0], t[1] = 1, 0
        return [tuple(t), tuple((i + 1) % n for i in range(n))]

    fs.append(("S4", sym(4)))
    fs.append(("S5", sym(5)))
    fs.append(("A4", [(1, 2, 0, 3), (0, 2, 3, 1)]))
    fs.append(("A5", [(1, 2, 0, 3, 4), (0, 1, 3, 4, 2)]))
    fs.append(("SL23", _mat_perms([[[1, 1], [0, 1]], [[0, 2], [1, 0]]], 3, 2)))
    fs.append(("GL23", _mat_perms([[[1, 1], [0, 1]], [[0, 2], [1, 0]], [[2, 0], [0, 1]]], 3, 2)))
    fs.append(("SL25", _mat_perms([[[1, 1], [0, 1]], [[0, 4], [1, 0]]], 5, 2)))
    fs.append(("He27", _mat_perms([[[1, 1, 0], [0, 1, 0], [0, 0, 1]],
                                   [[1, 0, 0], [0, 1, 1], [0, 0, 1]]], 3, 3)))
    for m in (5, 7, 8, 9, 11, 13):
        units = [a for a in range(2, m) if math.gcd(a, m) == 1]
        for a in units:
            fs.append((f"Aff{m}_{a}", _affine(m, [a])))
        fs.append((f"AGL{m}", _affine(m, units)))
    return fs


def _group_candidates(rng, lo, hi, max_products=400):
    """(names, generators, order) for single factors and direct products with order in [lo, hi]."""
    facs = []
    for name, gens in _factors():
        el = _closure(gens, 130)
        if el is not None and len(el) >= 2:
            facs.append((name, gens, len(el)))
    cands = [((name,), gens, N) for name, gens, N in facs if lo <= N <= hi]
    pairs = [(i, j) for i in range(len(facs)) for j in range(i, len(facs))
             if lo <= facs[i][2] * facs[j][2] <= hi]
    rng.shuffle(pairs)
    for i, j in pairs[:max_products]:
        ni, gi, Ni = facs[i]
        nj, gj, Nj = facs[j]
        cands.append(((ni, nj), _direct(gi, gj), Ni * Nj))
    return cands


def _table(gens, N):
    """Flat multiplication table (x*y at index x*N+y, identity at 0), or None if the order is not N."""
    elems = _closure(gens, N + 1)
    if elems is None or len(elems) != N:
        return None
    index = {x: i for i, x in enumerate(elems)}
    return [index[_comp(x, y)] for x in elems for y in elems]


# ---------------------------------------------------------------- C calls

def _c_run(args, stdin_graph, budget, d, D):
    """Run the C engine; return a validated (n, edges) or None."""
    text = lib.run_c(C_SOURCE, args, stdin_graph=stdin_graph, timeout=budget + 8.0)
    n, edges = lib.parse_graph_text(text)
    if n > 0 and lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def _group_phase(d, D, seed, best, end, rng, moore):
    """Voltage lifts over generic groups. Targets are the smallest sizes above the current best."""
    lo = max(d + 1, 2, (best[0] + 2) // 8)
    hi = min(130, moore // 2)
    if lo > hi:
        return best
    cands = _group_candidates(rng, lo, hi)
    tabs, dead, tries = {}, set(), {}
    errors = 0
    while errors < 3:
        budget = min(end - time.monotonic(), 5.0)
        if budget < 1.0:
            break
        n0 = best[0]
        live = []
        for ci, (_, _, N) in enumerate(cands):
            if ci in dead or N <= d:
                continue
            for p in (1, 2, 3, 4):
                size = 2 * p * N
                if n0 + 2 <= size <= moore:
                    live.append((size, tries.get((ci, p), 0), rng.random(), ci, p))
        if not live:
            break
        _, _, _, ci, p = min(live)
        tries[(ci, p)] = tries.get((ci, p), 0) + 1
        if ci not in tabs:
            tabs[ci] = _table(cands[ci][1], cands[ci][2])
            if tabs[ci] is None:
                dead.add(ci)
                continue
        N = cands[ci][2]
        try:
            got = _c_run([d, D, seed, f"{budget:.2f}", "group", N, p] + tabs[ci],
                         None, budget, d, D)
            errors = 0
        except Exception:
            got = None
            errors += 1
        if got is not None and got[0] > best[0]:
            best = got
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    span = 0.9 * time_limit - 2.0
    if span < 4.0:
        return best
    deadline = t0 + span
    rng = random.Random(seed * 1000003 + d * 1009 + D)

    try:
        best = _group_phase(d, D, seed, best, t0 + 0.55 * span, rng, moore)
    except Exception:
        pass

    for stage in ("auto", "grow"):
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        budget = 0.5 * remaining if stage == "auto" else remaining - 0.5
        try:
            got = _c_run([d, D, seed, f"{budget:.2f}", stage], best, budget, d, D)
        except Exception:
            got = None
        if got is not None and got[0] > best[0]:
            best = got

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
