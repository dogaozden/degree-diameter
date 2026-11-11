"""Lift search for the d=3, D=9 target: voltage lifts over metacyclic groups with simulated
annealing, plus a Cayley sweep and the old fallback chain. Python builds the start and the fallback."""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, lift-annealing version.
 *
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" then m lines "u v" (a valid start), or "0 0".
 * stdout: "n m" then m lines "u v": the best valid graph found.
 *
 * Model: a base multigraph with p vertices per side, d darts per base vertex, and
 * voltages in a metacyclic group G = Z_m x|_r Z_k of order N. The lift has 2pN vertices:
 * A-vertex (i,x) joins B-vertex (j, x*g) for each dart (i, j, g). Left multiplication by G
 * is an automorphism acting regularly on each fibre, so the diameter is decided by one BFS
 * from (s, e) for each base vertex s. Simulated annealing minimises the number of
 * unreached (source, vertex) pairs over voltages and base rewirings.
 *
 * Phases:
 *   A. Cayley sweep (p = 1): N downward from the Moore limit, random groups and sets.
 *   B. Annealed lifts with p = 1..4 and N chosen so the lift order exceeds the best found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096
#define MAXD 16
#define MAXP 4
#define MAXND (MAXD * MAXP)
#define MAXGRP 4096

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
} Graph;

static int d, D;
static double t_end;
static Graph best;
static int best_n = 0;
static Graph LG;   /* current voltage lift */
static Graph tmpg; /* scratch for candidates */

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

/* ------------------------------------------------------------------ groups */

/* Multiplication table of Z_m x|_r Z_k, element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int *MT = NULL;
static long MTcap = 0;
static int gl_m[MAXGRP], gl_r[MAXGRP];

static int build_group(int m, int k, int r) {
    int N = m * k;
    if ((long)N * N > MTcap) {
        int *t = realloc(MT, sizeof(int) * (size_t)N * N);
        if (!t) return 0;
        MT = t;
        MTcap = (long)N * N;
    }
    int *rp = malloc(sizeof(int) * (size_t)k);
    if (!rp) return 0;
    for (int b = 0; b < k; b++) rp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    free(rp);
    return 1;
}

/* Lists all (m, r) for groups of order N into gl_m / gl_r; returns the count. */
static int enum_groups(int N) {
    int c = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (c < MAXGRP) { gl_m[c] = 1; gl_r[c] = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
            if (c < MAXGRP) { gl_m[c] = m; gl_r[c] = r; c++; }
        }
    }
    return c;
}

/* ------------------------------------------------------------------ lift state */

static int pp = 1, NN = 1, nd = 0; /* base vertices per side, group order, number of darts */
static int di[MAXND], dj[MAXND], dg[MAXND];
static int bdi[MAXND], bdj[MAXND], bdg[MAXND];

/* True if dart t duplicates another dart on the same base pair with the same voltage. */
static int conflict(int t) {
    for (int u = 0; u < nd; u++)
        if (u != t && di[u] == di[t] && dj[u] == dj[t] && dg[u] == dg[t]) return 1;
    return 0;
}

/* Random d-regular base: d random permutation matrices, voltages made conflict-free. */
static int random_base(void) {
    nd = 0;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < pp; i++) perm[i] = i;
        for (int i = pp - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < pp; i++) {
            di[nd] = i; dj[nd] = perm[i]; dg[nd] = rndint(NN); nd++;
        }
    }
    for (int t = 0; t < nd; t++) {
        int tries = 0;
        while (conflict(t)) {
            if (++tries > 10000) return 0;
            dg[t] = rndint(NN);
        }
    }
    return 1;
}

/* Builds the lift LG from the current darts. Vertex (i,x) has index i*NN+x; B-side
 * vertices start at pp*NN. Every vertex ends with exactly d neighbours. */
static void build_lift(void) {
    int V = 2 * pp * NN;
    int B0 = pp * NN;
    LG.n = V;
    for (int v = 0; v < V; v++) {
        LG.deg[v] = 0;
        LG.side[v] = (unsigned char)(v >= B0);
    }
    for (int t = 0; t < nd; t++) {
        int i = di[t], j = dj[t], g = dg[t];
        for (int x = 0; x < NN; x++) {
            int a = i * NN + x;
            int b = B0 + j * NN + MT[x * NN + g];
            LG.adj[a][LG.deg[a]++] = b;
            LG.adj[b][LG.deg[b]++] = a;
        }
    }
}

static int vis[MAXV], qd[MAXV], qu[MAXV];
static int vstamp = 0;

/* Number of vertices within distance D of src (src included). */
static int reach_from(int src) {
    int head = 0, tail = 0;
    vstamp++;
    vis[src] = vstamp;
    qd[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        if (qd[v] >= D) continue;
        for (int k = 0; k < LG.deg[v]; k++) {
            int u = LG.adj[v][k];
            if (vis[u] != vstamp) {
                vis[u] = vstamp;
                qd[u] = qd[v] + 1;
                qu[tail++] = u;
            }
        }
    }
    return tail;
}

/* Sum over base representatives of unreached vertices. Zero means diameter <= D. */
static int lift_cost(void) {
    build_lift();
    int V = LG.n, cost = 0;
    for (int s = 0; s < 2 * pp; s++) cost += V - reach_from(s * NN);
    return cost;
}

static void swap_dj(int t1, int t2) {
    int tmp = dj[t1];
    dj[t1] = dj[t2];
    dj[t2] = tmp;
}

/* Simulated annealing on the current group (pp, NN must be set and MT built).
 * Returns 1 and leaves the zero-cost darts in place on success. */
static int sa_run(long steps) {
    if (!random_base()) return 0;
    int cur = lift_cost();
    int bestc = cur;
    memcpy(bdi, di, sizeof(int) * (size_t)nd);
    memcpy(bdj, dj, sizeof(int) * (size_t)nd);
    memcpy(bdg, dg, sizeof(int) * (size_t)nd);
    for (long s = 0; s < steps && bestc > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) break;
        double T = 3.0 * pow(0.002, (double)s / (double)steps);
        if (pp > 1 && rndint(100) < 15) {
            /* base rewire: swap the B-endpoints of two darts (keeps regularity) */
            int t1 = rndint(nd), t2 = rndint(nd);
            if (di[t1] == di[t2] || dj[t1] == dj[t2]) continue;
            swap_dj(t1, t2);
            if (conflict(t1) || conflict(t2)) { swap_dj(t1, t2); continue; }
            int nc = lift_cost();
            if (nc <= cur || rnd01() < exp(-(nc - cur) / T)) cur = nc;
            else swap_dj(t1, t2);
        } else {
            int t = rndint(nd);
            int old = dg[t];
            int g = rndint(NN);
            if (g == old) continue;
            dg[t] = g;
            if (conflict(t)) { dg[t] = old; continue; }
            int nc = lift_cost();
            if (nc <= cur || rnd01() < exp(-(nc - cur) / T)) cur = nc;
            else dg[t] = old;
        }
        if (cur < bestc) {
            bestc = cur;
            memcpy(bdi, di, sizeof(int) * (size_t)nd);
            memcpy(bdj, dj, sizeof(int) * (size_t)nd);
            memcpy(bdg, dg, sizeof(int) * (size_t)nd);
        }
    }
    if (bestc == 0) {
        memcpy(di, bdi, sizeof(int) * (size_t)nd);
        memcpy(dj, bdj, sizeof(int) * (size_t)nd);
        memcpy(dg, bdg, sizeof(int) * (size_t)nd);
    }
    return bestc == 0;
}

/* ------------------------------------------------------------------ validation */

static int cvis[MAXV], cqd[MAXV], cqu[MAXV];
static int cstamp = 0;

/* Full validity: simple, bipartite by side, degree <= d, diameter <= D, connected. */
static int check_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXV) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] < 0 || g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
            int back = 0;
            for (int k = 0; k < g->deg[u]; k++)
                if (g->adj[u][k] == v) back = 1;
            if (!back) return 0;
        }
    }
    for (int s = 0; s < n; s++) {
        int head = 0, tail = 0;
        cstamp++;
        cvis[s] = cstamp;
        cqd[s] = 0;
        cqu[tail++] = s;
        while (head < tail) {
            int v = cqu[head++];
            if (cqd[v] >= D) continue;
            for (int k = 0; k < g->deg[v]; k++) {
                int u = g->adj[v][k];
                if (cvis[u] != cstamp) {
                    cvis[u] = cstamp;
                    cqd[u] = cqd[v] + 1;
                    cqu[tail++] = u;
                }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

static void consider(const Graph *g) {
    if (g->n > best_n && check_valid(g)) {
        best = *g;
        best_n = g->n;
    }
}

/* Reads "n m" + edges from stdin; keeps it only if valid. */
static void read_start(void) {
    static Graph g;
    static int queue[MAXV];
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV || m < 0) return;
    memset(&g, 0, sizeof g);
    g.n = n;
    for (int v = 0; v < n; v++) g.side[v] = 255;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return;
        if (g.deg[u] >= MAXD || g.deg[v] >= MAXD) return;
        g.adj[u][g.deg[u]++] = v;
        g.adj[v][g.deg[v]++] = u;
    }
    for (int s = 0; s < n; s++) {
        if (g.side[s] != 255) continue;
        int head = 0, tail = 0;
        g.side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int k = 0; k < g.deg[v]; k++) {
                int u = g.adj[v][k];
                if (g.side[u] == 255) {
                    g.side[u] = (unsigned char)(1 - g.side[v]);
                    queue[tail++] = u;
                } else if (g.side[u] == g.side[v]) {
                    return;
                }
            }
        }
    }
    if (check_valid(&g)) {
        best = g;
        best_n = g.n;
    }
}

static void set_single(void) {
    memset(&best, 0, sizeof best);
    best.n = 1;
    best.side[0] = 0;
    best_n = 1;
}

/* K_{d,d} if valid, else a single vertex. Used only when nothing better is known. */
static void fallback(void) {
    if (best_n > 0) return;
    static Graph g;
    memset(&g, 0, sizeof g);
    g.n = 2 * d;
    for (int v = 0; v < g.n; v++) g.side[v] = (unsigned char)(v >= d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            g.adj[a][g.deg[a]++] = d + b;
            g.adj[d + b][g.deg[d + b]++] = a;
        }
    consider(&g);
    if (best_n == 0) set_single();
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

static void lift_to_graph(Graph *g) {
    build_lift();
    *g = LG;
}

/* ------------------------------------------------------------------ phases */

/* Phase A: bipartite Cayley graphs (p = 1). N runs downward from the Moore limit; the
 * first N with a valid connection set is the largest found, and the sweep stops there. */
static void cayley_sweep(double until) {
    long hi = moore_bound() / 2;
    if (hi > MAXV / 2) hi = MAXV / 2;
    for (long N = hi; N >= d + 1 && N >= best_n / 2 + 1; N--) {
        if (now() > until) return;
        int cnt = enum_groups((int)N);
        if (cnt == 0) continue;
        pp = 1;
        NN = (int)N;
        nd = d;
        int found = 0;
        for (int batch = 0; batch < 10 && !found; batch++) {
            if (now() > until) return;
            int idx = rndint(cnt);
            int m = gl_m[idx];
            if (!build_group(m, (int)N / m, gl_r[idx])) return;
            for (int t = 0; t < 150 && !found; t++) {
                for (int i = 0; i < d;) {
                    int x = rndint(NN), dup = 0;
                    for (int q = 0; q < i; q++)
                        if (dg[q] == x) dup = 1;
                    if (!dup) {
                        di[i] = 0;
                        dj[i] = 0;
                        dg[i] = x;
                        i++;
                    }
                }
                if (lift_cost() == 0) {
                    lift_to_graph(&tmpg);
                    consider(&tmpg);
                    found = 1;
                }
            }
        }
    }
}

/* Phase B: annealed lifts with p = 1..4 base vertices per side. Each run targets a lift
 * order just above the best found so far. */
static void sa_phase(double until) {
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(100);
        int p = r < 20 ? 1 : r < 45 ? 2 : r < 75 ? 3 : 4;
        long N = best_n / (2 * p) + 1;
        if (rndint(3) == 0) N += rndint(3);
        if (N < d + 1) N = d + 1;
        if (2L * p * N > moore || 2L * p * N > MAXV) continue;
        int cnt = enum_groups((int)N);
        if (cnt == 0) continue;
        int idx = rndint(cnt);
        int m = gl_m[idx];
        pp = p;
        NN = (int)N;
        nd = d * p;
        if (!build_group(m, (int)N / m, gl_r[idx])) return;
        if (sa_run(40000)) {
            lift_to_graph(&tmpg);
            consider(&tmpg);
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        set_single();
        print_graph(&best);
        return 0;
    }
    read_start();
    fallback();
    if (best_n < moore_bound()) {
        double span = t_end - t0;
        cayley_sweep(t0 + 0.3 * span);
        sa_phase(t_end);
    }
    if (!check_valid(&best)) set_single();
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
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    timeout = time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.2 and timeout > budget:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=timeout)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
