"""Bi-Cayley / voltage-lift search for bipartite degree-diameter graphs.

Strategy:
  * Lifts of a d-regular base multigraph with p vertices per side over a group G of
    order N (semidirect products Z_m x| Z_k). Vertices are (side, base vertex, group element)
    and each dart (i, j, g) joins A(i, x) to B(j, x*g).
  * Left translation by G is an automorphism, so a lift has diameter <= D iff every
    vertex is within D of the 2p "identity" representatives A(i, e) and B(j, e).
    Evaluating a candidate therefore costs 2p BFS runs, not an all-pairs check.
  * Simulated annealing over the voltages and the base structure (dart endpoint swaps),
    with the number of unreached (representative, vertex) pairs as the cost.
  * The target order is pushed upward one step at a time, always trying a random group
    of order just large enough to beat the current best.

Fallback: the start graph (if valid) or K_{d,d}. Python keeps the best valid graph.
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
#define MAXP 4
#define MAXND (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN];   /* rp[b] = r^b mod m */
} Grp;

typedef struct {
    int p, N, nd;
    int di[MAXND], dj[MAXND], dg[MAXND];   /* dart: A-vertex di -> B-vertex dj, voltage dg */
} Lift;

static int d, D;
static double t_end;
static Graph out;
static Graph cand;
static Grp GG;
static int NB[MAXN][MAXD];
static int NBC[MAXN];

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* Full validity: simple, bipartite (side labels), degree <= d, every pair within D. */
static int full_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    static int dist[MAXN], q[MAXN];
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; q[tail++] = u; }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

/* Read "n m" + edges; 2-colour; keep only if fully valid. Leaves n = 0 otherwise. */
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
    if (!full_valid(g)) g->n = 0;
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

/* ------------------------------------------------------------ groups */

/* Element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int gmul(int x, int y) {
    int a = x / GG.k, b = x % GG.k, c = y / GG.k, e = y % GG.k;
    return (int)((a + (long)GG.rp[b] * c) % GG.m) * GG.k + (b + e) % GG.k;
}

/* Uniform random semidirect product of order N (reservoir over (m, r) choices). */
static int random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    GG.m = bm;
    GG.k = bk;
    GG.r = br;
    GG.rp[0] = 1 % GG.m;
    for (int b = 1; b < GG.k; b++)
        GG.rp[b] = (int)((long)GG.rp[b - 1] * GG.r % GG.m);
    return 1;
}

/* ------------------------------------------------------------ lifts */

/* Dart validity: no two darts with the same (i, j, g), which would create a multi-edge. */
static int darts_ok(const Lift *L) {
    for (int t = 0; t < L->nd; t++)
        for (int s = 0; s < t; s++)
            if (L->di[s] == L->di[t] && L->dj[s] == L->dj[t] && L->dg[s] == L->dg[t])
                return 0;
    return 1;
}

static int clash_before(const Lift *L, int t, int g) {
    for (int s = 0; s < t; s++)
        if (L->di[s] == L->di[t] && L->dj[s] == L->dj[t] && L->dg[s] == g) return 1;
    return 0;
}

/* Fill NB/NBC with the adjacency of the lift. Each vertex has exactly d neighbours. */
static void lift_adj(const Lift *L) {
    int p = L->p, N = L->N, V = 2 * p * N;
    for (int v = 0; v < V; v++) NBC[v] = 0;
    for (int t = 0; t < L->nd; t++)
        for (int x = 0; x < N; x++) {
            int a = L->di[t] * N + x;
            int b = p * N + L->dj[t] * N + gmul(x, L->dg[t]);
            NB[a][NBC[a]++] = b;
            NB[b][NBC[b]++] = a;
        }
}

/* Number of (representative, vertex) pairs at distance > D. Zero means a valid lift. */
static int eval_lift(const Lift *L) {
    lift_adj(L);
    int p = L->p, N = L->N, V = 2 * p * N;
    static int dist[MAXN], q[MAXN];
    int total = 0;
    for (int r = 0; r < 2 * p; r++) {
        int src = r < p ? r * N : p * N + (r - p) * N;
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        q[tail++] = src;
        while (head < tail) {
            int v = q[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < NBC[v]; i++) {
                int u = NB[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; q[tail++] = u; }
            }
        }
        total += V - tail;
    }
    return total;
}

static void build_graph(const Lift *L, Graph *g) {
    int p = L->p, N = L->N;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < L->nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, L->di[t] * N + x, p * N + L->dj[t] * N + gmul(x, L->dg[t]));
}

/* Simulated annealing over voltages and base-graph endpoint swaps. Returns 1 if valid. */
static int try_lift(int p, int N, long steps, Lift *L) {
    L->p = p;
    L->N = N;
    L->nd = d * p;
    int t = 0;
    for (int k = 0; k < d; k++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < p; i++, t++) {
            L->di[t] = i;
            L->dj[t] = perm[i];
            int g;
            do { g = rndint(N); } while (clash_before(L, t, g));
            L->dg[t] = g;
        }
    }
    int cost = eval_lift(L);
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        Lift save = *L;
        int mv = rndint(3);
        if (mv < 2) {
            int t1 = rndint(L->nd);
            L->dg[t1] = rndint(N);
        } else {
            int t1 = rndint(L->nd), t2 = rndint(L->nd);
            if (L->dj[t1] == L->dj[t2]) continue;
            int tmp = L->dj[t1];
            L->dj[t1] = L->dj[t2];
            L->dj[t2] = tmp;
        }
        if (!darts_ok(L)) { *L = save; continue; }
        int nc = eval_lift(L);
        double T = 0.25 + 0.75 * (double)(s % 2000) / 2000.0;
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) cost = nc;
        else *L = save;
    }
    return cost == 0;
}

/* Keep trying lifts that are strictly larger than the current best. */
static void search(double until) {
    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    long fails = 0;
    static Lift L;
    while (now() < until) {
        long target = out.n + 2;
        if (target > cap) break;
        int r = rndint(10);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : 4;
        long N = (target + 2 * p - 1) / (2 * p) + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > cap) {
            if (++fails > 1000000) break;
            continue;
        }
        if (!random_group((int)N)) continue;
        long steps = 20000;
        if (!try_lift(p, (int)N, steps, &L)) continue;
        build_graph(&L, &cand);
        if (cand.n > out.n && full_valid(&cand)) copy_graph(&out, &cand);
    }
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.93 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("1 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }

    read_start(&out);
    if (out.n == 0) complete_bipartite(&out);
    if (!full_valid(&out)) complete_bipartite(&out);

    if (out.n < moore_bound()) search(t_end);

    if (!full_valid(&out)) complete_bipartite(&out);
    print_graph(&out);
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


def _fallback(d, D):
    """A graph that is certainly valid for (d, D)."""
    for cand in (lib.haar_graph(d, range(d)), (2, [(0, 1)]), (1, [])):
        try:
            if lib.is_valid(*cand, d, D):
                return cand
        except Exception:
            pass
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is not None and not lib.is_valid(*start, d, D):
        start = None
    best = start if start is not None else _fallback(d, D)
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except (RuntimeError, ValueError, OSError):
            pass
    return best
