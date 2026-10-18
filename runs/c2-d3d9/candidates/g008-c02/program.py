"""Lift search over metacyclic groups: simulated annealing on voltages instead of hill-climbing.

Python builds the best known start graph (or a fallback) and hands it to one C run.
The C engine anneals voltage lifts Z_m x|_r Z_k with 1 to 5 base vertices per side.
Cost = unreached (base vertex, target) pairs within D, from one BFS per base vertex,
because left multiplication by the group is an automorphism transitive on each fibre.
Every returned graph is checked with lib.is_valid, so a failed search only costs time.
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
#define MAXD 16
#define MAXP 6

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ------------------------------------------------------------ graphs */

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * MAXD);
    }
}

static int dist_g[MAXN], q_g[MAXN];

/* Full check: simple, bipartite by side labels, degree <= d, every pair within D. */
static int graph_valid(const Graph *g) {
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
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist_g[v] = -1;
        int head = 0, tail = 0;
        dist_g[s] = 0;
        q_g[tail++] = s;
        while (head < tail) {
            int v = q_g[head++];
            if (dist_g[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_g[u] < 0) { dist_g[u] = dist_g[v] + 1; q_g[tail++] = u; }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 2; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 2) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 2) { g->side[u] = (unsigned char)(1 - g->side[v]); queue[tail++] = u; }
            }
        }
    }
    if (!graph_valid(g)) g->n = 0;
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

/* Z_m x|_r Z_k: element (a,b) is the integer a*k+b; (a,b)(c,e) = (a + r^b c, b+e). */
typedef struct {
    int m, k, r, N;
    int rp[MAXN];   /* rp[b] = r^b mod m */
} Grp;

static void set_group(Grp *G, int m, int k, int r) {
    G->m = m;
    G->k = k;
    G->r = r;
    G->N = m * k;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    int a2 = (int)(((long)a + (long)G->rp[b] * c) % G->m);
    return a2 * G->k + (b + e) % G->k;
}

static int gl_m[MAXN], gl_k[MAXN], gl_r[MAXN];

/* All (m, k, r) with m*k = N, gcd(r,m) = 1, r^k = 1 mod m. Returns the count. */
static int list_groups(int N) {
    int c = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (c < MAXN) { gl_m[c] = 1; gl_k[c] = k; gl_r[c] = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (c < MAXN) { gl_m[c] = m; gl_k[c] = k; gl_r[c] = r; c++; }
        }
    }
    return c;
}

/* ------------------------------------------------------------ voltage lifts */

/* Base: layer t maps A_i to B_{perm[t][i]} with voltage g[t][i].
 * Each layer is a permutation, so the base is d-regular bipartite with p vertices per side.
 * Lift: A_{i,x} ~ B_{perm[t][i], x*g[t][i]} for x in G. Vertex index: A_{i,x} = i*N+x,
 * B_{j,y} = (p+j)*N+y. */
typedef struct {
    int p, N;
    int perm[MAXD][MAXP];
    int g[MAXD][MAXP];
} Lift;

static int adjL[MAXN][MAXD];
static int distL[MAXN], qL[MAXN];

/* Fills adjL. Returns the number of clashes (two layers giving the same parallel edge). */
static int lift_adj(const Lift *L, const Grp *G) {
    int p = L->p, N = L->N;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) {
            int j = L->perm[t][i];
            int gv = L->g[t][i];
            for (int x = 0; x < N; x++) {
                int u = i * N + x;
                int w = (p + j) * N + gmul(G, x, gv);
                adjL[u][t] = w;
                adjL[w][t] = u;
            }
        }
    int clash = 0;
    for (int i = 0; i < p; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (L->perm[t][i] == L->perm[t2][i] && L->g[t][i] == L->g[t2][i]) clash++;
    return clash;
}

/* Cost = unreached (source, target) pairs at distance > D, summed over the 2p fibre
 * representatives, plus a heavy penalty per parallel edge. Zero iff the lift is valid. */
static long lift_cost(const Lift *L, const Grp *G) {
    int p = L->p, N = L->N, V = 2 * p * N;
    long cost = (long)lift_adj(L, G) * V;
    for (int s0 = 0; s0 < 2 * p; s0++) {
        int s = s0 * N;   /* x = 0 is the identity */
        for (int v = 0; v < V; v++) distL[v] = -1;
        int head = 0, tail = 0;
        distL[s] = 0;
        qL[tail++] = s;
        while (head < tail) {
            int v = qL[head++];
            if (distL[v] >= D) continue;
            for (int t = 0; t < d; t++) {
                int u = adjL[v][t];
                if (distL[u] < 0) { distL[u] = distL[v] + 1; qL[tail++] = u; }
            }
        }
        cost += V - tail;
    }
    return cost;
}

static void random_lift(Lift *L, int p, int N) {
    L->p = p;
    L->N = N;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < p; i++) L->perm[t][i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = L->perm[t][i];
            L->perm[t][i] = L->perm[t][j];
            L->perm[t][j] = s;
        }
        for (int i = 0; i < p; i++) L->g[t][i] = rndint(N);
    }
}

/* Simulated annealing over voltages and base permutations. Returns 1 if cost reaches 0. */
static int sa_lift(Lift *L, const Grp *G, long steps) {
    long cur = lift_cost(L, G);
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        int t = rndint(d);
        if (L->p > 1 && rndint(8) == 0) {
            int i = rndint(L->p), i2 = rndint(L->p);
            if (i == i2) continue;
            int tmp = L->perm[t][i];
            L->perm[t][i] = L->perm[t][i2];
            L->perm[t][i2] = tmp;
            long nc = lift_cost(L, G);
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
                cur = nc;
            } else {
                tmp = L->perm[t][i];
                L->perm[t][i] = L->perm[t][i2];
                L->perm[t][i2] = tmp;
            }
        } else {
            int i = rndint(L->p);
            int old = L->g[t][i];
            int nv = rndint(L->N);
            if (nv == old) continue;
            L->g[t][i] = nv;
            long nc = lift_cost(L, G);
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) cur = nc;
            else L->g[t][i] = old;
        }
    }
    return cur == 0;
}

static void lift_to_graph(const Lift *L, const Grp *G, Graph *out) {
    int p = L->p, N = L->N;
    out->n = 2 * p * N;
    for (int v = 0; v < out->n; v++) {
        out->deg[v] = 0;
        out->side[v] = (unsigned char)(v >= p * N);
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++)
            for (int x = 0; x < N; x++)
                add_edge(out, i * N + x, (p + L->perm[t][i]) * N + gmul(G, x, L->g[t][i]));
}

/* Repeatedly anneal a random lift of order just above the current best. */
static void lift_search(Graph *best, double until) {
    static Lift L;
    static Grp G;
    static Graph cand;
    long moore = moore_bound();
    long fails = 0;
    while (now() < until) {
        int r = rndint(12);
        int p = r < 5 ? 1 : r < 8 ? 2 : r < 10 ? 3 : r < 11 ? 4 : 5;
        long target = best->n + 2;
        long N = (target + 2 * p - 1) / (2 * p) + rndint(3);
        if (N < 2) N = 2;
        long Nmax = moore / (2 * p);
        if (Nmax > MAXN / (2 * p)) Nmax = MAXN / (2 * p);
        if (N > Nmax) N = Nmax;
        if (N < 2 || 2 * p * N < target) {
            if (++fails > 100000) return;
            continue;
        }
        int gc = list_groups((int)N);
        if (gc == 0) continue;
        int gi = rndint(gc);
        set_group(&G, gl_m[gi], gl_k[gi], gl_r[gi]);
        random_lift(&L, p, (int)N);
        if (sa_lift(&L, &G, 60000)) {
            lift_to_graph(&L, &G, &cand);
            if (cand.n > best->n && graph_valid(&cand)) copy_graph(best, &cand);
        }
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
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!graph_valid(&best)) complete_bipartite(&best);

    if (best.n < moore_bound()) lift_search(&best, t_end);

    if (!graph_valid(&best)) complete_bipartite(&best);
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


def _fallback(d, D):
    """A graph that is certainly valid: K_{d,d} for D >= 2, K_2 for D = 1."""
    candidates = []
    if d >= 1:
        candidates.append(lib.haar_graph(d, range(d)))
    candidates.append((2, [(0, 1)]))
    for g in candidates:
        if lib.is_valid(g[0], g[1], d, D):
            return g
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = _fallback(d, D)
    try:
        start = known_start(d, D)
        if start is not None and lib.is_valid(start[0], start[1], d, D) and start[0] > best[0]:
            best = start
    except Exception:
        pass

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
