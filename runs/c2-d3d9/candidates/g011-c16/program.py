"""Combined program, v3: voltage annealing on bi-Cayley graphs.

Main change: instead of testing random or exhaustive voltage choices for feasibility only, the C
core runs simulated annealing on the voltages of a one-vertex-per-side bi-Cayley graph over
Z_m x|_r Z_k. The cost is the number of vertex pairs farther than D apart, counted by two BFS
runs from a_e and b_e. G acts regularly on both sides by left multiplication, so cost 0 proves
diameter <= D. Each order N gets a time slice over random groups, and the search moves to N+1
after success or when the slice runs out. The result is checked in C and again in Python with
lib.is_valid. The algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) is the fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley annealing search, v3.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Graph: A-vertex x (0..N-1) ~ B-vertex N+(x*g_t) for voltages g_0 = e, g_1..g_{d-1}
 * in G = Z_m x|_r Z_k. Left multiplication is an automorphism, so BFS from a_e and b_e
 * decides diameter. Cost = unreached vertices from a_e + from b_e; cost 0 means valid.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096
#define MAXH (MAXV / 2)
#define MAXD 32
#define MAXTRI 8192
#define SLICE 1.0
#define STEPS 6000

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
} Graph;

static int d, D;

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

static int dist_buf[MAXV], queue_buf[MAXV];

static int structural_ok(const Graph *g) {
    if (g->n <= 0 || g->n > MAXV) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return 1;
}

/* Full check: BFS from every vertex, depth D. Used once on the final graph and on input. */
static int full_valid(const Graph *g) {
    if (!structural_ok(g)) return 0;
    int nv = g->n;
    for (int s = 0; s < nv; s++) {
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[s] = 0;
        queue_buf[tail++] = s;
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
        if (tail < nv) return 0;
    }
    return 1;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue_buf[tail++] = s;
        while (head < tail) {
            int v = queue_buf[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    queue_buf[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct { int m, k, r; int rp[MAXH]; } Grp;
typedef struct { int m, k, r; } Tri;

static Tri tris[MAXTRI];
static int ntri;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    long t = ((long)a + (long)G->rp[b] * c) % G->m;
    return (int)(t * G->k + (b + e) % G->k);
}

/* Inverse of (a, b) is (-r^(-b) a, -b). */
static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long c = (G->m - ((long)G->rp[nb] * a) % G->m) % G->m;
    return (int)(c * G->k + nb);
}

static void set_group(Grp *G, Tri t) {
    G->m = t.m; G->k = t.k; G->r = t.r;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++)
        G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
}

static void list_groups(int N) {
    ntri = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ntri < MAXTRI) {
                tris[ntri].m = m; tris[ntri].k = k; tris[ntri].r = r;
                ntri++;
            }
        }
    }
}

/* ------------------------------------------------- annealing on voltages */

/* Unreached vertices (distance > D or none) from src in the bi-Cayley graph. */
static int unreached_from(int N, const Grp *G, const int *gs, const int *gi, int nd, int src) {
    int nv = 2 * N, head = 0, tail = 0;
    for (int v = 0; v < nv; v++) dist_buf[v] = -1;
    dist_buf[src] = 0;
    queue_buf[tail++] = src;
    while (head < tail) {
        int v = queue_buf[head++];
        if (dist_buf[v] >= D) continue;
        for (int t = 0; t < nd; t++) {
            int u = v < N ? N + gmul(G, v, gs[t]) : gmul(G, v - N, gi[t]);
            if (dist_buf[u] < 0) {
                dist_buf[u] = dist_buf[v] + 1;
                queue_buf[tail++] = u;
            }
        }
    }
    return nv - tail;
}

static int cost_of(int N, const Grp *G, const int *gs, const int *gi, int nd) {
    return unreached_from(N, G, gs, gi, nd, 0) + unreached_from(N, G, gs, gi, nd, N);
}

/* Random value in 1..N-1, distinct from gs[t] for t != skip, t >= 1. */
static int fresh_val(const int *gs, int nd, int skip, int N) {
    for (;;) {
        int g = 1 + rndint(N - 1), clash = 0;
        for (int t = 1; t < nd; t++)
            if (t != skip && gs[t] == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Simulated annealing on voltages g_1..g_{d-1} (g_0 = e). Returns 1 with cost 0 in gs. */
static int anneal(int N, const Grp *G, int *gs, int nd, long steps, double until) {
    int gi[MAXD];
    gs[0] = 0;
    for (int t = 1; t < nd; t++) gs[t] = -1;
    for (int t = 1; t < nd; t++) gs[t] = fresh_val(gs, nd, t, N);
    for (int t = 0; t < nd; t++) gi[t] = ginv(G, gs[t]);
    int cur = cost_of(N, G, gs, gi, nd);
    if (cur == 0) return 1;
    for (long s = 0; s < steps; s++) {
        if ((s & 63) == 0 && now() > until) break;
        double T = 3.0 * pow(0.03, (double)s / (double)steps);
        int t = 1 + rndint(nd - 1);
        int old = gs[t], oldi = gi[t];
        gs[t] = fresh_val(gs, nd, t, N);
        gi[t] = ginv(G, gs[t]);
        int nc = cost_of(N, G, gs, gi, nd);
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            gs[t] = old;
            gi[t] = oldi;
        }
    }
    return 0;
}

static void build_bc(Graph *g, int N, const Grp *G, const int *gs, int nd) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < nd; t++)
            add_edge(g, x, N + gmul(G, x, gs[t]));
}

/* Ascending orders N. Each N gets a time slice over random groups and restarts. */
static void sweep(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int N = best->n / 2 + 1;
    if (N < d + 1) N = d + 1;
    while (now() < until) {
        if (2L * N > moore || 2 * N > MAXV || N > MAXH) break;
        list_groups(N);
        double slice_end = now() + SLICE;
        if (slice_end > until) slice_end = until;
        int found = 0;
        while (!found && ntri > 0 && now() < slice_end) {
            int gs[MAXD];
            set_group(&G, tris[rndint(ntri)]);
            if (anneal(N, &G, gs, d, STEPS, slice_end)) {
                build_bc(&cand, N, &G, gs, d);
                if (cand.n > best->n && structural_ok(&cand)) {
                    copy_graph(best, &cand);
                    found = 1;
                }
            }
        }
        N++;
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
    double until = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("1 0\n"); return 0; }
    if (d == 1 || D == 1) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if ((long)best.n < moore_bound()) sweep(&best, until);
    if (!full_valid(&best)) complete_bipartite(&best);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
