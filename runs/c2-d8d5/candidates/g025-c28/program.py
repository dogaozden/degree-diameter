"""Cyclic voltage-lift search with bounded base matrices, plus exact and simple fallbacks.

Changes from the parent: the Python bi-Cayley phase is gone. C searches voltage lifts of
random d-regular bipartite base multigraphs (k <= 4 blocks per side) over Z_N. Each candidate
is scored by BFS from one representative per block (vertex-transitivity under Z_N makes this
exact), and simulated annealing moves voltages and double-swaps base darts. Every accepted
graph is re-checked with exact bitset diameter tests. Python keeps a valid fallback.
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
#define MAXK 4
#define MAXDART (MAXK * MAXD)

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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

/* ---- voltage lift state: K blocks per side over Z_Nn, darts (dI, dJ, dG) ---- */
static int Kb, Nn, nd;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART];
static int lA[MAXK][MAXD], lB[MAXK][MAXD];
static int distv[MAXN], qv[MAXN];

static void rebuild_lists(void) {
    int ca[MAXK] = {0}, cb[MAXK] = {0};
    for (int t = 0; t < nd; t++) {
        lA[dI[t]][ca[dI[t]]++] = t;
        lB[dJ[t]][cb[dJ[t]]++] = t;
    }
}

/* Vertices A_{i,x} = i*Nn + x, B_{j,y} = (Kb+j)*Nn + y; dart (i,j,g): A_{i,x} ~ B_{j,x+g}. */
static int unreached_from(int src) {
    int V = 2 * Kb * Nn, KN = Kb * Nn;
    for (int v = 0; v < V; v++) distv[v] = -1;
    int head = 0, tail = 0;
    distv[src] = 0;
    qv[tail++] = src;
    while (head < tail) {
        int v = qv[head++];
        int dv = distv[v];
        if (dv >= D) continue;
        if (v < KN) {
            int i = v / Nn, x = v - i * Nn;
            for (int c = 0; c < d; c++) {
                int t = lA[i][c];
                int u = (Kb + dJ[t]) * Nn + (x + dG[t]) % Nn;
                if (distv[u] < 0) { distv[u] = dv + 1; qv[tail++] = u; }
            }
        } else {
            int r = v - KN;
            int j = r / Nn, y = r - j * Nn;
            for (int c = 0; c < d; c++) {
                int t = lB[j][c];
                int u = dI[t] * Nn + (y - dG[t] + Nn) % Nn;
                if (distv[u] < 0) { distv[u] = dv + 1; qv[tail++] = u; }
            }
        }
    }
    return V - tail;
}

static int eval_cost(void) {
    rebuild_lists();
    int c = 0;
    for (int b = 0; b < 2 * Kb; b++) c += unreached_from(b * Nn);
    return c;
}

static int clashes(int t) {
    for (int s = 0; s < nd; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == dG[t]) return 1;
    return 0;
}

static void random_init(void) {
    nd = Kb * d;
    for (int t = 0; t < d; t++) {
        int perm[MAXK];
        for (int i = 0; i < Kb; i++) perm[i] = i;
        for (int i = Kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < Kb; i++) {
            int idx = t * Kb + i;
            dI[idx] = i;
            dJ[idx] = perm[i];
            dG[idx] = 0;
        }
    }
    for (int t = 0; t < nd; t++) {
        for (;;) {
            int g = rndint(Nn), clash = 0;
            for (int s = 0; s < t; s++)
                if (dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == g) { clash = 1; break; }
            if (!clash) { dG[t] = g; break; }
        }
    }
}

static void build_graph(Graph *g) {
    int KN = Kb * Nn;
    g->n = 2 * KN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= KN; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < Nn; x++)
            add_edge(g, dI[t] * Nn + x, (Kb + dJ[t]) * Nn + (x + dG[t]) % Nn);
}

/* Simulated annealing on voltages (80%) and double-swaps of base endpoints (20%). */
static int attempt(int k, int n_per, long steps, long patience) {
    Kb = k;
    Nn = n_per;
    random_init();
    int cur = eval_cost();
    if (cur == 0) return 1;
    int best_local = cur;
    long stagn = 0;
    for (long s = 0; s < steps; s++) {
        if ((s & 255) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.8) {
            int t = rndint(nd);
            int old = dG[t];
            int g = rndint(Nn);
            if (g == old) continue;
            dG[t] = g;
            if (clashes(t)) { dG[t] = old; continue; }
            int c2 = eval_cost();
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / T)) cur = c2;
            else { dG[t] = old; continue; }
        } else {
            int t1 = rndint(nd), t2 = rndint(nd);
            if (t1 == t2 || dJ[t1] == dJ[t2]) continue;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            if (clashes(t1) || clashes(t2)) {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                continue;
            }
            int c2 = eval_cost();
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / T)) cur = c2;
            else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                continue;
            }
        }
        if (cur == 0) return 1;
        if (cur < best_local) { best_local = cur; stagn = 0; }
        else if (++stagn > patience) return 0;
    }
    return 0;
}

static Graph best, cand;
static int frontier[MAXK + 1];

static int minN(int k) {
    int v = best.n / (2 * k) + 1;
    return v < d ? d : v;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        if (d >= 1 && d <= MAXD) { complete_bipartite(&best); print_graph(&best); }
        else printf("1 0\n");
        return 0;
    }
    complete_bipartite(&best);
    long moore = moore_bound();

    while (now() < t_end) {
        int cks[MAXK], nc = 0;
        for (int k = 1; k <= MAXK; k++) {
            int mn = minN(k);
            if (frontier[k] < mn) frontier[k] = mn;
            long tot = 2L * k * frontier[k];
            if (tot <= moore && tot <= MAXN) cks[nc++] = k;
        }
        if (nc == 0) break;
        int k = cks[rndint(nc)];
        int N_try = frontier[k];
        if (attempt(k, N_try, 30000, 6000)) {
            build_graph(&cand);
            if (cand.n > best.n && is_valid(&cand)) best = cand;
            frontier[k] = N_try + 1;
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    pg = _best_pg(d)
    if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
        best = pg

    if D == 2:
        return best
    if D == 3:
        if lib.is_prime_power(d - 1):
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                if ar[0] > best[0] and lib.is_valid(ar[0], ar[1], d, D):
                    best = ar
            except (ValueError, RuntimeError):
                pass

    if d <= 32:
        # Leave room for compilation, output and the final checks.
        elapsed = time.monotonic() - t0
        c_limit = round(0.8 * time_limit - 3.0 - elapsed, 2)
        if c_limit >= 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, c_limit],
                                 stdin_graph=None, timeout=c_limit + 6)
                n, e = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
