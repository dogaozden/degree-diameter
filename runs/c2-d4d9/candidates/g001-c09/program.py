"""Starter program: Python builds the best known start graph, the C engine searches from it.

Most improvements belong in C_SOURCE (it runs 10-100x faster than Python).
build() keeps the best valid graph it has, so a broken idea in C can only cost time.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core: orbit-reduced voltage-lift annealing.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * New idea (orbit-reduced energy):
 *   A lift over a group G = Z_m x| Z_k has vertices (i, x) on side A and (j, y) on side B,
 *   with edges (i, x) -- (j, x*g) for every dart (i, j, g). Left multiplication by any
 *   h in G is an automorphism, so the vertices of each side form 2p orbits. Two vertices
 *   of the same orbit see the same ball structure, so the graph has diameter <= D iff the
 *   BFS ball of each of the 2p orbit representatives (vertex i*N + identity, etc.) covers
 *   the whole graph. The energy (sum of unreached vertices over the 2p representatives)
 *   therefore costs 2p BFS runs instead of n bitset rounds. It is zero iff the lift is valid.
 *   This makes voltage annealing an order of magnitude faster than full pair counting.
 *
 * Search: pick p (base size per side), N (group order just above the best size), a random
 * group Z_m x| Z_k, and a random d-regular base multigraph; anneal the voltages on the
 * orbit energy with a periodically reheated Metropolis schedule. Accept the first zero
 * energy lift that beats the best graph, and confirm it with the full bitset check.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 8

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

/* ------------------------------------------------------------------ full check (bitset) */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (0 means connected with diameter <= D). */
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

/* K_{1,1}: valid for D >= 1. */
static void single_edge(Graph *g) {
    g->n = 2;
    g->deg[0] = g->deg[1] = 0;
    g->side[0] = 0;
    g->side[1] = 1;
    add_edge(g, 0, 1);
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

/* Pick a uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m.
 * Cyclic Z_N (m = 1) is always a candidate, so this always succeeds. The identity is index 0. */
static int random_group(int N, Grp *G) {
    long count = 0;
    G->m = 1; G->k = N; G->r = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { G->m = m; G->k = k; G->r = r; }
        }
    }
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------------ base multigraph */

/* Random d-regular bipartite base multigraph with p vertices per side (sum of d random
 * permutation matrices), retried until connected. M[i][j] = number of darts i -> j. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
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

/* ------------------------------------------------------------------ lift state */

static const Grp *LG;          /* current group */
static int P, NN, ND;          /* base size per side, group order, number of darts (= P*d) */
static int dI[MAXP * MAXD], dJ[MAXP * MAXD], dG[MAXP * MAXD];
static int dSA[MAXP * MAXD], dSB[MAXP * MAXD]; /* slot of dart in its A-end / B-end list */
static int nbr[MAXN * MAXD];   /* nbr[v*d + s]: s-th neighbour of lift vertex v */

/* Vertex ids: A-vertex (i, x) = i*NN + x, B-vertex (j, y) = P*NN + j*NN + y. */

static void lift_layout(int p, int M[MAXP][MAXP]) {
    P = p;
    ND = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dI[ND] = i; dJ[ND] = j; dG[ND] = -1; ND++;
            }
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < ND; t++) {
        dSA[t] = ca[dI[t]]++;
        dSB[t] = cb[dJ[t]]++;
    }
}

/* Write dart t with voltage g into nbr. Every slot of dart t is overwritten, so the
 * previous voltage leaves no stale entries behind. */
static void set_dart(int t, int g) {
    int N = NN, p = P;
    dG[t] = g;
    for (int x = 0; x < N; x++) {
        int y = gmul(LG, x, g);
        int a = dI[t] * N + x;
        int b = p * N + dJ[t] * N + y;
        nbr[a * d + dSA[t]] = b;
        nbr[b * d + dSB[t]] = a;
    }
}

/* A voltage for dart t not used by another dart on the same (i, j) pair. */
static int fresh_g(int t) {
    for (;;) {
        int g = rndint(NN), ok = 1;
        for (int s = 0; s < ND; s++)
            if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == g) { ok = 0; break; }
        if (ok) return g;
    }
}

static void lift_random_init(void) {
    for (int t = 0; t < ND; t++) dG[t] = -1;
    for (int t = 0; t < ND; t++) set_dart(t, fresh_g(t));
}

/* Orbit-reduced energy: sum over the 2P orbit representatives of the number of vertices
 * NOT within distance D. Zero iff the lift is connected with diameter <= D. */
static unsigned vis[MAXN];
static unsigned vstamp = 0;
static int qb[MAXN];

static long lift_energy(void) {
    int n = 2 * P * NN;
    long E = 0;
    for (int r = 0; r < 2 * P; r++) {
        int s = r < P ? r * NN : P * NN + (r - P) * NN;
        vstamp++;
        int head = 0, tail = 0;
        qb[tail++] = s;
        vis[s] = vstamp;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int v = qb[head++];
                const int *nb = nbr + v * d;
                for (int i = 0; i < d; i++) {
                    int u = nb[i];
                    if (vis[u] != vstamp) { vis[u] = vstamp; qb[tail++] = u; }
                }
            }
        }
        E += n - tail;
    }
    return E;
}

/* Anneal the voltages until the orbit energy is 0 or the deadline passes.
 * Returns 1 if a valid lift is left in nbr. */
static int lift_anneal(double until) {
    lift_random_init();
    long E = lift_energy();
    if (E == 0) return 1;
    double T0 = 1.0 + 0.05 * (double)E, T1 = 0.25;
    const long PERIOD = 4000;
    for (long step = 1;; step++) {
        if ((step & 31) == 0 && now() > until) return 0;
        double phase = (double)(step % PERIOD) / (double)PERIOD;
        double T = T0 * pow(T1 / T0, phase);
        int t = rndint(ND);
        int old = dG[t];
        set_dart(t, fresh_g(t));
        long E2 = lift_energy();
        if (E2 <= E || rnd01() < exp((double)(E - E2) / T)) {
            E = E2;
            if (E == 0) return 1;
        } else {
            set_dart(t, old);
        }
    }
}

/* Expand the current lift (nbr) into a full Graph. Each edge is added from its A end. */
static void lift_to_graph(Graph *g) {
    int A = P * NN, n = 2 * A;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= A;
    }
    for (int v = 0; v < A; v++)
        for (int i = 0; i < d; i++) add_edge(g, v, nbr[v * d + i]);
}

/* ------------------------------------------------------------------ search driver */

static void lift_search(Graph *best, double until) {
    static Grp G;
    static Graph cand;
    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : r < 9 ? 4 : 5 + rndint(2);
        if (d < 2) p = 1;   /* a connected d-regular base needs d >= 2 unless p = 1 */
        long N = best->n / (2L * p) + 1;   /* smallest order that beats best */
        if (N < d) N = d;                  /* enough room for distinct voltages */
        if (2L * p * N > cap) {
            p = 1;
            N = best->n / 2 + 1;
            if (N < d) N = d;
            if (2L * N > cap) return;
        }
        if (!random_group((int)N, &G)) continue;
        LG = &G;
        NN = (int)N;
        int M[MAXP][MAXP];
        make_base(p, M);
        lift_layout(p, M);
        double slice = now() + 4.0;
        if (slice > until) slice = until;
        if (lift_anneal(slice)) {
            lift_to_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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
    if (d < 1 || D < 1 || d > MAXD) {
        best.n = 1;
        best.deg[0] = 0;
        best.side[0] = 0;
        print_graph(&best);
        return 0;
    }
    if (D == 1) {
        single_edge(&best);
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    if (D >= 2 && best.n < moore_bound()) lift_search(&best, t_end);
    if (best.n == 0) complete_bipartite(&best);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D <= 0 or d <= 0:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])
    start = known_start(d, D)
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    if start is not None:
        best = start
    else:
        best = lib.haar_graph(d, range(d))           # K_{d,d}: valid for D >= 2
        if not lib.is_valid(best[0], best[1], d, D):
            best = (2, [(0, 1)])

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
