"""Haar-graph difference-cover search for the bipartite degree-diameter problem.

Construction: for a group G of order m and a d-subset S of G, the Haar graph joins
a_x to b_{x*s} for s in S. It is d-regular and bipartite on 2m vertices. Left
multiplication is an automorphism, so the diameter is at most 3 exactly when
  S S^-1 and S^-1 S both cover G \\ {e}, and S + S S^-1 S covers G.
C runs simulated annealing over S, using cyclic and semidirect groups of growing
order m. It keeps the largest valid graph. Fallbacks (start graph, K_{d,d}, one
edge) are all checked with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Haar-graph difference-cover search for bipartite degree-diameter graphs.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start graph), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * For D >= 3 and a group G of order m, pick S (d distinct elements). The Haar graph
 * has A-vertex x adjacent to B-vertex x*s for s in S. It is valid with diameter <= 3
 * when S S^-1 and S^-1 S cover G\{e}, and S u S S^-1 S covers G.
 * Simulated annealing minimises the number of uncovered elements, over random groups
 * Z_m or Z_m x| Z_k (any order m). Orders m are tried in increasing order.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXM 512

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (0 means diameter <= D, connected). */
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

/* Full validity: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* Read "n m" + edges from stdin and 2-colour. Leaves g->n = 0 if absent or invalid. */
static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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
                if (g->side[u] == 255) {
                    g->side[u] = 1 - g->side[v];
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

/* K_{d,d}: valid for D >= 2 (requires d <= MAXD). */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* A single edge: valid for D >= 1 and d >= 1. */
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
    int rp[MAXM]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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
                G->m = m;
                G->k = k;
                G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------------ Haar / difference covers */

static int MT[MAXM][MAXM]; /* multiplication table of the current group */
static int IV[MAXM];       /* inverses */
static int gm;             /* current group order */
static int HS[MAXD];       /* connection set S: d distinct group elements */
static unsigned char inS[MAXM];
static int mk1[MAXM], mk2[MAXM], mk3[MAXM];
static int stamp_ctr;

static void build_tables(const Grp *G, int m) {
    gm = m;
    for (int x = 0; x < m; x++)
        for (int y = 0; y < m; y++) MT[x][y] = gmul(G, x, y);
    for (int x = 0; x < m; x++)
        for (int y = 0; y < m; y++)
            if (MT[x][y] == 0) { IV[x] = y; break; }
}

/* Number of uncovered elements: non-identity g outside S S^-1, non-identity g outside
 * S^-1 S, and g outside S u S S^-1 S. Zero means the Haar graph has diameter <= 3. */
static int cover_cost(void) {
    int st = ++stamp_ctr;
    int m = gm;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            mk1[MT[HS[i]][IV[HS[j]]]] = st;   /* s t^-1 */
            mk2[MT[IV[HS[i]]][HS[j]]] = st;   /* s^-1 t */
        }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int q = MT[HS[i]][IV[HS[j]]];
            for (int k = 0; k < d; k++) mk3[MT[q][HS[k]]] = st;
        }
    for (int k = 0; k < d; k++) mk3[HS[k]] = st;
    int c = 0;
    for (int g = 1; g < m; g++) {
        if (mk1[g] != st) c++;
        if (mk2[g] != st) c++;
    }
    for (int g = 0; g < m; g++)
        if (mk3[g] != st) c++;
    return c;
}

/* Annealing over S for random groups of order m, until a zero-cost S is found or time runs out.
 * On success HS holds S and MT/IV hold its group tables. */
static int find_haar(int m, double until) {
    static Grp G;
    while (now() < until) {
        if (!random_group(m, &G)) return 0;
        build_tables(&G, m);
        for (int k = 0; k < d; k++) inS[HS[k]] = 0;
        for (int k = 0; k < d; k++) {
            int g;
            do g = rndint(m); while (inS[g]);
            HS[k] = g;
            inS[g] = 1;
        }
        int cur = cover_cost();
        const long iters = 300000;
        double T = 1.5;
        for (long it = 0; it < iters && cur > 0; it++) {
            if ((it & 255) == 0) {
                if (now() > until) break;
                T = 1.5 * pow(0.03, (double)it / (double)iters);
            }
            int i = rndint(d);
            int g = rndint(m);
            if (inS[g]) continue;
            int old = HS[i];
            inS[old] = 0;
            HS[i] = g;
            inS[g] = 1;
            int nc = cover_cost();
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
                cur = nc;
            } else {
                inS[g] = 0;
                HS[i] = old;
                inS[old] = 1;
            }
        }
        if (cur == 0) return 1;
    }
    return 0;
}

/* Haar graph of the current group and HS: 2m vertices, A = 0..m-1, B = m..2m-1. */
static void build_haar(Graph *g, int m) {
    g->n = 2 * m;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= m; }
    for (int x = 0; x < m; x++)
        for (int k = 0; k < d; k++) add_edge(g, x, m + MT[x][HS[k]]);
}

/* Try orders m = best/2 + 1, +1, ...; keep every valid Haar graph that beats best. */
static void haar_search(Graph *best, double until) {
    static Graph cand;
    long mmax = moore_bound() / 2;
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    if (mmax > MAXN / 2) mmax = MAXN / 2;
    long m = best->n / 2 + 1;
    if (m <= d) m = d + 1;
    while (now() < until && m <= mmax) {
        if (!find_haar((int)m, until)) break;
        build_haar(&cand, (int)m);
        if (is_valid(&cand) && cand.n > best->n) copy_graph(best, &cand);
        m++;
        if (m < best->n / 2 + 1) m = best->n / 2 + 1;
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

    if (d < 1 || D < 1) {
        printf("1 0\n");
        return 0;
    }

    static Graph best;
    if (d <= MAXD) read_start(&best);
    else best.n = 0;

    if (best.n == 0) {
        if (D >= 2 && d <= MAXD) complete_bipartite(&best);
        else single_edge(&best);
    }
    if (D >= 3 && d <= MAXD && best.n < moore_bound()) haar_search(&best, t_end);
    if (!is_valid(&best)) single_edge(&best);
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

    # Safe fallback chain: every candidate is checked before it can be returned.
    best = None
    for cand in (start, lib.haar_graph(d, range(d)), (2, [(0, 1)])):
        if cand is None:
            continue
        n, edges = cand
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            break
    if best is None:
        return (1, [])

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the valid fallback
    return best
