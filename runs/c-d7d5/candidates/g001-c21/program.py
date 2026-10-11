"""Lift search with an exact fiber-source diameter test.

Each candidate is a voltage lift of a d-regular bipartite base multigraph with p vertices
per side over a semidirect product Z_m x| Z_k. Left multiplication by the group is an
automorphism that fixes each fiber, so the diameter test only needs BFS from the 2p fiber
identities (A_i, e) and (B_j, e). That replaces the all-pairs bitset check in the inner loop.
Annealing moves change voltages and also the base multigraph (swapping B-endpoints of two
darts, which keeps every degree). The objective is the number of (source, vertex) pairs
farther than D. The final graph is checked with the full bitset validator before it is kept.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: voltage lifts over semidirect products Z_m x| Z_k.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (a valid start graph), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Method: a lift with P base vertices per side over group G (order GO) has 2*P*GO vertices.
 * Left multiplication by G is an automorphism that fixes each fibre, so the diameter is
 * <= D iff BFS from (A_i, e) and (B_j, e) reaches everything within D steps. The objective
 * for annealing is the number of unreached (source, vertex) pairs over these 2P sources.
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
#define MAXG 2048
#define MAXND (MAXP * MAXD)

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

/* Number of unordered pairs at distance > D (0 means diameter <= D). Bitset version,
 * used only for final validation of candidates. */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Group Z_m x| Z_k with r^k = 1 mod m. Element (a,b) is a*k+b.
 * (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Identity is 0. */
static int GM, GK, GO;
static int GRP[MAXG]; /* GRP[b] = r^b mod m */

static int random_group(int N, int *om, int *ok, int *orr) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { *om = m; *ok = k; *orr = r; }
        }
    }
    return count > 0;
}

static void build_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GO = m * k;
    GRP[0] = 1 % m;
    for (int b = 1; b < k; b++) GRP[b] = (int)((long)GRP[b - 1] * r % m);
}

static int mulf(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)((a + (long)GRP[b] * c) % GM) * GK + (b + e) % GK;
}

/* (a,b)^{-1} = (-r^{-b} a, -b). */
static int invf(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (GM - (int)((long)GRP[nb] * a % GM)) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------------ lifts */

static int P, ND;
static int DI[MAXND], DJ[MAXND], DG[MAXND];   /* dart t: A_{DI} -> B_{DJ} with voltage DG */
static int LISTB[MAXP][MAXD], NLB[MAXP];      /* darts ending at each B vertex */
static int RR[MAXND][MAXG];                   /* RR[t][x] = x * g_t */
static int RI[MAXND][MAXG];                   /* RI[t][y] = y * g_t^{-1} */

static void set_tables(int t) {
    int g = DG[t], gi = invf(g);
    for (int x = 0; x < GO; x++) {
        RR[t][x] = mulf(x, g);
        RI[t][x] = mulf(x, gi);
    }
}

static void rebuild_lists(void) {
    for (int j = 0; j < P; j++) NLB[j] = 0;
    for (int t = 0; t < ND; t++) LISTB[DJ[t]][NLB[DJ[t]]++] = t;
}

/* Two darts from the same A vertex with the same end and voltage would give a multi-edge. */
static int clash_t(int t) {
    int base = DI[t] * d;
    for (int s = base; s < base + d; s++)
        if (s != t && DJ[s] == DJ[t] && DG[s] == DG[t]) return 1;
    return 0;
}

static void swap_j(int t, int s) {
    int a = DJ[t];
    DJ[t] = DJ[s];
    DJ[s] = a;
}

/* Random base: d permutation matrices on p+p vertices, so every vertex has degree d. */
static int init_lift(int p) {
    P = p;
    ND = p * d;
    for (int k = 0; k < d; k++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            DI[i * d + k] = i;
            DJ[i * d + k] = perm[i];
        }
    }
    for (int t = 0; t < ND; t++) DG[t] = rndint(GO);
    for (int pass = 0; pass < 500; pass++) {
        int any = 0;
        for (int t = 0; t < ND; t++)
            if (clash_t(t)) { DG[t] = rndint(GO); any = 1; }
        if (!any) break;
    }
    for (int t = 0; t < ND; t++)
        if (clash_t(t)) return 0;
    for (int t = 0; t < ND; t++) set_tables(t);
    rebuild_lists();
    return 1;
}

/* BFS from one vertex, counting vertices within distance D. Vertex v < P*GO is A, else B. */
static unsigned VIS[MAXN];
static unsigned STAMP = 0;
static int QB[MAXN];

static int bfs_reach(int src) {
    int PN = P * GO;
    STAMP++;
    int head = 0, tail = 0, cnt = 1;
    VIS[src] = STAMP;
    QB[tail++] = src;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int end = tail;
        while (head < end) {
            int v = QB[head++];
            if (v < PN) {
                int i = v / GO, x = v - i * GO;
                for (int kk = 0; kk < d; kk++) {
                    int t = i * d + kk;
                    int u = PN + DJ[t] * GO + RR[t][x];
                    if (VIS[u] != STAMP) { VIS[u] = STAMP; QB[tail++] = u; cnt++; }
                }
            } else {
                int w = v - PN, j = w / GO, y = w - j * GO;
                for (int c = 0; c < NLB[j]; c++) {
                    int t = LISTB[j][c];
                    int u = DI[t] * GO + RI[t][y];
                    if (VIS[u] != STAMP) { VIS[u] = STAMP; QB[tail++] = u; cnt++; }
                }
            }
        }
    }
    return cnt;
}

/* Objective: unreached (source, vertex) pairs from the 2P fibre identities. 0 iff diameter <= D. */
static long eval_bad(void) {
    int n = 2 * P * GO;
    long bad = 0;
    for (int i = 0; i < P; i++) bad += n - bfs_reach(i * GO);
    for (int j = 0; j < P; j++) bad += n - bfs_reach(P * GO + j * GO);
    return bad;
}

static long steps_for(int n) {
    long s = 20000000L / (n > 0 ? n : 1);
    if (s < 3000) s = 3000;
    if (s > 2000000) s = 2000000;
    return s;
}

/* Simulated annealing over voltages and base B-endpoints. Returns 1 if a valid lift was reached. */
static int anneal(long steps) {
    long bad = eval_bad();
    if (bad == 0) return 1;
    for (long s = 0; s < steps; s++) {
        if ((s & 127) == 0 && now() > t_end) break;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.1;
        int t = rndint(ND);
        if (P > 1 && rnd01() < 0.15) {
            int t2 = rndint(ND);
            if (DI[t2] == DI[t]) continue;
            swap_j(t, t2);
            rebuild_lists();
            if (clash_t(t) || clash_t(t2)) {
                swap_j(t, t2);
                rebuild_lists();
                continue;
            }
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) {
                bad = nb;
            } else {
                swap_j(t, t2);
                rebuild_lists();
            }
        } else {
            int old = DG[t];
            int g = rndint(GO);
            if (g == old) continue;
            DG[t] = g;
            if (clash_t(t)) { DG[t] = old; continue; }
            set_tables(t);
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) {
                bad = nb;
            } else {
                DG[t] = old;
                set_tables(t);
            }
        }
        if (bad == 0) return 1;
    }
    return bad == 0;
}

static void build_graph(Graph *g) {
    int PN = P * GO;
    g->n = 2 * PN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= PN; }
    for (int i = 0; i < P; i++)
        for (int x = 0; x < GO; x++)
            for (int kk = 0; kk < d; kk++) {
                int t = i * d + kk;
                int u = PN + DJ[t] * GO + RR[t][x];
                add_edge(g, i * GO + x, u);
            }
}

/* Repeatedly pick a random group and base of order about best->n / 2p + 1, anneal, and
 * keep any valid lift that beats best. */
static void lift_search(Graph *best) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < t_end) {
        int bn = best->n;
        if (bn >= moore) return;
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        int N = bn / (2 * p) + 1;
        if (rndint(4) == 0) N++;
        if (N < d) N = d;
        if (2L * p * N > moore || 2 * p * N > MAXN || N > MAXG) {
            if (++fails > 5000) return;
            continue;
        }
        int m, k, rr;
        if (!random_group(N, &m, &k, &rr)) {
            if (++fails > 5000) return;
            continue;
        }
        build_group(m, k, rr);
        if (!init_lift(p)) continue;
        if (anneal(steps_for(2 * p * N))) {
            build_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) *best = cand;
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

    static Graph best;
    if (d < 1 || d > MAXD || D < 1) {
        best.n = 1;
        best.deg[0] = 0;
        best.side[0] = 0;
        print_graph(&best);
        return 0;
    }
    if (D == 1) {
        best.n = 2;
        best.deg[0] = best.deg[1] = 0;
        best.side[0] = 0;
        best.side[1] = 1;
        add_edge(&best, 0, 1);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore_bound()) lift_search(&best);
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


def _trivial(d, D):
    """Always-valid fallback graph."""
    if D >= 2 and d >= 1:
        return lib.haar_graph(d, range(d))             # K_{d,d}, diameter 2
    if D >= 1 and d >= 1:
        return (2, [(0, 1)])
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    best = start if start is not None else _trivial(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    if best[0] >= lib.moore_bound(d, D):
        return best   # a Moore graph cannot be beaten
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, int(seed), round(budget, 2)],
                             stdin_graph=start, timeout=budget + 3)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
