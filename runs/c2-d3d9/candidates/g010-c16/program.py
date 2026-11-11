"""Starter program: Python builds the best known start graph, the C engine searches from it.

Most improvements belong in C_SOURCE (it runs 10-100x faster than Python).
build() keeps the best valid graph it has, so a broken idea in C can only cost time.

This version replaces the cyclic and metacyclic Cayley phase with voltage lifts of small
base graphs (P vertices per side, d-regular) over metacyclic groups Z_m x|_r Z_k. Validity is
checked by only 2P BFS runs from base vertices, since left multiplication by the group is an
automorphism that is transitive on each fibre. That is far cheaper than the full bitset
distance check, so the hill-climb can test hundreds of thousands of voltage assignments.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search:
 *   1. Voltage lifts. A base graph has P vertices per side and is d-regular (d
 *      permutation layers). Darts (i, j, g) join A(i,x) to B(j, x*g) in a group G of
 *      order N = m*k (metacyclic Z_m x| Z_k). Left multiplication is an automorphism,
 *      so the lift has diameter <= D iff every base vertex reaches all 2PN vertices
 *      within D steps. That is 2P BFS runs. Hill-climb moves change one voltage or swap
 *      two targets inside one layer, minimising the number of unreached (source, vertex)
 *      pairs.
 *   2. Grow by two: insert one vertex per side and anneal edge swaps until diameter <= D.
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
#define MAXP 6
#define GMAX 1024
#define MAXDARTS (MAXD * MAXP)
#define MAXV (2 * MAXP * GMAX)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

static int d, D;
static double t_end;
static double stop_at;

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* vertices farther than D from v, set by bad_pairs() */

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
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

/* Read "n m" + edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int cmul[GMAX][GMAX];
static int cinv[GMAX];
static int NG;   /* current group order */
static int P;    /* base vertices per side */

static int build_group(int m, int k, int r) {
    int N = m * k;
    if (N < 1 || N > GMAX) return 0;
    int rp[GMAX];
    for (int b = 0; b < k; b++) rp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            cmul[x][y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (cmul[x][y] == 0) { cinv[x] = y; break; }
    NG = N;
    return 1;
}

static int gm_list[4096], gk_list[4096], gr_list[4096];

/* All metacyclic groups of order N (as (m, k, r) triples). Returns the count. */
static int enum_groups(int N) {
    int G = 0;
    for (int m = 1; m <= N && G < 4000; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            gm_list[G] = 1; gk_list[G] = k; gr_list[G] = 0; G++;
            continue;
        }
        for (int r = 1; r < m && G < 4000; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            gm_list[G] = m; gk_list[G] = k; gr_list[G] = r; G++;
        }
    }
    return G;
}

/* ------------------------------------------------------------------ voltage lifts */

/* Dart t: base A-vertex di[t] -> base B-vertex dj[t] with voltage dg[t].
 * Layer t (darts t*P .. t*P+P-1) is a permutation, so the base is d-regular. */
static int di[MAXDARTS], dj[MAXDARTS], dg[MAXDARTS];
static int nd;
static int outA[MAXP][MAXD], inB[MAXP][MAXD];

static void index_darts(void) {
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        outA[di[t]][ca[di[t]]++] = t;
        inB[dj[t]][cb[dj[t]]++] = t;
    }
}

/* 1 if dart t duplicates another dart (same base pair and same voltage). */
static int clash_dart(int t) {
    for (int u = 0; u < nd; u++)
        if (u != t && di[u] == di[t] && dj[u] == dj[t] && dg[u] == dg[t]) return 1;
    return 0;
}

static int fix_clashes(void) {
    for (int tries = 0; tries < 2000; tries++) {
        int bad = -1;
        for (int t = 0; t < nd && bad < 0; t++)
            if (clash_dart(t)) bad = t;
        if (bad < 0) return 1;
        dg[bad] = rndint(NG);
    }
    return 0;
}

static void random_darts(void) {
    nd = d * P;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < P; i++) {
            int idx = t * P + i;
            di[idx] = i;
            dj[idx] = perm[i];
            dg[idx] = rndint(NG);
        }
    }
}

static int dist[MAXV], qbuf[MAXV];

/* Sum over the 2P base vertices of the number of lift vertices NOT within D of it.
 * Zero means the lift has diameter <= D (by transitivity of left multiplication). */
static long lift_cost(void) {
    int V = 2 * P * NG, PN = P * NG;
    long miss = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = s * NG;
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        qbuf[tail++] = src;
        while (head < tail) {
            int v = qbuf[head++];
            if (dist[v] >= D) continue;
            if (v < PN) {
                int i = v / NG, x = v % NG;
                for (int q = 0; q < d; q++) {
                    int t = outA[i][q];
                    int u = PN + dj[t] * NG + cmul[x][dg[t]];
                    if (dist[u] < 0) { dist[u] = dist[v] + 1; qbuf[tail++] = u; }
                }
            } else {
                int w = v - PN, j = w / NG, y = w % NG;
                for (int q = 0; q < d; q++) {
                    int t = inB[j][q];
                    int u = di[t] * NG + cmul[y][cinv[dg[t]]];
                    if (dist[u] < 0) { dist[u] = dist[v] + 1; qbuf[tail++] = u; }
                }
            }
        }
        miss += V - tail;
    }
    return miss;
}

static void build_lift_graph(Graph *g) {
    int PN = P * NG;
    g->n = 2 * PN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= PN; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NG; x++)
            add_edge(g, di[t] * NG + x, PN + dj[t] * NG + cmul[x][dg[t]]);
}

/* Hill-climb over voltages and layer targets. Returns 1 if the lift reaches cost 0. */
static int lift_climb(int steps) {
    long cur = lift_cost();
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 63) == 0 && now() > stop_at) return 0;
        if (rndint(10) < 7) {
            int t = rndint(nd);
            int old = dg[t];
            dg[t] = rndint(NG);
            if (clash_dart(t)) { dg[t] = old; continue; }
            long c = lift_cost();
            if (c <= cur || rnd01() < 0.01) cur = c;
            else dg[t] = old;
        } else {
            if (P < 2) continue;
            int t = rndint(d), a = rndint(P), b = rndint(P);
            if (a == b) continue;
            int ia = t * P + a, ib = t * P + b;
            int tmp = dj[ia]; dj[ia] = dj[ib]; dj[ib] = tmp;
            if (clash_dart(ia) || clash_dart(ib)) {
                tmp = dj[ia]; dj[ia] = dj[ib]; dj[ib] = tmp;
                continue;
            }
            index_darts();
            long c = lift_cost();
            if (c <= cur || rnd01() < 0.01) cur = c;
            else {
                tmp = dj[ia]; dj[ia] = dj[ib]; dj[ib] = tmp;
                index_darts();
            }
        }
    }
    return cur == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    stop_at = until;
    while (now() < until) {
        long T = best->n + 2;
        if (T > moore) return;
        int p = 1 + rndint(MAXP);
        long Nlo = (T + 2L * p - 1) / (2L * p);
        long N = Nlo + rndint(2 + rndint(8));
        if (N < d) N = d;
        if (N > GMAX || 2L * p * N > moore || 2L * p * N > MAXN) continue;
        int cnt = enum_groups((int)N);
        if (cnt == 0) continue;
        int gi = rndint(cnt);
        P = p;
        if (!build_group(gm_list[gi], gk_list[gi], gr_list[gi])) continue;
        random_darts();
        if (!fix_clashes()) continue;
        index_darts();
        if (lift_climb(4000)) {
            build_lift_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Insert one new vertex per side into a copy of best (degree d each), then anneal edge swaps.
 * Returns 1 if the work graph ends valid with best->n + 2 vertices. */
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
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
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
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (d >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
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
    if d < 1 or D < 1:
        return (1, [])

    # Safe fallbacks: every candidate is checked, the largest valid one is kept.
    best = None
    start = known_start(d, D)
    pool = ([start] if start is not None else []) + [
        lib.haar_graph(d, range(d)),   # K_{d,d}, valid for D >= 2
        (2, [(0, 1)]),                 # K_2, valid for any D >= 1
    ]
    for cand in pool:
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (best is None or cand[0] > best[0]):
            best = cand
    if best is None:
        return (1, [])

    moore = lib.moore_bound(d, D)
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= moore:
        budget = 0.0   # already a Moore graph: nothing to search for
    if budget > 0.5 and D >= 2:
        budget = round(budget, 2)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=best,
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
