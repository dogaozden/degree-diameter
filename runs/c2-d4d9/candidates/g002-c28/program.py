"""Haar-first cyclic/metacyclic search for bipartite degree-diameter graphs.

Bold change for this island: the search now starts from Haar graphs (one base vertex
per side, so the lift is a Cayley-type bipartite graph H(G, S) with |S| = d). For a
group acting regularly on each fibre, the diameter test needs only the two base
representatives, so each candidate costs O(N d). That makes many fresh groups and
connection sets affordable. The search then falls back to the parent's mixed-base
voltage lifts and grow-by-two. Every output is checked in C and again in Python, and
K_{d,d} (or a trivial graph for small D) is kept as a fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" then m edge lines, or "0 0".
 * stdout: "n m" then m edge lines, the largest valid graph found.
 *
 * Phases:
 *   1. Haar search: p = 1 voltage lifts over Z_m x|_r Z_k (Cayley-type bipartite graphs).
 *   2. Mixed-base voltage lifts over the same groups (p up to PMAX).
 *   3. Grow by two with annealed degree-preserving swaps.
 * The distance test uses 2p BFS runs from base representatives (group acts regularly).
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
#define PMAX 6

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

/* ------------------------------------------------------------ distance checks */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (exact, bitset based). */
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

static int vis[MAXN];
static int vstamp = 0;
static int qbuf[MAXN];

/* Sum over the 2p base representatives of vertices farther than D.
 * Cost 0 <=> diameter <= D (and connected). */
static long rep_cost(const Graph *g, int p, int N) {
    long cost = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        if (vstamp >= 2000000000) { memset(vis, 0, sizeof vis); vstamp = 0; }
        vstamp++;
        int head = 0, tail = 0;
        vis[src] = vstamp;
        qbuf[tail++] = src;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qbuf[head++];
                for (int i = 0; i < g->deg[v]; i++) {
                    int u = g->adj[v][i];
                    if (vis[u] != vstamp) {
                        vis[u] = vstamp;
                        qbuf[tail++] = u;
                    }
                }
            }
        }
        cost += g->n - tail;
    }
    return cost;
}

/* ------------------------------------------------------------ input / output */

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

static void single_edge(Graph *g) {
    g->n = 2;
    g->deg[0] = g->deg[1] = 0;
    g->side[0] = 0;
    g->side[1] = 1;
    add_edge(g, 0, 1);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a,b) is a*k+b; (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r,m) = 1, r^k = 1 mod m. */
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

/* ------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular base multigraph with p vertices per side, connected. */
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

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Simulated annealing over voltages of one random base over a group of order N.
 * Returns 1 with a valid lift (2pN vertices) in out. */
static int lift_anneal(Graph *out, int p, int N, const Grp *G, long steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXP * MAXD];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            if (M[i][j] > N) return 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(out, p, N, G, dt, nd);
    long cost = rep_cost(out, p, N);
    double T0 = 2.0 + 0.05 * (double)cost, T1 = 0.2;
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(out, p, N, G, dt, nd);
        long nc = rep_cost(out, p, N);
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) cost = nc;
        else dt[t].g = old;
    }
    if (cost != 0) return 0;
    build_lift(out, p, N, G, dt, nd);
    return 1;
}

/* ------------------------------------------------------------ Haar-first search */

/* Haar phase: p = 1 lifts (Cayley-type bipartite graphs H(G,S), |S| = d). Each
 * candidate is cheap, so many fresh groups are tried. Target window adapts to success. */
static void haar_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    double slack = 0.02;
    int fails = 0;
    while (now() < until) {
        long lo = best->n + 2;
        if (lo > moore) break;
        long hi = (long)(best->n * (1.0 + slack)) + 2;
        if (hi > moore) hi = moore;
        if (hi < lo) hi = lo;
        long target = lo + (long)(rnd() % (uint64_t)(hi - lo + 1));
        long N = (target + 1) / 2;   /* order 2N */
        int ok = 0;
        if (N >= d && 2 * N <= moore && 2 * N <= MAXN && random_group((int)N, &G)) {
            long work = 4L * N * d;
            long steps = 300000000L / (work > 0 ? work : 1);
            if (steps < 500) steps = 500;
            if (steps > 200000) steps = 200000;
            if (lift_anneal(&cand, 1, (int)N, &G, steps) && 2 * N > best->n) {
                copy_graph(best, &cand);
                ok = 1;
            }
        }
        if (ok) {
            fails = 0;
            slack *= 1.5;
            if (slack > 0.15) slack = 0.15;
        } else if (++fails >= 25) {
            fails = 0;
            slack *= 0.6;
            if (slack < 0.001) slack = 0.001;
        }
    }
}

/* Mixed-base lift search (p uniform in 1..PMAX). */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    double slack = 0.02;
    int fails = 0;
    while (now() < until) {
        long lo = best->n + 2;
        if (lo > moore) break;
        long hi = (long)(best->n * (1.0 + slack)) + 2;
        if (hi > moore) hi = moore;
        if (hi < lo) hi = lo;
        long target = lo + (long)(rnd() % (uint64_t)(hi - lo + 1));
        int p = 1 + rndint(PMAX);
        long N = (target + 2L * p - 1) / (2L * p);
        long nn = 2L * p * N;
        int ok = 0;
        if (N >= 1 && nn <= moore && nn <= MAXN && random_group((int)N, &G)) {
            long work = 2L * p * nn * d;
            long steps = 300000000L / (work > 0 ? work : 1);
            if (steps < 200) steps = 200;
            if (steps > 100000) steps = 100000;
            if (lift_anneal(&cand, p, (int)N, &G, steps) && nn > best->n) {
                copy_graph(best, &cand);
                ok = 1;
            }
        }
        if (ok) {
            fails = 0;
            slack *= 1.5;
            if (slack > 0.15) slack = 0.15;
        } else if (++fails >= 25) {
            fails = 0;
            slack *= 0.6;
            if (slack < 0.001) slack = 0.001;
        }
    }
}

/* ------------------------------------------------------------ grow by two */

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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("2 1\n0 1\n");
        return 0;
    }

    static Graph best;
    read_start(&best);
    if (best.n == 0) {
        if (D >= 2) complete_bipartite(&best);
        else single_edge(&best);
    }

    if (D >= 2 && best.n < moore_bound()) {
        double total = t_end - t0;
        haar_search(&best, t0 + 0.50 * total);
        if (best.n < moore_bound()) lift_search(&best, t0 + 0.80 * total);
        if (best.n > 0 && best.n < MAXN) grow_search(&best, t_end);
    }

    if (!is_valid(&best)) {
        if (D >= 2) complete_bipartite(&best);
        else single_edge(&best);
    }
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _trivial(d, D):
    """Always-valid fallback graph for (d, D)."""
    if D == 0:
        return (1, [])
    if d >= 1 and D >= 1:
        if D >= 2 and d >= 1:
            # K_{d,d} is valid for D >= 2; use it when it fits the degree bound.
            n, e = lib.haar_graph(d, range(d))
            if lib.is_valid(n, e, d, D):
                return (n, e)
        return (2, [(0, 1)])
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None:
        start = _trivial(d, D)
    best = start
    if not lib.is_valid(best[0], best[1], d, D):
        best = _trivial(d, D)

    if D < 2 or d < 2:
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
