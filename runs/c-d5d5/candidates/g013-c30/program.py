"""Grow-and-anneal engine for bipartite degree-diameter graphs.

Replaces the lift search with a different construction: start from a valid
d-regular bipartite graph (K_{d,d}, or a regular valid start from Python), then
repeatedly add one vertex per side by stealing a matching of d edges, and repair
the diameter defect with degree-preserving 2-switch simulated annealing. Every
accepted state is d-regular, simple and bipartite by construction and is checked
for diameter before it is kept. Python keeps the largest valid graph among its
constructions and the C output, so a valid graph is always returned.
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

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXD 16

static int d, D;
static long moore;
static int n;                       /* current vertex count */
static int side[MAXN];              /* 0 / 1 bipartition */
static int adj[MAXN][MAXD];         /* d-regular adjacency */

static int bestn;                   /* best valid state */
static int bside[MAXN];
static int badj[MAXN][MAXD];

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int lm_a, lm_b, lm_c, lm_e;  /* last applied switch, for undo */

static int used[MAXN];
static int stamp = 0;

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

static long compute_moore(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < d; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

/* Replace neighbour `old` of v by `nw`. */
static void rep(int v, int old, int nw) {
    for (int i = 0; i < d; i++)
        if (adj[v][i] == old) { adj[v][i] = nw; return; }
}

/* Number of unordered pairs at distance > D (bitset BFS, D rounds). */
static long bad_pairs(void) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < d; i++) {
                const uint64_t *s = cur + (size_t)adj[v][i] * W;
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

/* Full validity of the current state: simple, bipartite, degree d, diameter <= D. */
static int is_valid_state(void) {
    if (n < 2 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < d; i++) {
            int u = adj[v][i];
            if (u < 0 || u >= n || u == v || side[u] == side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (adj[v][j] == u) return 0;
        }
    }
    return bad_pairs() == 0;
}

static void save_best(void) {
    bestn = n;
    memcpy(bside, side, sizeof side);
    memcpy(badj, adj, sizeof adj);
}

static void restore_best(void) {
    n = bestn;
    memcpy(side, bside, sizeof side);
    memcpy(adj, badj, sizeof adj);
}

/* K_{d,d} as the default regular start. */
static void make_k(void) {
    n = 2 * d;
    for (int v = 0; v < n; v++) side[v] = v >= d;
    for (int a = 0; a < d; a++)
        for (int i = 0; i < d; i++) {
            adj[a][i] = d + i;
            adj[d + i][a] = a;
        }
}

/* Read "n m" + edges; accept only a d-regular, bipartite, valid graph. */
static int read_start(void) {
    static int deg[MAXN];
    static int queue[MAXN];
    int nn, mm;
    if (scanf("%d %d", &nn, &mm) != 2) return 0;
    if (nn < 2 || nn > MAXN - 2 || mm < 0) return 0;
    for (int v = 0; v < nn; v++) deg[v] = 0;
    for (int e = 0; e < mm; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= nn || v >= nn || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d) return 0;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    for (int v = 0; v < nn; v++)
        if (deg[v] != d) return 0;
    n = nn;
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        int head = 0, tail = 0;
        side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < d; i++) {
                int u = adj[v][i];
                if (side[u] == -1) { side[u] = 1 - side[v]; queue[tail++] = u; }
                else if (side[u] == side[v]) return 0;
            }
        }
    }
    return is_valid_state();
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b), a,c on one side. */
static int try_switch(void) {
    int a = rndint(n), c = rndint(n);
    if (c == a || side[c] != side[a]) return 0;
    int b = adj[a][rndint(d)];
    int e = adj[c][rndint(d)];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    rep(a, b, e);
    rep(b, a, c);
    rep(c, e, b);
    rep(e, c, a);
    lm_a = a; lm_b = b; lm_c = c; lm_e = e;
    return 1;
}

static void undo_switch(void) {
    int a = lm_a, b = lm_b, c = lm_c, e = lm_e;
    rep(a, e, b);
    rep(e, a, c);
    rep(c, b, e);
    rep(b, c, a);
}

/* Add one vertex per side (x in side 0, y in side 1), stealing a matching of d
   edges: each stolen edge (a,b) becomes (a,y) and (b,x). Degrees stay d. */
static int grow_step(void) {
    int x = n, y = n + 1, cx = 0, cy = 0, tries = 0;
    stamp++;
    side[x] = 0;
    side[y] = 1;
    while (cx < d && tries < 200000) {
        tries++;
        int a = rndint(n);
        if (side[a] != 0 || used[a] == stamp) continue;
        int b = adj[a][rndint(d)];
        if (used[b] == stamp) continue;
        used[a] = stamp;
        used[b] = stamp;
        rep(a, b, y);
        rep(b, a, x);
        adj[x][cx++] = b;
        adj[y][cy++] = a;
    }
    if (cx != d || cy != d) return 0;
    n += 2;
    return 1;
}

/* Simulated annealing on the number of bad pairs. Returns 1 if reached 0. */
static int anneal(double until) {
    long cur = bad_pairs();
    double T = 0.8;
    for (long it = 0; cur > 0; it++) {
        if ((it & 127) == 0 && now() > until) return 0;
        if (!try_switch()) continue;
        long nb = bad_pairs();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
        else undo_switch();
        T *= 0.9995;
        if (T < 0.1) T = 0.8;
    }
    return 1;
}

/* Repeatedly grow the best valid state by two vertices and anneal the defect away. */
static void search(double until) {
    int fails = 0;
    while (now() < until) {
        if (bestn + 2 > moore || bestn + 2 > MAXN) break;
        restore_best();
        if (!grow_step()) { fails++; continue; }
        double slice = 1.0 + 0.5 * fails;
        if (slice > 12.0) slice = 12.0;
        double lim = now() + slice;
        if (lim > until) lim = until;
        if (anneal(lim) && is_valid_state()) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }
}

static void print_graph(void) {
    long m = (long)n * d / 2;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < d; i++)
            if (u < adj[u][i]) printf("%d %d\n", u, adj[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    if (!read_start()) make_k();
    save_best();
    if (bestn + 2 <= moore) search(t0 + limit * 0.95);

    restore_best();
    if (!is_valid_state()) make_k();
    print_graph();
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    consider(_known_start(d, D))

    if D < 2 or d < 3 or d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
