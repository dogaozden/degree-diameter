"""Random-start annealing search for bipartite degree-diameter graphs.

The C engine starts each attempt from a random d-regular bipartite circulant on a
target number of vertices, mixes it with degree-preserving edge switches, then
anneals switches to drive the number of pairs at distance > D to zero. Targets
grow geometrically on success and shrink on failure. The best valid graph found
(or the known construction) is always returned.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: random-start switch annealing.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start), or "0 0".
 * stdout:  "n m" then m lines "u v": best valid graph found.
 *
 * Each attempt at target order N: random d-regular bipartite circulant on N/2+N/2 vertices,
 * mixed by random switches, then simulated annealing on switches minimising the number of
 * vertex pairs at distance > D (bitset BFS). Success moves the target up.
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
#define MAXM (MAXN * MAXD / 2)

static int d, D;
static int n, M;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int EA[MAXM], EB[MAXM];          /* edge list: EA in part A (ids < n/2 for circulants), EB in part B */
static int bEA[MAXM], bEB[MAXM], bestN = 0, bestM = 0;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

static int has_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void repl(int u, int old, int nw) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == old) {
            adj[u][i] = nw;
            return;
        }
}

static void add_edge_list(int a, int b) {
    EA[M] = a;
    EB[M] = b;
    M++;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

/* Pairs at distance > D (unordered), and per-vertex counts in badv[]. */
static long bad_pairs(void) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
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
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

/* Random-start graph: h + h vertices, d-regular circulant between the parts. */
static void build_circulant(int h) {
    n = 2 * h;
    M = 0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < h; i++)
        for (int s = 0; s < d; s++) add_edge_list(i, h + (i + s) % h);
}

static int valid_switch(int e1, int e2) {
    int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
    return a1 != a2 && b1 != b2 && !has_nb(a1, b2) && !has_nb(a2, b1);
}

/* Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Applying it twice restores the state. */
static void apply_switch(int e1, int e2) {
    int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    EB[e1] = b2;
    EB[e2] = b1;
}

static void mix(void) {
    long lim = 20L * M;
    for (long k = 0; k < lim; k++) {
        int e1 = rndint(M), e2 = rndint(M);
        if (valid_switch(e1, e2)) apply_switch(e1, e2);
    }
}

/* Simulated annealing on switches until zero bad pairs (returns 1) or time runs out (returns 0). */
static int anneal(double until) {
    long cur = bad_pairs();
    if (cur == 0) return 1;
    double T = 2.0;
    for (long it = 1;; it++) {
        if ((it & 7) == 0 && now() > until) return 0;
        int e1 = rndint(M);
        for (int t = 0; t < 20 && badv[EA[e1]] == 0 && badv[EB[e1]] == 0; t++) e1 = rndint(M);
        int e2 = rndint(M);
        if (!valid_switch(e1, e2)) continue;
        apply_switch(e1, e2);
        long nb = bad_pairs();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
            cur = nb;
        } else {
            apply_switch(e1, e2);
        }
        if (cur == 0) return 1;
        T *= 0.9995;
        if (T < 0.3) T = 2.0;
    }
}

static void save_best(void) {
    bestN = n;
    bestM = M;
    memcpy(bEA, EA, sizeof(int) * M);
    memcpy(bEB, EB, sizeof(int) * M);
}

/* Read "n m" + edges, 2-colour, and keep it only if it is valid. */
static int read_start(void) {
    int nn, mm;
    if (scanf("%d %d", &nn, &mm) != 2) return 0;
    if (nn <= 0 || nn > MAXN || mm < 0 || mm > MAXM) return 0;
    n = nn;
    M = 0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    static int U[MAXM], V[MAXM], col[MAXN], q[MAXN];
    for (int e = 0; e < mm; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d || has_nb(u, v)) return 0;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        U[e] = u;
        V[e] = v;
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (col[u] == -1) {
                    col[u] = 1 - col[v];
                    q[tail++] = u;
                } else if (col[u] == col[v]) {
                    return 0;
                }
            }
        }
    }
    for (int e = 0; e < mm; e++) {
        if (col[U[e]] == 0) {
            EA[e] = U[e];
            EB[e] = V[e];
        } else {
            EA[e] = V[e];
            EB[e] = U[e];
        }
    }
    M = mm;
    return bad_pairs() == 0;
}

static void print_best(void) {
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bEA[i], bEB[i]);
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
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (read_start()) {
        save_best();
    } else {
        build_circulant(d);              /* K_{d,d} */
        if (bad_pairs() == 0) save_best();
    }

    if (D >= 2) {
        int lo = bestN, step = 2;
        long moore = moore_bound();
        while (now() < t_end) {
            long target = (long)lo + step;
            if (target < 2L * d) target = 2L * d;
            if (target & 1) target++;
            if (target > moore || target > MAXN) {
                if (step <= 2) break;
                step /= 2;
                continue;
            }
            double left = t_end - now();
            double slice = left / 3.0;
            if (slice < 3.0) slice = left;
            build_circulant((int)(target / 2));
            mix();
            if (anneal(now() + slice)) {
                save_best();
                lo = (int)target;
                if (step < (1 << 20)) step *= 2;
            } else {
                if (step > 2) step /= 2;
            }
        }
    }
    print_best();
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
    if start is None:
        start = lib.haar_graph(d, range(d))           # K_{d,d}: valid for D >= 2
    best = start
    if not lib.is_valid(*best, d, D):
        best = lib.haar_graph(d, range(d))
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start,
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
