"""Bipartite degree-diameter search, second engine.

Idea: keep the vertex count fixed at a target n and anneal over degree-preserving
edge swaps (a1-b1, a2-b2 -> a1-b2, a2-b1) to drive the number of pairs at distance
greater than D to zero. Starts are either a padded copy of the best graph (two new
vertices wired in with the spare degree) or a random circulant (Haar) graph.
Each success raises the target by two. Python keeps a validated fallback throughout.
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

#define MAXN 512
#define MAXD 16
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;
static Graph best;

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
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

/* ------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= d || g->deg[v] >= d || has_edge(g, u, v)) {
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

/* Always-valid fallback: K_{d,d} when D >= 2 (d <= MAXD), else a single edge. */
static void set_fallback(Graph *g) {
    memset(g, 0, sizeof *g);
    if (D >= 2 && d >= 1 && d <= MAXD) {
        g->n = 2 * d;
        for (int v = 0; v < g->n; v++) g->side[v] = v >= d;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) add_edge(g, a, d + b);
    } else {
        g->n = 2;
        g->side[0] = 0;
        g->side[1] = 1;
        add_edge(g, 0, 1);
    }
}

/* ------------------------------------------------------------ starts */

static int balanced(const Graph *g) {
    int c0 = 0;
    for (int v = 0; v < g->n; v++) c0 += g->side[v] == 0;
    return g->n % 2 == 0 && 2 * c0 == g->n;
}

/* Haar graph H(N, S) with N = n/2 and d distinct shifts: d-regular, simple, bipartite. */
static void circulant_start(Graph *g, int n) {
    int N = n / 2;
    int S[MAXD], cnt = 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    while (cnt < d) {
        int s = rndint(N), ok = 1;
        for (int i = 0; i < cnt; i++)
            if (S[i] == s) ok = 0;
        if (ok) S[cnt++] = s;
    }
    for (int a = 0; a < N; a++)
        for (int t = 0; t < d; t++) add_edge(g, a, N + (a + S[t]) % N);
}

/* Two new vertices x (side 0) and y (side 1), joined to each other and given
 * d-1 more edges each by splitting existing edges (a,b) -> (x,b), (y,a). */
static void padded_start(Graph *g, const Graph *src) {
    int n = src->n;
    copy_graph(g, src);
    int x = n, y = n + 1;
    g->n = n + 2;
    g->deg[x] = g->deg[y] = 0;
    g->side[x] = 0;
    g->side[y] = 1;
    add_edge(g, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (g->side[a] != 0 || used[a] == stamp || g->deg[a] == 0) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(g, a, b);
        add_edge(g, x, b);
        add_edge(g, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

/* ------------------------------------------------------------ annealing */

static int pick_side0(const Graph *g) {
    int a;
    do a = rndint(g->n); while (g->side[a] != 0);
    return a;
}

/* Degree-preserving A-B edge swaps, cost = bad pairs, geometric cooling.
 * Returns the final cost (0 means a valid diameter-D graph was reached). */
static long anneal(Graph *g, long iters, double T0, double T1) {
    long cur = bad_pairs(g);
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 1023) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a1 = pick_side0(g), a2 = pick_side0(g);
        if (a1 == a2 || g->deg[a1] == 0 || g->deg[a2] == 0) continue;
        int b1 = g->adj[a1][rndint(g->deg[a1])];
        int b2 = g->adj[a2][rndint(g->deg[a2])];
        if (b1 == b2 || has_edge(g, a1, b2) || has_edge(g, a2, b1)) continue;
        del_edge(g, a1, b1);
        del_edge(g, a2, b2);
        add_edge(g, a1, b2);
        add_edge(g, a2, b1);
        long nc = bad_pairs(g);
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            del_edge(g, a1, b2);
            del_edge(g, a2, b1);
            add_edge(g, a1, b1);
            add_edge(g, a2, b2);
        }
    }
    return cur;
}

/* Raise the target order by two while annealing succeeds. */
static void search(void) {
    long moore = moore_bound();
    static Graph cur;
    while (now() < t_end) {
        long target = best.n > 0 ? best.n + 2 : 2L * d;
        if (target > moore || target > MAXN) break;
        int n = (int)target;
        if (n / 2 < d) n = 2 * d;
        if (n > moore || n > MAXN) break;
        int found = 0;
        for (int att = 0; !found && now() < t_end; att++) {
            int pad = best.n > 0 && best.n + 2 == n && balanced(&best) && (att % 2 == 0);
            if (pad) padded_start(&cur, &best);
            else circulant_start(&cur, n);
            double T0 = 0.5 + 3.0 * rnd01();
            if (anneal(&cur, 300000L, T0, 0.05) == 0 && is_valid(&cur)) {
                copy_graph(&best, &cur);
                found = 1;
            }
        }
        if (!found) break;
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1) { printf("1 0\n"); return 0; }
    if (d > MAXD) { printf("2 1\n0 1\n"); return 0; }

    memset(&best, 0, sizeof best);
    read_start(&best);
    if (best.n == 0) set_fallback(&best);
    if (is_valid(&best) && best.n < moore_bound()) search();
    if (!is_valid(&best)) set_fallback(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    try:
        if D == 3 and lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    except Exception:
        return None
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    # Valid fallback chain: known construction, K_{d,d}, then a single edge.
    best = None
    candidates = [known_start(d, D)]
    if d >= 1:
        candidates.append(lib.haar_graph(d, range(d)))
    candidates.append((2, [(0, 1)]))
    for cand in candidates:
        if cand is None:
            continue
        try:
            if lib.is_valid(cand[0], cand[1], d, D):
                best = cand
                break
        except Exception:
            continue
    if best is None:
        best = (1, [])

    if d >= 1 and D >= 1 and best[0] < lib.moore_bound(d, D):
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=best if best[0] > 1 else None,
                                 timeout=budget + 10.0)
                out = lib.parse_graph_text(text)
                if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                    best = out
            except Exception:
                pass
    return best
