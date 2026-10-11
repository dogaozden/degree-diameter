"""Bold change: the lift-based search is replaced by a search over abelian Cayley-type
bipartite graphs (Haar-style graphs H(G, S) on G x {0,1}, with A_g ~ B_{g+s} for s in S,
G = Z_a x Z_b, |S| = d). For each side size N the C engine anneals a d-element set S
until the diameter bound holds. Only two BFS runs are needed (from A_0 and B_0) because
translations act transitively on each side. The engine then hands the remaining time to
grow-by-two annealing from the best graph. The start graph is always kept as a fallback,
and Python re-validates everything before returning it.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: abelian Haar-type graphs + grow-by-two.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: for side size N, pick an abelian group G = Z_a x Z_b with ab = N and a
 *   d-element set S of G. Graph: A_g ~ B_{g+s}. Translations are automorphisms, so
 *   diameter <= D is checked by BFS from A_0 and B_0 only. Anneal S on the number of
 *   unreached pairs.
 * Phase 2: grow by two (add one vertex per side using stolen edges), then anneal
 *   degree-preserving swaps until the diameter bound holds.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long moore;
static double t_end;
static Graph best;
static Graph work;
static Graph cand;

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

static long compute_moore(void) {
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
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Bitset reachability, D rounds. */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ abelian group */

/* G = Z_GA x Z_GB, element x = i*GB + j, NG = GA*GB. */
static int GA = 1, GB = 1, NG = 1;

static int gadd(int x, int y) {
    int i = x / GB, j = x % GB, k = y / GB, l = y % GB;
    return ((i + k) % GA) * GB + (j + l) % GB;
}

static int gneg(int x) {
    int i = x / GB, j = x % GB;
    return ((GA - i) % GA) * GB + (GB - j) % GB;
}

static void set_group(int a, int b) {
    GA = a;
    GB = b;
    NG = a * b;
}

/* Uniform random divisor split N = a*b. */
static void random_group(int N) {
    int cnt = 0, pick = 1;
    for (int a = 1; a <= N; a++)
        if (N % a == 0) {
            cnt++;
            if (rndint(cnt) == 0) pick = a;
        }
    set_group(pick, N / pick);
}

/* ------------------------------------------------------------------ Haar-type graphs */

/* Graph H(G, S): A_g (index g) ~ B_{g+s} (index NG + g + s) for s in S. */
static int Sg[MAXD], NSg[MAXD];
static int qq[2 * MAXN], vis[2 * MAXN];
static int vstamp = 0;

static int in_S(int x, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (Sg[i] == x) return 1;
    return 0;
}

/* Requires NG >= d. */
static void random_set(void) {
    for (int t = 0; t < d; t++) {
        int x;
        do { x = rndint(NG); } while (in_S(x, t));
        Sg[t] = x;
        NSg[t] = gneg(x);
    }
}

/* Unreached (source, vertex) pairs from A_0 and B_0 within D steps. 0 iff valid. */
static long haar_cost(void) {
    long unreached = 0;
    int n2 = 2 * NG;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? NG : 0;
        vstamp++;
        int head = 0, tail = 0;
        vis[s0] = vstamp;
        qq[tail++] = s0;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qq[head++];
                if (u < NG) {
                    for (int t = 0; t < d; t++) {
                        int v = NG + gadd(u, Sg[t]);
                        if (vis[v] != vstamp) { vis[v] = vstamp; qq[tail++] = v; }
                    }
                } else {
                    int h = u - NG;
                    for (int t = 0; t < d; t++) {
                        int v = gadd(h, NSg[t]);
                        if (vis[v] != vstamp) { vis[v] = vstamp; qq[tail++] = v; }
                    }
                }
            }
        }
        unreached += n2 - tail;
    }
    return unreached;
}

static void build_haar(Graph *g) {
    g->n = 2 * NG;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= NG; }
    for (int x = 0; x < NG; x++)
        for (int t = 0; t < d; t++) add_edge(g, x, NG + gadd(x, Sg[t]));
}

/* Anneal S for the current group. Returns the final cost (0 = success). */
static long anneal(double until, int steps) {
    random_set();
    long c = haar_cost();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = rndint(d);
        int x = rndint(NG);
        if (in_S(x, d)) continue;
        int old = Sg[t], oldn = NSg[t];
        Sg[t] = x;
        NSg[t] = gneg(x);
        long c2 = haar_cost();
        double T = 1.5 * (1.0 - (double)s / steps) + 0.05;
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            Sg[t] = old;
            NSg[t] = oldn;
        }
    }
    return c;
}

/* Search increasing side sizes N, trying random abelian groups of order N. */
static void haar_phase(double until) {
    while (now() < until) {
        int bestN = best.n / 2;
        int cap = moore < MAXN ? (int)moore : MAXN;
        int N = bestN + 1 + (rnd01() < 0.5 ? 0 : rndint(4));
        if (N < d) N = d;
        if (2 * N > cap) N = bestN + 1;
        if (N < d || 2 * N > cap) return;
        random_group(N);
        if (anneal(until, 30000) == 0) {
            build_haar(&cand);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *base, Graph *w, double until) {
    int n = base->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
    copy_graph(w, base);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(w);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(w->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(w->n);
        if (w->deg[v] == 0) continue;
        int u = w->adj[v][rndint(w->deg[v])];
        int s = rndint(w->n);
        if (w->side[s] != w->side[v] || s == v || w->deg[s] == 0) continue;
        int t = w->adj[s][rndint(w->deg[s])];
        if (t == u || has_edge(w, v, t) || has_edge(w, s, u)) continue;
        del_edge(w, v, u);
        del_edge(w, s, t);
        add_edge(w, v, t);
        add_edge(w, s, u);
        long nb = bad_pairs(w);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(w, v, t);
            del_edge(w, s, u);
            add_edge(w, v, u);
            add_edge(w, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(w);
}

static void grow_search(double until) {
    while (now() < until && best.n + 2 <= moore && best.n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
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
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        haar_phase(t0 + (t_end - t0) * 0.6);
        grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
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

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
