"""Cyclic Haar annealing seed plus random-start and grow annealing (a different construction).

The parent used orbit-checked semidirect voltage lifts. This version replaces that engine
with three ideas, all in C:

1. Cyclic Haar search. The graph with parts Z_m and Z_m, where a_i ~ b_{i+s} for s in S,
   |S| = d, is a d-regular bipartite lift. Its diameter is found by simulated annealing over
   the shift set S (cost = unreached pairs). m is raised until annealing fails.
2. Random-start annealing. A random d-regular bipartite graph on N = best + 2 vertices is
   annealed with degree-preserving double-edge swaps, with the unreached-pair count as cost.
   It has no algebraic structure, so it explores a different region from the lifts.
3. Grow and kick. Growth by one vertex pair (edge stealing, then annealing), and a plateau
   kick (random swaps on the best graph, then repair at the same order).

Python still provides K_{d,d} or a known construction (D = 3, 4) as a start, validates the
C output, and falls back to the start on any error. Only one C run is made.
"""
import itertools
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
#define MAXD 16
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} G;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
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

static int has_edge(const G *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(G *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(G *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(G *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D; also fills badv[]. */
static long bad_pairs(const G *g) {
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

static int is_valid(const G *g) {
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

static void read_start(G *g) {
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

static void print_graph(const G *g) {
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
static void complete_bipartite(G *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ cyclic Haar search */

static void build_haar(G *g, int m, const int *S) {
    g->n = 2 * m;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= m; }
    for (int i = 0; i < m; i++)
        for (int t = 0; t < d; t++) add_edge(g, i, m + (i + S[t]) % m);
}

static void rand_shifts(int *S, int m) {
    for (int t = 0; t < d; t++) {
        int v, ok;
        do {
            v = rndint(m);
            ok = 1;
            for (int u = 0; u < t; u++)
                if (S[u] == v) ok = 0;
        } while (!ok);
        S[t] = v;
    }
}

/* For m = d+1, d+2, ...: anneal the shift set S until the Haar graph has diameter <= D.
 * Stops at the first m that fails. Updates best only with a strictly larger valid graph. */
static void haar_search(G *best, double until) {
    int m = best->n / 2 + 1;
    if (m < d + 1) m = d + 1;
    static G cand;
    int S[MAXD];
    while (now() < until) {
        if (2L * m > moore_bound() || 2L * m > MAXN) break;
        int ok = 0;
        for (int rest = 0; rest < 6 && !ok && now() < until; rest++) {
            rand_shifts(S, m);
            build_haar(&cand, m, S);
            long c = bad_pairs(&cand);
            for (int s = 0; s < 1500 && c > 0; s++) {
                if ((s & 63) == 0 && now() > until) break;
                double T = 1.0 * (1.0 - s / 1500.0) + 0.05;
                int t = rndint(d), v = rndint(m), dup = 0;
                for (int u = 0; u < d; u++)
                    if (S[u] == v) dup = 1;
                if (dup) continue;
                int old = S[t];
                S[t] = v;
                build_haar(&cand, m, S);
                long nc = bad_pairs(&cand);
                if (nc <= c || rnd01() < exp((double)(c - nc) / T)) c = nc;
                else S[t] = old;
            }
            if (c == 0) ok = 1;
        }
        if (!ok) break;
        build_haar(&cand, m, S);
        if (is_valid(&cand) && cand.n > best->n) *best = cand;
        m++;
    }
}

/* ------------------------------------------------------------ random start */

/* d-regular bipartite graph on N vertices (sides N/2 each): d random perfect matchings
 * between the sides, each one rejected until it avoids existing edges. */
static int random_regular(G *g, int N) {
    int k = N / 2;
    if (N < 2 || (N % 2) || k < d || N > MAXN) return 0;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= k; }
    static int perm[MAXN];
    for (int l = 0; l < d; l++) {
        int placed = 0;
        for (int att = 0; att < 400 && !placed; att++) {
            for (int i = 0; i < k; i++) perm[i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int x = perm[i]; perm[i] = perm[j]; perm[j] = x;
            }
            int ok = 1;
            for (int i = 0; i < k && ok; i++)
                if (has_edge(g, i, k + perm[i])) ok = 0;
            if (ok) {
                for (int i = 0; i < k; i++) add_edge(g, i, k + perm[i]);
                placed = 1;
            }
        }
        if (!placed) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------ annealing */

/* Vertex choice biased toward vertices that miss some pairs (a heuristic only). */
static int pick_vertex(const G *g) {
    int v = rndint(g->n);
    for (int t = 0; t < 20 && badv[v] == 0; t++) v = rndint(g->n);
    return v;
}

/* Degree-preserving double-edge swaps on the unreached-pair cost.
 * Returns 1 iff g ends up a valid diameter-D graph before 'until'. */
static int anneal(G *g, long steps, double until) {
    long bad = bad_pairs(g);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double T = 1.2 * (1.0 - (double)s / (double)steps) + 0.05;
        int a = pick_vertex(g);
        if (g->deg[a] == 0) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        int c = rndint(g->n);
        if (c == a || g->side[c] != g->side[a] || g->deg[c] == 0) continue;
        int e = g->adj[c][rndint(g->deg[c])];
        if (e == b || has_edge(g, a, e) || has_edge(g, c, b)) continue;
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(g, a, e);
            del_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
    }
    return bad == 0 && is_valid(g);
}

/* ------------------------------------------------------------ grow by one pair */

/* Adds vertices x (side 0) and y (side 1) with edge x-y. x takes the far end b of an
 * old edge a-b and y takes a, d-1 times, so every degree stays exact. Then anneals. */
static int grow_once(const G *best, G *work, double until, long steps) {
    int n = best->n;
    if (n + 2 > MAXN) return 0;
    *work = *best;
    work->n = n + 2;
    int x = n, y = n + 1;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    if (k < d - 1) return 0;
    return anneal(work, steps, until);
}

/* Plateau kick: random degree-preserving swaps applied to a copy of best. */
static void kick(const G *best, G *work, int swaps) {
    *work = *best;
    int done = 0;
    for (long tries = 0; done < swaps && tries < (long)swaps * 80; tries++) {
        int v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (s == v || work->side[s] != work->side[v] || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        done++;
    }
}

/* Mixed search: grow by a pair, random start at N+2, or kick + repair at fixed order. */
static void grow_search(G *best, double until) {
    static G work;
    int fails = 0;
    while (now() < until) {
        long lim = moore_bound();
        if (lim > MAXN) lim = MAXN;
        int N = best->n;
        if (N + 2 > lim) break;
        double left = until - now();
        if (left <= 0) break;
        double slice = left / 5.0;
        if (slice < 3.0) slice = 3.0;
        if (slice > left) slice = left;
        double dl = now() + slice;
        int mode = rndint(10);
        int grew = 0, same = 0;
        if (fails > 0 && fails % 10 == 0) {
            kick(best, &work, 20 + rndint(40));
            same = anneal(&work, 30000, dl) && work.n == N;
        } else if (mode < 6) {
            grew = grow_once(best, &work, dl, 3000 + rndint(6000));
        } else {
            grew = random_regular(&work, N + 2) && anneal(&work, 40000, dl);
        }
        if (grew && work.n > N) {
            *best = work;
            fails = 0;
        } else if (same) {
            *best = work;
            fails++;
        } else {
            fails++;
        }
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
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static G best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        haar_search(&best, t0 + (t_end - t0) * 0.35);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
