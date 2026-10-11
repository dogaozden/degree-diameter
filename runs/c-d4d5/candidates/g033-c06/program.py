"""Bold variant: random-start simulated annealing on bipartite graphs, instead of voltage lifts.

Construction change for the weak targets:
- The C engine starts from a random d-regular bipartite graph on a target number of vertices
  (or from a given start graph). It minimises the number of vertex pairs at distance > D by
  degree-preserving 2-switches, focused on vertices that are still bad.
- When a graph reaches zero bad pairs, it saturates spare degree, records the result, and grows
  by two vertices (one per side) with degree-preserving edge stealing. Then it anneals again.
- If an annealing phase stalls, the engine restarts from the best valid graph with fresh growth.

Safety: Python first builds the algebraic starts (K_{d,d}, PG(2,q), Araujo-Pardo-Lopez, W(q))
and checks each with lib.is_valid. Every C result is checked with lib.is_valid before it
replaces the current best, and the best-so-far is always returned. Trivial and Moore-tight
cases return immediately.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter annealing engine.
 * Usage:  prog d D seed time_limit [target_n]   < start_graph
 * stdin:  "n m" then m lines "u v", or "0 0" for no start graph.
 * stdout: "n m" then m lines "u v": the largest valid graph found.
 */
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
} Graph;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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
        if (s > 100000000L) break;
    }
    return 2 * s;
}

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static int curbad[MAXN];
static long cur_bad;

/* Number of unordered vertex pairs at distance > D; fills badv[] per vertex. */
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

static long refresh(const Graph *g) {
    long b = bad_pairs(g);
    memcpy(curbad, badv, sizeof(int) * (size_t)g->n);
    return b;
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

/* Adding an A-B edge never increases a distance, so saturation keeps validity. */
static void saturate(Graph *g) {
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
        }
    }
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
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
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Random d-regular-ish bipartite graph on N vertices (N/2 per side). */
static void random_regular(Graph *g, int N) {
    int half = N / 2;
    g->n = 2 * half;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= half;
    }
    static int perm[MAXN];
    for (int t = 0; t < d; t++) {
        for (int attempt = 0; attempt < 500; attempt++) {
            for (int i = 0; i < half; i++) perm[i] = i;
            for (int i = half - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            int ok = 1;
            for (int i = 0; i < half && ok; i++)
                if (has_edge(g, i, half + perm[i])) ok = 0;
            if (ok) {
                for (int i = 0; i < half; i++) add_edge(g, i, half + perm[i]);
                break;
            }
        }
    }
}

static int used[MAXN];
static int ustamp = 0;

/* Add two vertices x (side 0) and y (side 1) joined to each other. Each takes d-1 edges
 * from disjoint old edges (a,b): a moves to y, b moves to x. Degrees are preserved. */
static void grow_pair(Graph *g) {
    int n = g->n;
    int x = n, y = n + 1;
    g->n = n + 2;
    g->deg[x] = g->deg[y] = 0;
    g->side[x] = 0;
    g->side[y] = 1;
    add_edge(g, x, y);
    ustamp++;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (g->side[a] != 0 || g->deg[a] == 0 || used[a] == ustamp) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        if (used[b] == ustamp) continue;
        del_edge(g, a, b);
        add_edge(g, x, b);
        add_edge(g, y, a);
        used[a] = used[b] = ustamp;
        k++;
    }
}

/* Degree-preserving 2-switch annealing on the bad-pair count. Returns 1 once valid. */
static int anneal(Graph *g, long iters, double until) {
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now() > until) return 0;
        double T = 1.5 * pow(0.03 / 1.5, (double)(it % 200000) / 200000.0);
        int v = -1;
        for (int t = 0; t < 30; t++) {
            int c = rndint(g->n);
            if (curbad[c] > 0) {
                v = c;
                break;
            }
        }
        if (v < 0) v = rndint(g->n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int a1, b1;
        if (g->side[v] == 0) {
            a1 = v;
            b1 = u;
        } else {
            a1 = u;
            b1 = v;
        }
        int a2 = rndint(g->n);
        if (g->side[a2] != 0 || g->deg[a2] == 0) continue;
        int b2 = g->adj[a2][rndint(g->deg[a2])];
        if (a1 == a2 || b1 == b2 || has_edge(g, a1, b2) || has_edge(g, a2, b1)) continue;
        del_edge(g, a1, b1);
        del_edge(g, a2, b2);
        add_edge(g, a1, b2);
        add_edge(g, a2, b1);
        long nb = bad_pairs(g);
        long delta = nb - cur_bad;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur_bad = nb;
            memcpy(curbad, badv, sizeof(int) * (size_t)g->n);
            if (nb == 0) return 1;
        } else {
            del_edge(g, a1, b2);
            del_edge(g, a2, b1);
            add_edge(g, a1, b1);
            add_edge(g, a2, b2);
        }
    }
    return cur_bad == 0;
}

static Graph cur, best;

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int target = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD - 1) {
        if (d >= 1 && d <= MAXD - 1) {
            complete_bipartite(&best);
            print_graph(&best);
        } else {
            printf("2 1\n0 1\n");
        }
        return 0;
    }
    long mb = moore_bound();

    read_start(&cur);
    if (cur.n == 0) {
        int tgt = target;
        if (tgt < 2 * d) tgt = 2 * d;
        tgt += tgt & 1;
        if (tgt > mb) tgt = (int)mb;
        if (tgt > MAXN) tgt = MAXN;
        tgt -= tgt & 1;
        random_regular(&cur, tgt);
    } else {
        saturate(&cur);
    }

    int have_best = 0;
    cur_bad = refresh(&cur);
    if (cur_bad == 0) {
        best = cur;
        have_best = 1;
    }

    while (now() < t_end) {
        if (cur_bad == 0) {
            saturate(&cur);
            cur_bad = refresh(&cur);
            if (cur_bad == 0 && (!have_best || cur.n > best.n)) {
                best = cur;
                have_best = 1;
            }
            if (cur.n + 2 > mb || cur.n + 2 > MAXN) break;
            grow_pair(&cur);
            cur_bad = refresh(&cur);
            continue;
        }
        if (!anneal(&cur, 400000, t_end)) {
            if (have_best) {
                cur = best;
                cur_bad = refresh(&cur);
            }
        }
    }

    if (!have_best || !is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


MAX_C_DEGREE = 15


def _run_engine(d, D, seed, budget, start, target):
    """Run the annealing engine once; return (n, edges) parsed from its output."""
    args = [d, D, seed, f"{budget:.2f}", target]
    text = lib.run_c(C_SOURCE, args, stdin_graph=start, timeout=budget + 4.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > MAX_C_DEGREE or best[0] >= lib.moore_bound(d, D):
        return best

    target = best[0] + 2
    # Run 1: random-start annealing (the new construction). Run 2: continue from the best so far.
    plan = [(seed, False), (seed + 7919, True)]
    for idx, (s, from_best) in enumerate(plan):
        left = 0.88 * time_limit - (time.monotonic() - t0) - 1.0
        if left < 1.0:
            break
        budget = left * (0.6 if idx == 0 else 1.0)
        start = best if from_best else None
        try:
            out = _run_engine(d, D, s, budget, start, target)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
