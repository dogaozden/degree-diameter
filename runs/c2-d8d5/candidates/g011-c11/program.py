"""Bold variant: random bipartite regular starts annealed toward diameter D (not cyclic lifts), then grown by two."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: random near-regular bipartite starts at a target order, simulated
# annealing on double-edge swaps to minimise pairs at distance > D, and
# grow-by-two from every success. A failed start shrinks the target.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Random-regular annealing for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit [target_n] < anchor_graph
 * stdin:  "n m" + m edge lines (valid anchor), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D; badv[v] = vertices unreached from v. */
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

/* Reads the anchor; checks degree bound, no duplicates, bipartiteness (not diameter). */
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
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
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
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Random near-d-regular bipartite graph with m vertices per side (greedy, then fill). */
static void build_random(Graph *g, int m) {
    static int order[MAXN], cand[MAXN];
    g->n = 2 * m;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= m; }
    for (int i = 0; i < m; i++) order[i] = i;
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = order[i]; order[i] = order[j]; order[j] = t;
    }
    for (int oi = 0; oi < m; oi++) {
        int a = order[oi];
        for (int k = 0; k < d; k++) {
            int nc = 0;
            for (int j = 0; j < m; j++)
                if (g->deg[m + j] < d && !has_edge(g, a, m + j)) cand[nc++] = m + j;
            if (!nc) break;
            add_edge(g, a, cand[rndint(nc)]);
        }
    }
    for (int pass = 0; pass < 2; pass++)
        for (int a = 0; a < m; a++)
            for (int j = 0; j < m && g->deg[a] < d; j++)
                if (g->deg[m + j] < d && !has_edge(g, a, m + j)) add_edge(g, a, m + j);
}

static int cbad[MAXN];
static int blist[MAXN];

/* Anneal g (fixed order) with double-edge swaps until no bad pairs.
 * Returns 1 on success, 0 on timeout or stagnation. */
static int anneal(Graph *g, double until, long stall_limit) {
    long c = bad_pairs(g);
    memcpy(cbad, badv, sizeof(int) * g->n);
    if (c == 0) return 1;
    double T0 = 2.0 + 0.01 * (double)c;
    double T = T0;
    long bestc = c, stall = 0;
    while (c > 0) {
        if (now() > until) return 0;
        if (stall > stall_limit) return 0;
        int nbl = 0;
        for (int w = 0; w < g->n; w++)
            if (cbad[w]) blist[nbl++] = w;
        int v = (nbl && rnd01() < 0.8) ? blist[rndint(nbl)] : rndint(g->n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int s = rndint(g->n);
        if (s == v || g->side[s] != g->side[v] || g->deg[s] == 0) continue;
        int t = g->adj[s][rndint(g->deg[s])];
        if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) continue;
        del_edge(g, v, u);
        del_edge(g, s, t);
        add_edge(g, v, t);
        add_edge(g, s, u);
        long c2 = bad_pairs(g);
        if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) {
            c = c2;
            memcpy(cbad, badv, sizeof(int) * g->n);
            if (c < bestc) { bestc = c; stall = 0; }
            else stall++;
        } else {
            del_edge(g, v, t);
            del_edge(g, s, u);
            add_edge(g, v, u);
            add_edge(g, s, t);
            stall++;
        }
        T *= 0.9995;
        if (T < 0.05 * T0) T = T0;
    }
    return 1;
}

/* Adds two vertices x (side 0) and y (side 1) joined to each other; steals
 * d-1 edges (a,b) so that x-b and y-a replace them. Old degrees are kept. */
static int grow2(Graph *g) {
    int n = g->n;
    if (n + 2 > MAXN || (long)(n + 2) > moore_bound()) return 0;
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    int x = n, y = n + 1;
    g->n = n + 2;
    g->deg[x] = g->deg[y] = 0;
    g->side[x] = 0;
    g->side[y] = 1;
    add_edge(g, x, y);
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
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < anchor\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long target = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph anchor, best, cur;
    if (d < 1 || D < 2 || d > MAXD || 2 * d > MAXN) {
        printf("0 0\n");
        return 0;
    }
    read_start(&anchor);
    if (anchor.n > 0 && is_valid(&anchor)) copy_graph(&best, &anchor);
    else complete_bipartite(&best);

    long mo = moore_bound();
    long T = target > 0 ? target : mo * 3 / 10;
    for (;;) {
        if (now() >= t_end) break;
        if (T <= best.n) T = best.n + 2;
        if (T & 1) T++;
        if (T > mo || T > MAXN || T < 2L * d) break;

        build_random(&cur, (int)(T / 2));
        if (anneal(&cur, t_end, 1500)) {
            copy_graph(&best, &cur);
            int fails = 0;
            while (now() < t_end) {
                if (!grow2(&cur)) break;
                if (anneal(&cur, t_end, 1200)) {
                    copy_graph(&best, &cur);
                    fails = 0;
                } else {
                    if (now() >= t_end) break;
                    copy_graph(&cur, &best);
                    if (++fails >= 2) break;
                }
            }
            long step = best.n / 200;
            if (step < 1) step = 1;
            T = best.n + 2 * step;
        } else {
            if (now() >= t_end) break;
            long step = T / 100;
            if (step < 2) step = 2;
            T -= step;
        }
    }

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _target_n(d, D, floor):
    """Aggressive start order for the random-annealing engine (about 31% of the Moore bound)."""
    t = int(0.31 * lib.moore_bound(d, D))
    t -= t % 2
    return max(floor + 2, t)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Return the new graph if it is a larger valid graph, else None."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return best
        return None

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold search: random bipartite regular starts annealed toward diameter D (C engine).
    if D >= 2 and time.monotonic() < end - 1.0:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            target = _target_n(d, D, best[0])
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), target],
                                 stdin_graph=best, timeout=c_budget + 6)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
