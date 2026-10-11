"""Native C kill-repair-regrow search for bipartite graphs with max degree d and diameter D.

New in this version (not in the parent):
  * The whole search runs in C. Balls are bitsets, and the cost is the exact number of
    vertex pairs at distance > D, which is fast enough for simulated annealing.
  * Vertex insertion by edge stealing: a new vertex on side t is joined to a greedy cover
    (by radius-(D-1) balls) of the opposite side. A saturated cover vertex gives up one
    random edge, so insertion does not need spare degree.
  * Degree-preserving bipartite double-edge switches plus cross-side fills, accepted by
    Metropolis on the bad-pair count. Only states with cost 0 are ever kept.
  * Redundant-edge pruning frees degree before regrowth. Local kills (BFS clusters) are
    repaired and regrown, and the walk is anchored to the best graph found.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1400
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int side[MAXN];
} G;

static G g, snap, bestg;
static int d_, D_;
static double deadline_s;
static uint64_t rs = 88172645463325252ULL;
static uint64_t BUF[2][MAXN * MAXW];
static int defi0[MAXN], defi1[MAXN];

static uint64_t rnext(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static double rnd01(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int m) { return (int)(rnext() % (uint64_t)m); }
static int timeup(void) { return (double)clock() / CLOCKS_PER_SEC >= deadline_s; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < g.deg[a]; k++) if (g.adj[a][k] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    g.adj[a][g.deg[a]++] = b;
    g.adj[b][g.deg[b]++] = a;
}
static void drop_from(int a, int b) {
    for (int k = 0; k < g.deg[a]; k++) {
        if (g.adj[a][k] == b) {
            g.adj[a][k] = g.adj[a][--g.deg[a]];
            return;
        }
    }
}
static void remove_edge(int a, int b) { drop_from(a, b); drop_from(b, a); }

/* Bitset balls of radius r; returns a pointer into BUF valid until the next call. */
static uint64_t *compute_balls(int r) {
    int n = g.n, W = (n + 63) / 64;
    uint64_t *a = BUF[0], *b = BUF[1];
    memset(a, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) a[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = b + (size_t)v * W;
            const uint64_t *src = a + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int k = 0; k < g.deg[v]; k++) {
                const uint64_t *s2 = a + (size_t)g.adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = a; a = b; b = t;
    }
    return a;
}

/* Number of unordered vertex pairs at distance > D_ (unreachable pairs included). */
static long long cost_now(void) {
    int n = g.n, W = (n + 63) / 64;
    if (n <= 1) return 0;
    uint64_t *b = compute_balls(D_);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(b[(size_t)v * W + w]);
        bad += n - cnt;
    }
    return bad / 2;
}

/* Delete vertex x; the last vertex is moved into slot x. */
static void kill_vertex(int x) {
    while (g.deg[x] > 0) remove_edge(x, g.adj[x][0]);
    int last = g.n - 1;
    if (x != last) {
        for (int k = 0; k < g.deg[last]; k++) {
            int u = g.adj[last][k];
            for (int j = 0; j < g.deg[u]; j++) {
                if (g.adj[u][j] == last) { g.adj[u][j] = x; break; }
            }
        }
        g.deg[x] = g.deg[last];
        memcpy(g.adj[x], g.adj[last], sizeof(int) * MAXD);
        g.side[x] = g.side[last];
    }
    g.deg[last] = 0;
    g.n--;
}

/* Kill k vertices. Victims are removed in descending id order, so earlier kills
   do not disturb the ids of later victims. local = BFS-like cluster. */
static void kill_set(int k, int local) {
    int vic[16], nv = 0;
    if (g.n <= k + 2) return;
    vic[nv++] = rndint(g.n);
    for (int tr = 0; tr < 60 && nv < k && local; tr++) {
        int x = vic[rndint(nv)];
        if (g.deg[x] == 0) continue;
        int u = g.adj[x][rndint(g.deg[x])];
        int dup = 0;
        for (int i = 0; i < nv; i++) if (vic[i] == u) dup = 1;
        if (!dup) vic[nv++] = u;
    }
    while (nv < k) {
        int x = rndint(g.n), dup = 0;
        for (int i = 0; i < nv; i++) if (vic[i] == x) dup = 1;
        if (!dup) vic[nv++] = x;
    }
    for (int i = 0; i < nv; i++)
        for (int j = i + 1; j < nv; j++)
            if (vic[j] > vic[i]) { int t = vic[i]; vic[i] = vic[j]; vic[j] = t; }
    for (int i = 0; i < nv; i++) kill_vertex(vic[i]);
}

/* Add a vertex on side t, joined to a greedy cover (radius D-1 balls) of the other
   side. Saturated cover vertices give up one random edge (edge stealing). */
static void add_vertex(int t) {
    int n = g.n, W = (n + 63) / 64;
    if (n >= MAXN - 2) return;
    uint64_t *ball = compute_balls(D_ - 1);
    uint64_t covered[MAXW];
    char used[MAXN];
    int chosen[MAXD], nc = 0;
    memset(covered, 0, sizeof covered);
    memset(used, 0, sizeof used);
    for (int step = 0; step < d_; step++) {
        int best = -1;
        double bsc = -1.0;
        for (int s = 0; s < n; s++) {
            if (used[s] || g.side[s] == t) continue;
            int gain = 0;
            const uint64_t *bs = ball + (size_t)s * W;
            for (int w = 0; w < W; w++) gain += pc64(bs[w] & ~covered[w]);
            if (gain == 0) continue;
            double sc = gain + 0.5 * rnd01();
            if (sc > bsc) { bsc = sc; best = s; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) covered[w] |= ball[(size_t)best * W + w];
    }
    if (nc == 0) return;
    int v = g.n++;
    g.side[v] = t;
    g.deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (g.deg[s] >= d_) remove_edge(s, g.adj[s][rndint(g.deg[s])]);
        add_edge(s, v);
    }
}

/* Add random cross-side edges between deficient vertices (never increases cost). */
static void fill(void) {
    int n = g.n, c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) {
        if (g.deg[v] < d_) {
            if (g.side[v] == 0) defi0[c0++] = v; else defi1[c1++] = v;
        }
    }
    if (!c0 || !c1) return;
    long long tries = 3LL * c0 * c1 + 10;
    for (long long t = 0; t < tries; t++) {
        int a = defi0[rndint(c0)], b = defi1[rndint(c1)];
        if (g.deg[a] < d_ && g.deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
    }
}

static int pick_side0(int exclude) {
    for (int tr = 0; tr < 100; tr++) {
        int x = rndint(g.n);
        if (x != exclude && g.side[x] == 0 && g.deg[x] > 0) return x;
    }
    return -1;
}

/* Annealing on bad pairs. Moves: degree-preserving bipartite switches, and fills.
   Returns the final cost (0 means valid). */
static long long anneal(int iters, double T) {
    long long c = cost_now();
    for (int it = 0; it < iters && c > 0; it++) {
        if (timeup()) break;
        if (rnd01() < 0.05) {
            fill();
            c = cost_now();
            continue;
        }
        int a = pick_side0(-1);
        if (a < 0) break;
        int c2 = pick_side0(a);
        if (c2 < 0) continue;
        int b = g.adj[a][rndint(g.deg[a])];
        int e = g.adj[c2][rndint(g.deg[c2])];
        if (has_edge(a, e) || has_edge(c2, b)) continue;
        remove_edge(a, b);
        remove_edge(c2, e);
        add_edge(a, e);
        add_edge(c2, b);
        long long nc = cost_now();
        long long delta = nc - c;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            c = nc;
        } else {
            remove_edge(a, e);
            remove_edge(c2, b);
            add_edge(a, b);
            add_edge(c2, e);
        }
    }
    return c;
}

/* Delete random edges that keep the diameter bound (frees degree for regrowth). */
static void prune(int tests) {
    for (int t = 0; t < tests; t++) {
        if (timeup()) break;
        int a = rndint(g.n);
        if (g.deg[a] == 0) continue;
        int b = g.adj[a][rndint(g.deg[a])];
        remove_edge(a, b);
        if (cost_now() != 0) add_edge(a, b);
    }
}

static void build_kdd(void) {
    memset(&g, 0, sizeof g);
    int d = d_;
    g.n = 2 * d;
    for (int v = 0; v < 2 * d; v++) g.side[v] = (v >= d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(a, d + b);
}

static int colour_graph(void) {
    int n = g.n;
    int col[MAXN], stack[MAXN];
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int k = 0; k < g.deg[u]; k++) {
                int v = g.adj[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stack[sp++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < n; i++) g.side[i] = col[i];
    return 1;
}

static void run_search(void) {
    while (!timeup()) {
        memcpy(&snap, &g, sizeof(G));
        int op = rndint(10);
        double T = (rndint(3) == 0) ? 0.25 : (rndint(2) ? 0.4 : 0.6);
        if (op < 4) {
            if (rndint(2)) prune(60);
            add_vertex(rndint(2));
            fill();
        } else {
            int k = 1 + rndint(3);
            kill_set(k, rndint(3) != 0);
            for (int i = 0; i < k; i++) {
                add_vertex(rndint(2));
                fill();
            }
        }
        long long c = anneal(700, T);
        if (c == 0) {
            if (g.n > bestg.n) memcpy(&bestg, &g, sizeof(G));
            /* Anchor: drifting too far below the best graph returns to it. */
            if (g.n < bestg.n - 2) memcpy(&g, &bestg, sizeof(G));
        } else {
            memcpy(&g, &snap, sizeof(G));
        }
    }
}

static void output_graph(const G *x) {
    long long m2 = 0;
    for (int v = 0; v < x->n; v++) m2 += x->deg[v];
    printf("%d %lld\n", x->n, m2 / 2);
    for (int v = 0; v < x->n; v++)
        for (int k = 0; k < x->deg[v]; k++) {
            int u = x->adj[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    deadline_s = (double)clock() / CLOCKS_PER_SEC + budget;

    if (d_ < 1 || d_ > MAXD) { printf("0 0\n"); return 0; }
    if (D_ < 2) {
        if (d_ >= 1) printf("2 1\n0 1\n"); else printf("1 0\n");
        return 0;
    }

    int N = 0, M = 0, ok = 0;
    if (scanf("%d %d", &N, &M) == 2 && N > 0 && N <= MAXN - 200 && M >= 0) {
        memset(&g, 0, sizeof g);
        g.n = N;
        ok = 1;
        for (int i = 0; i < M && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
                g.deg[u] >= d_ || g.deg[v] >= d_ || has_edge(u, v)) {
                ok = 0;
            } else {
                add_edge(u, v);
            }
        }
        if (ok) ok = colour_graph();
    }
    if (!ok) build_kdd();

    if (cost_now() != 0) build_kdd();
    memcpy(&bestg, &g, sizeof(G));

    run_search();

    memcpy(&g, &bestg, sizeof(G));
    if (cost_now() != 0) build_kdd();
    output_graph(&g);
    return 0;
}
'''


# ----------------------------------------------------------------- constructions

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    """PG(2, q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    base = None
    if D >= 4:
        base = _best_gq(d)
    elif D == 3:
        base = _best_pg(d)
    if base is not None and base[0] > best[0] and lib.is_valid(base[0], base[1], d, D):
        best = base

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = max(1.0, 0.8 * time_limit - 3.0)
    timeout = max(budget + 2.0, 0.92 * time_limit)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                        stdin_graph=best, timeout=timeout)
        n, e = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
