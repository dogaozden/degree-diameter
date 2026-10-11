import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bit-parallel simulated annealing that grows a bipartite graph.
#
# State: a valid bipartite graph (max degree d, diameter <= D). Each step adds
# one vertex joined to a greedy cover of the opposite side (stealing an edge
# from saturated vertices), then anneals with degree-preserving double-edge
# switches and random fills to drive the count of bad pairs back to zero.
# On failure the state is restored to the last valid graph, so the output is
# always valid. Output is the largest valid graph found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXDEG 64
#define ITERS 2500

typedef uint64_t u64;

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXDEG];
} Snap;

static int D, d, n, W;
static int side[MAXN], deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char am[MAXN][MAXN];
static u64 ball[MAXN][MAXW], nxt[MAXN][MAXW];
static u64 rs = 88172645463325252ULL;
static clock_t t_end;
static Snap cur_s, best_s;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void reset(void) {
    memset(am, 0, sizeof am);
    memset(deg, 0, sizeof deg);
    n = 0;
}

static void add_edge(int a, int b) {
    am[a][b] = 1;
    am[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    am[a][b] = 0;
    am[b][a] = 0;
    for (int k = 0; k < deg[a]; k++)
        if (nb[a][k] == b) { nb[a][k] = nb[a][--deg[a]]; break; }
    for (int k = 0; k < deg[b]; k++)
        if (nb[b][k] == a) { nb[b][k] = nb[b][--deg[b]]; break; }
}

/* ball[v] = vertices within distance r of v (bitsets over current n). */
static void compute_balls(int r) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) ball[v][w] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int rr = 0; rr < r; rr++) {
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) nxt[v][w] = ball[v][w];
        for (int v = 0; v < n; v++)
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= ball[u][w];
            }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) ball[v][w] = nxt[v][w];
    }
}

/* Number of unordered pairs at distance > D. */
static long cost(void) {
    compute_balls(D);
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(ball[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void save(Snap *s) {
    s->n = n;
    for (int v = 0; v < n; v++) {
        s->side[v] = side[v];
        s->deg[v] = deg[v];
        memcpy(s->nb[v], nb[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void load(const Snap *s) {
    for (int i = 0; i < n; i++) memset(am[i], 0, (size_t)n);
    n = s->n;
    for (int v = 0; v < n; v++) {
        side[v] = s->side[v];
        deg[v] = s->deg[v];
        memcpy(nb[v], s->nb[v], sizeof(int) * (size_t)deg[v]);
        for (int k = 0; k < deg[v]; k++) am[v][nb[v][k]] = 1;
    }
}

/* Add a vertex on a random side, joined to a greedy cover of the opposite side. */
static void add_vertex(void) {
    int s = (int)(rnd() & 1);
    int v = n;
    compute_balls(D - 1);
    W = (n + 63) >> 6;
    u64 cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    static char mark[MAXN];
    memset(mark, 0, (size_t)n);
    int chosen[MAXDEG];
    int nc = 0;
    for (int step = 0; step < d; step++) {
        int best = -1;
        double bs = -1.0;
        for (int c = 0; c < n; c++) {
            if (side[c] != 1 - s || mark[c]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(ball[c][w] & ~cov[w]);
            double sc = g + 0.5 * rnd01();
            if (sc > bs) { bs = sc; best = c; }
        }
        if (best < 0) break;
        mark[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) cov[w] |= ball[best][w];
    }
    n = v + 1;
    side[v] = s;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (deg[c] >= d) {
            int k = rndint(deg[c]);
            int y = nb[c][k];
            del_edge(c, y);
        }
        add_edge(c, v);
    }
}

/* Add one random cross-side edge between deficient vertices (never increases cost). */
static void fill_one(void) {
    for (int t = 0; t < 60; t++) {
        int a = rndint(n);
        if (deg[a] >= d) continue;
        int b = rndint(n);
        if (side[b] == side[a] || deg[b] >= d || am[a][b]) continue;
        add_edge(a, b);
        return;
    }
}

/* Choose a double-edge switch a-b, c-e -> a-e, c-b preserving degrees and bipartiteness. */
static int pick_switch(int *pa, int *pb, int *pc, int *pe) {
    int a = rndint(n);
    if (deg[a] == 0) return 0;
    int b = nb[a][rndint(deg[a])];
    int c = -1;
    for (int t = 0; t < 20; t++) {
        int x = rndint(n);
        if (x != a && side[x] == side[a] && deg[x] > 0) { c = x; break; }
    }
    if (c < 0) return 0;
    int e = nb[c][rndint(deg[c])];
    if (e == b) return 0;
    if (am[a][e] || am[c][b]) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}

static void apply_switch(int a, int b, int c, int e) {
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static void undo_switch(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Simulated annealing towards zero bad pairs. Returns 1 if the state is valid. */
static int anneal(long iters) {
    long cur = cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && clock() > t_end) break;
        double T = 1.0 * (1.0 - (double)it / (double)iters) + 0.05;
        if (rnd01() < 0.15) {
            fill_one();
            cur = cost();
            continue;
        }
        int a, b, c, e;
        if (!pick_switch(&a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        long nc = cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            undo_switch(a, b, c, e);
        }
    }
    return cur == 0;
}

static void build_complete(void) {
    reset();
    n = 2 * d;
    for (int i = 0; i < d; i++) { side[i] = 0; side[d + i] = 1; }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) add_edge(i, d + j);
}

static int read_input(void) {
    int m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 200 || m < 0) return 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (am[u][v]) return 0;
        if (deg[u] >= d || deg[v] >= d) return 0;
        add_edge(u, v);
    }
    return 1;
}

static int colour_graph(void) {
    static int col[MAXN];
    static int q[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[tail++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < n; v++) side[v] = col[v];
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((u64)strtoull(argv[3], NULL, 10) * 2654435761ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double budget = atof(argv[4]);

    if (d < 2 || d >= MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }

    reset();
    int ok = read_input() && colour_graph() && cost() == 0;
    if (!ok) {
        build_complete();
    }

    t_end = clock() + (clock_t)(budget * (double)CLOCKS_PER_SEC);
    save(&best_s);

    while (clock() < t_end) {
        if (n >= MAXN - 2) break;
        save(&cur_s);
        add_vertex();
        if (anneal(ITERS)) {
            if (n > best_s.n) save(&best_s);
        } else {
            load(&cur_s);
        }
    }

    long m = 0;
    for (int v = 0; v < best_s.n; v++) m += best_s.deg[v];
    m /= 2;
    printf("%d %ld\n", best_s.n, m);
    for (int v = 0; v < best_s.n; v++)
        for (int k = 0; k < best_s.deg[v]; k++) {
            int u = best_s.nb[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers: cover growth and saturation.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng, attempts):
    """Greedily add vertices whose neighbourhoods are cover sets of the opposite side."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order (never breaks validity)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts=60):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + 0.9 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d} (diameter 2, valid for D >= 2).
    fallback_n, fallback_e = lib.haar_graph(d, range(d))
    best_n, best_e = fallback_n, list(fallback_e)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D < 2 or best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    # Structured base: W(q) for D >= 4, PG(2,q) for D = 3 (or as fallback).
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n1, e1 = _grow(n0, e0, d, D, start + 0.2 * time_limit, rng)
        consider(n1, e1)

    # Hand the best graph to the C annealer, which tries to add vertices.
    rem = hard_end - time.monotonic()
    if d <= 60 and best_n <= 800 and rem > 6 and best_n < lib.moore_bound(d, D):
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(max(1.0, rem - 4.0), 2)],
                            stdin_graph=(best_n, best_e), timeout=rem)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback_n, list(fallback_e)
    return best_n, list(best_e)
