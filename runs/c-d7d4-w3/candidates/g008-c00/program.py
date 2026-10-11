# New idea: a C-side growth search. Starting from the best valid graph, insert two
# vertices (v on side A, w on side B) by rewiring d disjoint matching edges
# (x_i, y_i): delete them, join v to all y_i and w to all x_i. Degrees are preserved
# and bipartiteness holds. Saturate spare degree, then run degree-preserving
# double-edge switches under simulated annealing on the exact count of vertex pairs
# at distance > D, using bitset BFS. A zero-cost state is a valid, larger graph.
# The parent's Python pipeline (GQ/PG base, voltage lifts, twin trials) supplies the start.
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2400
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static Graph G, BEST;
static int DEG = 0, DIAM = 0;
static uint64_t rs = 88172645463325252ULL;
static uint64_t ballA[MAXN * MAXW], ballB[MAXN * MAXW];
static int side0[MAXN], side1[MAXN], n0cnt = 0, n1cnt = 0;
static int mark[MAXN];
static int stamp = 0;

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static uint64_t xr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd(int k) { return (int)(xr() % (uint64_t)k); }
static double rndu(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < G.deg[u]; k++)
        if (G.adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    G.adj[u][G.deg[u]++] = v;
    G.adj[v][G.deg[v]++] = u;
}

static void drop_arc(int u, int v) {
    int k = 0;
    while (G.adj[u][k] != v) k++;
    G.adj[u][k] = G.adj[u][--G.deg[u]];
}

static void del_edge(int u, int v) {
    drop_arc(u, v);
    drop_arc(v, u);
}

/* Number of unordered vertex pairs at distance > DIAM (unreachable counts). */
static long cost_eval(void) {
    int N = G.n, w = (N + 63) >> 6;
    uint64_t *cur = ballA, *nxt = ballB, *t;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * w);
    for (int v = 0; v < N; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * w;
            memcpy(o, cur + (size_t)v * w, sizeof(uint64_t) * w);
            for (int k = 0; k < G.deg[v]; k++) {
                const uint64_t *s = cur + (size_t)G.adj[v][k] * w;
                for (int j = 0; j < w; j++) o[j] |= s[j];
            }
        }
        t = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * w;
        for (int j = 0; j < w; j++) c += popc64(s[j]);
        bad += N - c;
    }
    return bad / 2;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    memcpy(dst->side, src->side, sizeof(int) * src->n);
    memcpy(dst->deg, src->deg, sizeof(int) * src->n);
    for (int v = 0; v < src->n; v++)
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
}

static void rebuild_lists(void) {
    n0cnt = n1cnt = 0;
    for (int v = 0; v < G.n; v++) {
        if (G.side[v] == 0) side0[n0cnt++] = v;
        else side1[n1cnt++] = v;
    }
}

/* Degree-preserving double-edge switch: (a,b),(c,e) -> (a,e),(c,b). Sides kept. */
static int switch_move(int s[4]) {
    if (n0cnt < 2) return 0;
    int a = side0[rnd(n0cnt)];
    if (G.deg[a] == 0) return 0;
    int b = G.adj[a][rnd(G.deg[a])];
    int c = side0[rnd(n0cnt)];
    if (c == a || G.deg[c] == 0) return 0;
    int e = G.adj[c][rnd(G.deg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    s[0] = a;
    s[1] = b;
    s[2] = c;
    s[3] = e;
    return 1;
}

static void undo_switch(const int s[4]) {
    int a = s[0], b = s[1], c = s[2], e = s[3];
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Insert v (side 0) and w (side 1) by rewiring DEG disjoint matching edges. */
static int insert_pair(void) {
    if (n0cnt == 0 || G.n + 2 > MAXN) return 0;
    int xs[MAXD], ys[MAXD], k = 0;
    stamp++;
    int start = rnd(n0cnt);
    for (int t = 0; t < n0cnt && k < DEG; t++) {
        int x = side0[(start + t) % n0cnt];
        if (G.deg[x] == 0) continue;
        int y = G.adj[x][rnd(G.deg[x])];
        if (mark[y] == stamp) continue;
        mark[y] = stamp;
        xs[k] = x;
        ys[k] = y;
        k++;
    }
    if (k < DEG) return 0;
    for (int i = 0; i < k; i++) del_edge(xs[i], ys[i]);
    int v = G.n, w = G.n + 1;
    G.side[v] = 0;
    G.side[w] = 1;
    G.deg[v] = 0;
    G.deg[w] = 0;
    G.n += 2;
    for (int i = 0; i < k; i++) {
        add_edge(v, ys[i]);
        add_edge(w, xs[i]);
    }
    side0[n0cnt++] = v;
    side1[n1cnt++] = w;
    return 1;
}

/* Join random deficient opposite-side pairs. */
static void saturate(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int i = 0; i < n0cnt; i++)
        if (G.deg[side0[i]] < DEG) L[nl++] = side0[i];
    for (int i = 0; i < n1cnt; i++)
        if (G.deg[side1[i]] < DEG) R[nr++] = side1[i];
    if (!nl || !nr) return;
    long trials = 30L * (nl + nr) + 100;
    for (long t = 0; t < trials; t++) {
        int a = L[rnd(nl)], b = R[rnd(nr)];
        if (G.deg[a] < DEG && G.deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
    }
}

static long anneal(long iters, double T0, double T1, double tlim) {
    long cur = cost_eval();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && now() > tlim) break;
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        int s[4];
        if (!switch_move(s)) continue;
        long nc = cost_eval();
        long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cur = nc;
        else undo_switch(s);
    }
    return cur;
}

static int load_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN || m < 0) return 0;
    G.n = n;
    for (int v = 0; v < n; v++) {
        G.deg[v] = 0;
        G.side[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (G.deg[u] >= DEG || G.deg[v] >= DEG) return 0;
        if (has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (G.side[s] != -1) continue;
        G.side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int k = 0; k < G.deg[u]; k++) {
                int v = G.adj[u][k];
                if (G.side[v] == -1) {
                    G.side[v] = 1 - G.side[u];
                    stk[sp++] = v;
                } else if (G.side[v] == G.side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) m++;
    printf("%d %ld\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) printf("%d %d\n", v, g->adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (DEG < 1 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    if (!load_input()) {
        printf("0 0\n");
        return 0;
    }
    double deadline = now() + budget;
    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }
    copy_graph(&BEST, &G);
    long base_iters = 4000L + 60L * G.n;
    while (now() < deadline) {
        copy_graph(&G, &BEST);
        rebuild_lists();
        if (!insert_pair()) continue;
        saturate();
        if (anneal(base_iters, 0.9, 0.05, deadline) == 0)
            copy_graph(&BEST, &G);
    }
    print_graph(&BEST);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions (from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
            for attempt in range(200):
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins in random order while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Voltage lifts over small groups, searched by annealing (parent stage).
# ----------------------------------------------------------------------------

def _group_specs(lo, hi):
    """Cyclic groups and semidirect products Z_m x| Z_k with order in [lo, hi]."""
    specs = [("cyc", n) for n in range(lo, hi + 1)]
    for k in range(2, 13):
        for m in range(2, hi // k + 1):
            if not (lo <= m * k <= hi):
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    specs.append(("semi", m, k, r))
    return specs


def _make_group(spec):
    """Return (order, mul, inv) for a group spec from _group_specs."""
    if spec[0] == "cyc":
        return lib.cyclic_group(spec[1])
    _, m, k, r = spec
    return lib.semidirect_group(m, k, r)


def _random_base(a, d, rng, order):
    """Random base darts [i, j, g]: every A-vertex and B-vertex gets exactly d darts."""
    left = [i for i in range(a) for _ in range(d)]
    right = list(left)
    rng.shuffle(right)
    return [[left[k], right[k], rng.randrange(order)] for k in range(len(left))]


def _lift_adj(a, order, darts, R):
    """Adjacency lists of the lift. Side A is indices 0..a*order-1, side B is the rest."""
    N = 2 * a * order
    off = a * order
    adj = [[] for _ in range(N)]
    for i, j, g in darts:
        Rg = R[g]
        ba = i * order
        bb = off + j * order
        for x in range(order):
            u = ba + x
            v = bb + Rg[x]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _lift_cost(adj, a, order, D):
    """Number of (representative, vertex) pairs at distance > D, over the 2a representatives."""
    N = len(adj)
    total = 0
    sources = [i * order for i in range(a)] + [a * order + j * order for j in range(a)]
    for s in sources:
        seen = [False] * N
        seen[s] = True
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _lift_edges(a, order, darts, R):
    """Sorted edge list of the lift (every edge joins side A to side B)."""
    off = a * order
    E = set()
    for i, j, g in darts:
        Rg = R[g]
        for x in range(order):
            E.add((i * order + x, off + j * order + Rg[x]))
    return sorted(E)


def _voltage_search(a, d, D, order, R, rng, iters, deadline):
    """Anneal darts of a random base until the lift has diameter <= D. Returns darts or None."""
    darts = _random_base(a, d, rng, order)
    cur = _lift_cost(_lift_adj(a, order, darts, R), a, order, D)
    for _ in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        new = [list(x) for x in darts]
        if rng.random() < 0.7:
            new[rng.randrange(len(new))][2] = rng.randrange(order)
        else:
            k1 = rng.randrange(len(new))
            k2 = rng.randrange(len(new))
            new[k1][1], new[k2][1] = new[k2][1], new[k1][1]
        c2 = _lift_cost(_lift_adj(a, order, new, R), a, order, D)
        if c2 <= cur or rng.random() < 0.02:
            darts, cur = new, c2
    return darts if cur == 0 else None


def _lift_stage(d, D, get_best, rng, deadline, consider):
    """Repeatedly search voltage lifts over random groups just above the current best order."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        best = get_best()
        avail = [a for a in (1, 2) if best // (2 * a) + 1 <= moore // (2 * a)]
        if not avail:
            return
        a = rng.choice(avail)
        lo = best // (2 * a) + 1
        hi = min(moore // (2 * a), lo + 60)
        specs = _group_specs(lo, hi)
        if not specs:
            return
        spec = rng.choice(specs)
        order, mul, _ = _make_group(spec)
        R = [[mul(x, g) for x in range(order)] for g in range(order)]
        darts = _voltage_search(a, d, D, order, R, rng, 1500, deadline)
        if darts is not None:
            consider(2 * a * order, _lift_edges(a, order, darts, R))


# ----------------------------------------------------------------------------
# C stage: matching-rewire insertion + annealing (see C_SOURCE).
# ----------------------------------------------------------------------------

def _c_stage(d, D, seed, n, edges, t0, time_limit):
    """Run the C growth search from (n, edges); return parsed (n, edges) or None."""
    remaining = 0.92 * time_limit - (time.monotonic() - t0)
    budget = remaining - 2.5
    if budget < 2.0:
        return None
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=remaining)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= moore:
        return best_n, list(best_e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, t0 + 0.10 * time_limit, rng)
            consider(n1, e1)

    if best_n >= moore:
        return best_n, list(best_e)

    # Parent's voltage-lift stage, shortened.
    lift_end = t0 + 0.22 * time_limit
    if time.monotonic() < lift_end:
        _lift_stage(d, D, lambda: best_n, rng, lift_end, consider)

    # Parent's randomized twin-duplication pipelines, shortened.
    trial_end = t0 + 0.30 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    if best_n >= moore:
        return best_n, list(best_e)

    # NEW: C-side two-vertex insertion with degree-preserving switch annealing.
    if D >= 2 and d <= 31 and moore <= 2400 and best_n >= 2:
        try:
            res = _c_stage(d, D, seed, best_n, best_e, t0, time_limit)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
