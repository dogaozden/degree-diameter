import itertools
import random
import sys
import time

import lib

sys.setrecursionlimit(10000)


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs with fixed vertex count.
#
# Input: a bipartite graph with max degree d (often one new vertex that has
# been attached with spare-degree repairs). Moves:
#   - fill: add a cross-side edge between two deficient vertices (never hurts),
#   - double-edge switch (keeps all degrees and bipartiteness).
# Cost = number of vertex pairs at distance > D (computed with bitsets).
# Prints a valid graph as soon as cost reaches 0, otherwise "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3000

static int N, DD, DMAX, WW;
static int *deg, *nb, *col, *qu;
static unsigned char *am;
static uint64_t *rA, *rB;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static int cost(void) {
    uint64_t *cu = rA, *nx = rB;
    int v, i, r, w;
    for (v = 0; v < N; v++) {
        memset(cu + (size_t)v * WW, 0, sizeof(uint64_t) * (size_t)WW);
        cu[(size_t)v * WW + v / 64] |= 1ULL << (v % 64);
    }
    for (r = 0; r < DD; r++) {
        for (v = 0; v < N; v++) {
            uint64_t *o = nx + (size_t)v * WW;
            uint64_t *s0 = cu + (size_t)v * WW;
            for (w = 0; w < WW; w++) o[w] = s0[w];
            for (i = 0; i < deg[v]; i++) {
                uint64_t *s = cu + (size_t)nb[v * DMAX + i] * WW;
                for (w = 0; w < WW; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cu; cu = nx; nx = t;
    }
    long bad = 0;
    for (v = 0; v < N; v++) {
        int pc = 0;
        for (w = 0; w < WW; w++) pc += popc(cu[(size_t)v * WW + w]);
        bad += N - pc;
    }
    return (int)(bad / 2);
}

static void addE(int a, int b) {
    nb[a * DMAX + deg[a]++] = b;
    nb[b * DMAX + deg[b]++] = a;
    am[a * N + b] = 1;
    am[b * N + a] = 1;
}

static void rep(int v, int old, int nw) {
    int i;
    for (i = 0; i < deg[v]; i++)
        if (nb[v * DMAX + i] == old) { nb[v * DMAX + i] = nw; return; }
}

/* remove a-b and c-e, add a-e and c-b (a,c on side 0; b,e on side 1) */
static void sw(int a, int b, int c, int e) {
    rep(a, b, e);
    rep(e, c, a);
    rep(c, e, b);
    rep(b, a, c);
    am[a * N + b] = am[b * N + a] = 0;
    am[c * N + e] = am[e * N + c] = 0;
    am[a * N + e] = am[e * N + a] = 1;
    am[c * N + b] = am[b * N + c] = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DD = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double t0 = now_s();
    double span = tl * 0.9;

    int n, m, i, k, s;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0 || d < 1 || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n; DMAX = d; WW = (n + 63) / 64;
    deg = calloc(n, sizeof(int));
    nb = calloc((size_t)n * d, sizeof(int));
    am = calloc((size_t)n * n, 1);
    col = malloc(sizeof(int) * n);
    qu = malloc(sizeof(int) * n);
    rA = calloc((size_t)n * WW, sizeof(uint64_t));
    rB = calloc((size_t)n * WW, sizeof(uint64_t));
    int *L0 = malloc(sizeof(int) * n), *L1 = malloc(sizeof(int) * n), *S0 = malloc(sizeof(int) * n);

    int ok = 1;
    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || am[u * n + v] || deg[u] >= d || deg[v] >= d) {
            ok = 0; break;
        }
        addE(u, v);
    }
    if (ok) {
        for (i = 0; i < n; i++) col[i] = -1;
        for (s = 0; s < n && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int head = 0, tail = 0;
            qu[tail++] = s;
            while (head < tail && ok) {
                int x = qu[head++];
                for (k = 0; k < deg[x]; k++) {
                    int y = nb[x * d + k];
                    if (col[y] < 0) { col[y] = 1 - col[x]; qu[tail++] = y; }
                    else if (col[y] == col[x]) { ok = 0; break; }
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    int cur = cost();
    while (cur > 0) {
        double el = now_s() - t0;
        if (el > span) break;
        double frac = el / span;
        double T = 0.5 * (1.0 - frac) + 0.03;

        int n0 = 0, n1 = 0, s0 = 0;
        for (i = 0; i < n; i++) {
            if (deg[i] < d) { if (col[i] == 0) L0[n0++] = i; else L1[n1++] = i; }
            if (col[i] == 0 && deg[i] > 0) S0[s0++] = i;
        }
        int filled = 0;
        if (n0 > 0 && n1 > 0) {
            for (k = 0; k < 30 && !filled; k++) {
                int a = L0[rndi(n0)], b = L1[rndi(n1)];
                if (!am[a * n + b]) { addE(a, b); filled = 1; }
            }
        }
        if (filled) { cur = cost(); continue; }
        if (s0 == 0) break;

        int a = S0[rndi(s0)];
        int b = nb[a * d + rndi(deg[a])];
        int c = S0[rndi(s0)];
        if (c == a) continue;
        int e = nb[c * d + rndi(deg[c])];
        if (am[a * n + e] || am[c * n + b]) continue;
        sw(a, b, c, e);
        int nc = cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
        else sw(a, e, c, b);
    }

    if (cur == 0) {
        long cnt = 0;
        int u;
        for (u = 0; u < n; u++)
            for (k = 0; k < deg[u]; k++)
                if (nb[u * d + k] > u) cnt++;
        printf("%d %ld\n", n, cnt);
        for (u = 0; u < n; u++)
            for (k = 0; k < deg[u]; k++)
                if (nb[u * d + k] > u) printf("%d %d\n", u, nb[u * d + k]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """A dense structured graph whose degree is at least d, later thinned into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
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
# Thin a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _perfect_matching(n, adj, color, rng):
    """Random perfect matching of the bipartite graph (Kuhn augmentation). dict left->right, or None."""
    left = [v for v in range(n) if color[v] == 0]
    nb = {}
    for u in left:
        lst = list(adj[u])
        rng.shuffle(lst)
        nb[u] = lst
    match_l = {}
    match_r = {}
    for u in left:
        for v in nb[u]:
            if v not in match_r:
                match_l[u] = v
                match_r[v] = u
                break

    def augment(u, seen):
        for v in nb[u]:
            if v in seen:
                continue
            seen.add(v)
            w = match_r.get(v)
            if w is None or augment(w, seen):
                match_l[u] = v
                match_r[v] = u
                return True
        return False

    for u in left:
        if u not in match_l:
            if not augment(u, set()):
                return None
    if len(match_l) != len(left):
        return None
    return match_l


def _regular_thin(n, edges, d, rng):
    """For a (d+1)-regular bipartite graph, drop a random perfect matching. Returns edges or None."""
    adj = _to_sets(n, edges)
    if any(len(a) != d + 1 for a in adj):
        return None
    color = _bipartition(n, adj)
    match = _perfect_matching(n, adj, color, rng)
    if match is None:
        return None
    drop = {(min(u, v), max(u, v)) for u, v in match.items()}
    return [(u, v) for u, v in edges if (min(u, v), max(u, v)) not in drop]


def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = None
    if rng.random() < 0.8:
        e = _regular_thin(raw_n, raw_e, d, rng)
    if e is None:
        e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# NEW: attach a vertex, then let the C annealer repair the diameter.
# ----------------------------------------------------------------------------

def _attach(n, edges, d, rng):
    """Add vertex n joined to d vertices of the colour-1 side.

    Chosen vertices with full degree first lose one random edge to make room,
    so the new vertex has degree <= d. The resulting graph stays bipartite.
    """
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    side1 = [v for v in range(n) if color[v] == 1]
    if not side1:
        return None
    rng.shuffle(side1)
    side1.sort(key=lambda v: len(adj[v]) >= d)  # spare-degree vertices first
    chosen = side1[:d]
    drop = set()
    for b in chosen:
        if len(adj[b]) >= d:
            a = rng.choice(adj[b])
            drop.add((min(a, b), max(a, b)))
    out = [e for e in edges if (min(e[0], e[1]), max(e[0], e[1])) not in drop]
    v = n
    out += [(b, v) for b in chosen]
    return n + 1, out


def _c_repair(n, edges, d, D, budget, seed):
    """Run the C annealer on (n, edges) for `budget` seconds. Returns (n, edges) or None."""
    if budget < 0.5:
        return None
    txt = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(n, edges), timeout=budget + 15.0)
    rn, re = lib.parse_graph_text(txt)
    if rn <= 0:
        return None
    return rn, re


def _c_phase(best_n, best_e, d, D, deadline, rng, consider):
    """Repeatedly attach a vertex and ask C to repair it. Keeps every valid success."""
    cur_n, cur_e = best_n, list(best_e)
    fails = 0
    while fails < 4:
        remain = deadline - time.monotonic()
        if remain < 1.5:
            break
        att = _attach(cur_n, cur_e, d, rng)
        if att is None:
            break
        slice_t = min(remain - 0.5, 6.0)
        try:
            res = _c_repair(att[0], att[1], d, D, slice_t, rng.randrange(1 << 30))
        except RuntimeError:
            res = None
        if res is not None and res[0] > cur_n and lib.is_valid(res[0], res[1], d, D):
            cur_n, cur_e = res
            consider(cur_n, cur_e)
            fails = 0
        else:
            fails += 1
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Python pruning helpers.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    """Delete random redundant edges (keeping diameter <= D). Returns the pruned edge list."""
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    """Repeatedly prune redundant edges, regrow with cover vertices, keep the best."""
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver. Phases (fractions of the usable budget T = 0.85 * time_limit):
#   A  structured small base (W(q) or PG(2,q)) grown, twin trials
#   B  thinned dense graph (regular matching thinning or degree reduction + deletion)
#   C  attach-and-repair with the C annealer, from the best valid graph
#   D  redundant-edge pruning and regrowth from the best graph
# Every candidate passes lib.is_valid before it is kept, and haar_graph is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured small base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.20)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Calibration shortcut: already at the Moore bound, nothing to search for.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.45):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.45):
                r = _deletion_trial(d, D, rn, re, rng, at(0.45))
                if r is None:
                    break
                consider(*r)

    # Phase C: C annealer attaches and repairs from the best valid graph.
    if D >= 2 and time.monotonic() < at(0.80):
        _c_phase(best_n, best_e, d, D, at(0.80), rng, consider)

    # Phase D: prune redundant edges and regrow from the best graph.
    if D >= 2 and time.monotonic() < at(1.0):
        _prune_regrow(best_n, best_e, d, D, at(1.0), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
