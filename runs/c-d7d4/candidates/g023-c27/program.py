import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: LNS over valid bipartite graphs. Each move removes 1-2
# vertices, adds 1-3 new vertices on random sides, fills spare degree, then
# anneals with degree-preserving bipartite double-edge switches until the
# diameter bound holds again. Only valid graphs are ever kept, and the best
# one is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)
#define ANNEAL_IT 400

static int d, D, n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];

static int s_n;
static int s_deg[MAXN];
static int s_col[MAXN];
static int s_adj[MAXN][MAXD];

static int b_n;
static int b_deg[MAXN];
static int b_adj[MAXN][MAXD];

static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static uint64_t (*CA)[MAXW] = bufA;
static uint64_t (*CB)[MAXW] = bufB;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }

static clock_t t0;
static double budget_s;
static time_t w0;

static int timeup(void) {
    if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget_s) return 1;
    if ((double)(time(NULL) - w0) > budget_s + 1.0) return 1;
    return 0;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}
static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; return; }
    }
}
static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}
static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* Number of unordered pairs at distance > D (unreachable counts as bad). */
static long long cost_of(void) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) CA[v][w] = 0;
        CA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) CB[v][w] = CA[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) CB[v][w] |= CA[u][w];
            }
        }
        uint64_t (*t)[MAXW] = CA;
        CA = CB;
        CB = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(CA[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void remove_vertex(int v) {
    while (deg[v] > 0) del_edge(v, adj[v][deg[v] - 1]);
    int last = n - 1;
    if (v != last) {
        for (int i = 0; i < deg[last]; i++) {
            int x = adj[last][i];
            for (int j = 0; j < deg[x]; j++) {
                if (adj[x][j] == last) { adj[x][j] = v; break; }
            }
        }
        deg[v] = deg[last];
        memcpy(adj[v], adj[last], sizeof(int) * (size_t)deg[last]);
        col[v] = col[last];
    }
    n--;
}

static void shuf(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add a new vertex on side c, joined to up to d vertices of the other side. */
static void add_vertex(int c) {
    int v = n++;
    col[v] = c;
    deg[v] = 0;
    static int cf[MAXN], cd[MAXN];
    int nf = 0, nd = 0;
    for (int u = 0; u < v; u++) {
        if (col[u] == 1 - c) {
            if (deg[u] < d) cf[nf++] = u;
            else cd[nd++] = u;
        }
    }
    shuf(cf, nf);
    shuf(cd, nd);
    int k = 0;
    for (int i = 0; i < nf + nd && k < d; i++) {
        int u = (i < nf) ? cf[i] : cd[i - nf];
        if (deg[u] >= d) {
            if (deg[u] == 0) continue;
            int w = adj[u][rndint(deg[u])];
            del_edge(u, w);
        }
        add_edge(v, u);
        k++;
    }
}

/* Random joins between deficient vertices on opposite sides. */
static void fill(void) {
    if (n < 2) return;
    long long tries = 40LL * n + 200;
    for (long long t = 0; t < tries; t++) {
        int a = rndint(n), b = rndint(n);
        if (col[a] == col[b] || deg[a] >= d || deg[b] >= d) continue;
        if (col[a] == 1) { int x = a; a = b; b = x; }
        if (has_edge(a, b)) continue;
        add_edge(a, b);
    }
}

/* Degree-preserving bipartite switches that try to reduce the cost. */
static long long anneal(int K, long long cur) {
    static int side0[MAXN];
    int m0 = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) side0[m0++] = v;
    if (m0 == 0) return cur;
    for (int it = 0; it < K && cur > 0; it++) {
        if ((it & 15) == 0 && timeup()) break;
        int a = side0[rndint(m0)];
        if (deg[a] == 0) continue;
        int c = side0[rndint(m0)];
        if (c == a || deg[c] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long long nw = cost_of();
        if (nw <= cur || (nw == cur + 1 && rndint(20) == 0)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

static void save_state(void) {
    s_n = n;
    memcpy(s_deg, deg, sizeof(int) * (size_t)n);
    memcpy(s_col, col, sizeof(int) * (size_t)n);
    memcpy(s_adj, adj, sizeof(int) * MAXD * (size_t)n);
}

static void restore_state(void) {
    n = s_n;
    memcpy(deg, s_deg, sizeof(int) * (size_t)n);
    memcpy(col, s_col, sizeof(int) * (size_t)n);
    memcpy(adj, s_adj, sizeof(int) * MAXD * (size_t)n);
}

static void save_best(void) {
    b_n = n;
    memcpy(b_deg, deg, sizeof(int) * (size_t)n);
    memcpy(b_adj, adj, sizeof(int) * MAXD * (size_t)n);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 1ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    t0 = clock();
    w0 = time(NULL);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 < 1 || n0 > MAXN - 16 || m0 < 0 || d < 1 || d > MAXD - 2 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    for (int i = 0; i < n; i++) deg[i] = 0;
    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { bad = 1; break; }
        if (has_edge(u, v) || deg[u] >= d || deg[v] >= d) { bad = 1; break; }
        add_edge(u, v);
    }
    if (bad) { printf("0 0\n"); return 0; }

    /* Bipartition by BFS. */
    int *q = (int *)malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; q[t++] = v; }
                else if (col[v] == col[u]) bad = 1;
            }
        }
    }
    free(q);
    if (bad) { printf("0 0\n"); return 0; }

    long long cur = cost_of();
    if (cur > 0) cur = anneal(20000, cur);
    if (cur > 0) { printf("0 0\n"); return 0; }

    save_best();
    while (!timeup()) {
        if (n + 6 >= MAXN) break;
        if (n < 8) break;
        save_state();
        int r = 1 + rndint(2);
        int net0 = (rndint(3) == 0);
        int kadd = net0 ? r : r + 1;
        for (int i = 0; i < r; i++) remove_vertex(rndint(n));
        for (int i = 0; i < kadd; i++) add_vertex(rndint(2));
        fill();
        long long c = cost_of();
        if (c > 0) c = anneal(ANNEAL_IT, c);
        if (c == 0) {
            if (n > b_n) save_best();
        } else {
            restore_state();
        }
    }

    long long m = 0;
    for (int v = 0; v < b_n; v++)
        for (int i = 0; i < b_deg[v]; i++)
            if (v < b_adj[v][i]) m++;
    printf("%d %lld\n", b_n, m);
    for (int v = 0; v < b_n; v++)
        for (int i = 0; i < b_deg[v]; i++)
            if (v < b_adj[v][i]) printf("%d %d\n", v, b_adj[v][i]);
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
# Bipartite voltage lifts over small groups (a separate construction family).
# ----------------------------------------------------------------------------

def _pick_group(order, rng):
    """Return (order, mul) for a cyclic or a semidirect group of the given order."""
    if order >= 4 and rng.random() < 0.5:
        ks = [k for k in range(2, 13) if order % k == 0 and order // k >= 2]
        rng.shuffle(ks)
        for k in ks:
            m = order // k
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                r = rng.choice(rs)
                try:
                    o, mul, _ = lib.semidirect_group(m, k, r)
                    return o, mul
                except ValueError:
                    continue
    o, mul, _ = lib.cyclic_group(order)
    return o, mul


def _init_darts(s, d, order, rng):
    """Darts (u, v, g): A vertex u, B vertex v (local indices), voltage g. Each A and B vertex gets d darts."""
    slots = [v for v in range(s) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    seen = set()
    for u in range(s):
        for j in range(d):
            v = slots[u * d + j]
            for _ in range(60):
                g = rng.randrange(order)
                if (u, v, g) not in seen:
                    break
            else:
                return None
            seen.add((u, v, g))
            darts.append((u, v, g))
    return darts


def _lift(s, darts, order, mul):
    """Lift the base graph: A side is 0..s-1, B side is s..2s-1 in the base."""
    return lib.group_lift(2 * s, [(u, s + v, g) for u, v, g in darts], order, mul)


def _lift_search(d, D, best_n, rng, deadline, consider):
    """Hill-climb voltages of random bipartite base lifts until a diameter-D lift appears."""
    base_pick = (1, 1, 2, 2, 3)
    while time.monotonic() < deadline:
        s = rng.choice(base_pick)
        base_n = 2 * s
        lo = best_n // base_n
        order = lo + 1 + rng.randrange(0, max(2, lo // 8 + 1))
        order, mul = _pick_group(order, rng)
        darts = _init_darts(s, d, order, rng)
        if darts is None:
            continue
        n, e = _lift(s, darts, order, mul)
        cost = lib.bad_pairs(n, e, D)
        steps = 0
        while cost > 0 and steps < 250 and time.monotonic() < deadline:
            steps += 1
            i = rng.randrange(len(darts))
            u, v, old = darts[i]
            g2 = rng.randrange(order)
            if g2 == old or (u, v, g2) in set(darts):
                continue
            darts[i] = (u, v, g2)
            n2, e2 = _lift(s, darts, order, mul)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= cost or rng.random() < 0.02:
                cost, n, e = c2, n2, e2
            else:
                darts[i] = (u, v, old)
        if cost == 0 and time.monotonic() < deadline:
            if n > best_n and lib.is_valid(n, e, d, D):
                consider(n, e)
                best_n = max(best_n, n)
            n3, e3 = _grow(n, e, d, D, deadline, rng)
            consider(n3, e3)
            best_n = max(best_n, n3)


# ----------------------------------------------------------------------------
# C engine driver. Returns a valid (n, edges) strictly from the C output, or None.
# ----------------------------------------------------------------------------

def _c_search(d, D, n, edges, seed, budget):
    """Run the C LNS engine from a valid start graph for about `budget` seconds."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(n, list(edges)), timeout=budget + 8.0)
        rn, re = lib.parse_graph_text(out)
    except Exception:
        return None
    if rn < 1 or not lib.is_valid(rn, re, d, D):
        return None
    return rn, re


# ----------------------------------------------------------------------------
# Driver. Phases (fractions of time_limit):
#   A  structured base (W(q) or PG(2,q)) grown, twin trials        until 0.12
#   L  bipartite voltage lifts over small groups                   until 0.18
#   C  C engine LNS from the best valid graph so far               until 0.90
# Every candidate passes lib.is_valid before it is kept. The fallback is
# haar_graph(d, range(d)), which is valid for every d >= 1 and D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def at(f):
        return start + f * time_limit

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.18):
        _lift_search(d, D, best_n, rng, at(0.18), consider)

    # Phase C: C engine LNS from the best valid graph found so far.
    if D >= 2 and d <= 60:
        budget = at(0.90) - time.monotonic() - 2.0
        if budget >= 2.0:
            res = _c_search(d, D, best_n, best_e, seed, budget)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
