# Hybrid search: the parent's structured/twin/lift pipeline builds a valid start graph,
# then a new C engine grows it one vertex at a time. Each growth step adds a vertex to
# the best valid graph (after an optional degree-preserving shake), and a simulated
# annealer repairs it by minimising the exact number of vertex pairs at distance > D
# (bitset BFS). Moves are degree-preserving double-edge swaps, endpoint re-attachments
# to spare-degree vertices, and greedy filling of spare degree (which never raises the
# cost). Any valid graph found is kept, and the best one is printed before the budget ends.
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

#define MAXN 1100
#define MAXD 16
#define MAXW ((MAXN + 63) / 64)

static int d, D, n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];

static int bn;
static int bdeg[MAXN];
static int badj[MAXN][MAXD];

static int tdeg[MAXN];
static int tadj[MAXN][MAXD];

static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];

static uint64_t rs = 88172645463325252ULL;
static double budget_s = 10.0;
static double T0 = 3.0, T1 = 0.15;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void rep(int v, int old, int nw) {
    for (int k = 0; k < deg[v]; k++)
        if (adj[v][k] == old) { adj[v][k] = nw; return; }
}

static void del_nb(int v, int x) {
    for (int k = 0; k < deg[v]; k++)
        if (adj[v][k] == x) { adj[v][k] = adj[v][deg[v] - 1]; deg[v]--; return; }
}

static void add_nb(int v, int x) { adj[v][deg[v]++] = x; }

static long long moore_bound(void) {
    if (D == 0 || d == 0) return 1;
    if (d == 1) return 2;
    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    return 2 * s;
}

/* Number of unordered pairs at distance > D (unreachable pairs count). */
static long long cost_fn(void) {
    int Wc = (n + 63) / 64;
    uint64_t *A = bufA, *B = bufB;
    memset(A, 0, sizeof(uint64_t) * (size_t)n * Wc);
    for (int v = 0; v < n; v++) A[(size_t)v * Wc + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *bv = B + (size_t)v * Wc;
            const uint64_t *av = A + (size_t)v * Wc;
            memcpy(bv, av, sizeof(uint64_t) * Wc);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *au = A + (size_t)adj[v][k] * Wc;
                for (int w = 0; w < Wc; w++) bv[w] |= au[w];
            }
        }
        uint64_t *t = A; A = B; B = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        const uint64_t *av = A + (size_t)v * Wc;
        for (int w = 0; w < Wc; w++) cnt += popc(av[w]);
        total += n - cnt;
    }
    return total / 2;
}

static void save_state(void) {
    memcpy(tdeg, deg, sizeof(int) * n);
    memcpy(tadj, adj, sizeof(adj[0]) * n);
}

static void restore_state(void) {
    memcpy(deg, tdeg, sizeof(int) * n);
    memcpy(adj, tadj, sizeof(adj[0]) * n);
}

static void save_best(void) {
    bn = n;
    memcpy(bdeg, deg, sizeof(int) * n);
    memcpy(badj, adj, sizeof(adj[0]) * n);
}

static void restore_best(void) {
    n = bn;
    memcpy(deg, bdeg, sizeof(int) * bn);
    memcpy(adj, badj, sizeof(adj[0]) * bn);
}

static void shuffle_int(int *x, int c) {
    for (int i = c - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i]; x[i] = x[j]; x[j] = t;
    }
}

/* Add edges between deficient opposite-side vertices. Never increases the cost. */
static void fill_edges(void) {
    static int L0[MAXN], L1[MAXN];
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) L0[c0++] = v;
            else L1[c1++] = v;
        }
    }
    if (c0 == 0 || c1 == 0) return;
    shuffle_int(L0, c0);
    shuffle_int(L1, c1);
    long work = 0;
    for (int i = 0; i < c0; i++) {
        int a = L0[i];
        for (int j = 0; j < c1 && deg[a] < d; j++) {
            int b = L1[j];
            work++;
            if (deg[b] >= d || has_edge(a, b)) continue;
            add_nb(a, b);
            add_nb(b, a);
        }
        if (work > 300000) break;
    }
}

/* Double-edge swap: degrees preserved. Returns 1 if applied. */
static int move_swap(void) {
    int a = -1, c = -1;
    for (int t = 0; t < 60; t++) {
        int v = rndint(n);
        if (side[v] == 0 && deg[v] > 0) { a = v; break; }
    }
    for (int t = 0; t < 60; t++) {
        int v = rndint(n);
        if (side[v] == 0 && deg[v] > 0) { c = v; break; }
    }
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj[a][rndint(deg[a])];
    int e = adj[c][rndint(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    rep(a, b, e);
    rep(b, a, c);
    rep(c, e, b);
    rep(e, c, a);
    return 1;
}

/* Move one endpoint of an edge (a,b) to a spare-degree vertex z on b's side. */
static int move_endpoint(void) {
    int s = rndint(2);
    int a = -1;
    for (int t = 0; t < 60; t++) {
        int v = rndint(n);
        if (side[v] == s && deg[v] > 0) { a = v; break; }
    }
    if (a < 0) return 0;
    int b = adj[a][rndint(deg[a])];
    static int Lz[MAXN];
    int cz = 0;
    for (int v = 0; v < n; v++)
        if (side[v] != s && deg[v] < d) Lz[cz++] = v;
    if (cz == 0) return 0;
    int z = -1;
    for (int t = 0; t < 12; t++) {
        int v = Lz[rndint(cz)];
        if (!has_edge(a, v)) { z = v; break; }
    }
    if (z < 0) return 0;
    del_nb(b, a);
    rep(a, b, z);
    add_nb(z, a);
    return 1;
}

/* Anneal from the current state. Returns 1 if the cost reached 0. */
static int anneal(int K) {
    long long c = cost_fn();
    for (int it = 0; it < K && c > 0; it++) {
        if ((it & 31) == 0 && elapsed() > budget_s) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)K);
        save_state();
        int ok = (rnd64() & 1) ? move_swap() : move_endpoint();
        if (!ok) continue;
        fill_edges();
        long long nc = cost_fn();
        if (nc <= c || rnd01() < exp(-(double)(nc - c) / T)) c = nc;
        else restore_state();
    }
    return c == 0;
}

static void print_arrays(int nv, const int *dg, int (*ad)[MAXD]) {
    long m = 0;
    for (int v = 0; v < nv; v++)
        for (int k = 0; k < dg[v]; k++)
            if (ad[v][k] > v) m++;
    printf("%d %ld\n", nv, m);
    for (int v = 0; v < nv; v++)
        for (int k = 0; k < dg[v]; k++)
            if (ad[v][k] > v) printf("%d %d\n", v, ad[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);

    int nn = 0, m = 0;
    if (scanf("%d %d", &nn, &m) != 2) { nn = 0; m = 0; }
    if (nn < 0 || nn > MAXN) nn = 0;
    n = nn;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= MAXD || deg[v] >= MAXD) continue;
        if (has_edge(u, v)) continue;
        add_nb(u, v);
        add_nb(v, u);
    }

    /* Bipartition by BFS (isolated vertices get side 0). */
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    q[t++] = w;
                }
            }
        }
    }

    if (d < 1 || d > MAXD || D < 1 || n == 0) {
        print_arrays(n, deg, adj);
        return 0;
    }

    long long moore = moore_bound();
    save_best();                       /* raw input as fallback */
    int bvalid = 0;
    fill_edges();
    if (cost_fn() == 0 || anneal(20000)) {
        save_best();
        bvalid = 1;
    }
    if (!bvalid) {
        print_arrays(bn, bdeg, badj);
        return 0;
    }

    while (bn < moore && elapsed() < budget_s) {
        restore_best();
        if (rnd01() < 0.5)
            for (int k = 0; k < 4; k++) move_swap();
        side[n] = rndint(2);
        deg[n] = 0;
        n++;
        fill_edges();
        if (anneal(5000)) save_best();
    }

    print_arrays(bn, bdeg, badj);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (from the parent pipeline).
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
# Voltage lifts over small groups (pure Python, budgeted).
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
# C engine driver.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, n, edges, budget, timeout):
    """Run the C annealing engine once. Returns (n, edges) or None on any failure."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(n, edges), timeout=timeout)
        return lib.parse_graph_text(out)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.9 * time_limit
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

    # Meets the Moore bound already (e.g. d=1): return immediately.
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.08 * time_limit, rng)
            consider(n1, e1)

    # Voltage-lift search over small groups.
    lift_end = start + 0.2 * time_limit
    if time.monotonic() < lift_end:
        _lift_stage(d, D, lambda: best_n, rng, lift_end, consider)

    # Randomized twin-duplication pipelines from the structured base.
    trial_end = start + 0.3 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # New stage: C annealing engine grows the best valid graph by one vertex at a time.
    remaining = end - time.monotonic()
    budget = remaining - 2.5
    if budget >= 2.0:
        res = _c_search(d, D, seed, best_n, best_e, budget, remaining + 1.0)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
