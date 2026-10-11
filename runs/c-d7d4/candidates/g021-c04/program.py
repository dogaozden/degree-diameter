import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-bounded bipartite annealing with eviction moves.
#
# State: a bipartite graph with max degree <= d on n vertices. Moves insert a
# random opposite-side pair (a, b). If a or b already has degree d, a random
# incident edge is evicted first, so degrees never exceed d. Cost is the number
# of unordered pairs at distance > D (unreachable pairs count). Metropolis
# acceptance with a cyclic temperature schedule. Whenever cost reaches 0 the
# graph is recorded and one vertex is appended (on the smaller side). Output is
# the largest valid graph seen, or the input graph if none beat it.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1000
#define WMAX 16
#define MAXD 64

static int n, d, D, W;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static int side[MAXN];
static uint64_t ball[MAXN][WMAX];
static uint64_t tmpb[MAXN][WMAX];
static int best_n;
static int best_deg[MAXN];
static int best_nb[MAXN][MAXD];
static unsigned long long rs = 1;

static unsigned long long rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int adjacent(int a, int b) {
    for (int j = 0; j < deg[a]; j++)
        if (nb[a][j] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    for (int j = 0; j < deg[a]; j++) {
        if (nb[a][j] == b) {
            nb[a][j] = nb[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Number of unordered pairs at distance > D (unreachable counts as bad). */
static long long cost_bad(void) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) ball[v][w] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < D; s++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) tmpb[v][w] = ball[v][w];
            for (int j = 0; j < deg[v]; j++) {
                int u = nb[v][j];
                for (int w = 0; w < W; w++) tmpb[v][w] |= ball[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) ball[v][w] = tmpb[v][w];
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(ball[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int pick_pair(int *pa, int *pb) {
    for (int t = 0; t < 64; t++) {
        int a = rndint(n), b = rndint(n);
        if (side[a] == side[b] || adjacent(a, b)) continue;
        *pa = a;
        *pb = b;
        return 1;
    }
    return 0;
}

static void add_vertex(void) {
    int c0 = 0;
    for (int v = 0; v < n; v++)
        if (side[v] == 0) c0++;
    side[n] = (c0 * 2 <= n) ? 0 : 1;
    deg[n] = 0;
    n++;
}

static void save_best(void) {
    best_n = n;
    for (int v = 0; v < n; v++) {
        best_deg[v] = deg[v];
        memcpy(best_nb[v], nb[v], sizeof(int) * deg[v]);
    }
}

static void emit_best(void) {
    long long s = 0;
    for (int a = 0; a < best_n; a++) s += best_deg[a];
    printf("%d %lld\n", best_n, s / 2);
    for (int a = 0; a < best_n; a++)
        for (int j = 0; j < best_deg[a]; j++) {
            int b = best_nb[a][j];
            if (a < b) printf("%d %d\n", a, b);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    if (d < 1 || d >= MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 < 0 || n0 > MAXN - 8 || m0 < 0 || m0 > MAXN * d) {
        printf("0 0\n");
        return 0;
    }
    n = (n0 > 0) ? n0 : 2;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v || adjacent(u, v) ||
            deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    if (n0 == 0) add_edge(0, 1);

    static int stk[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int top = 0;
        stk[top++] = s;
        while (top > 0) {
            int u = stk[--top];
            for (int j = 0; j < deg[u]; j++) {
                int v = nb[u][j];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    stk[top++] = v;
                } else if (side[v] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    save_best();
    long long cur = cost_bad();
    clock_t t0 = clock();
    long long it = 0, stage = 0;
    const long long L = 50000;
    const double T0 = 1.2, T1 = 0.04;

    while (1) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;
        if (cur == 0) {
            save_best();
            if (n >= MAXN - 2) break;
            add_vertex();
            cur = cost_bad();
            stage = 0;
            continue;
        }
        stage++;
        double fr = (double)(stage % L) / (double)L;
        double T = T0 * pow(T1 / T0, fr);
        int a, b;
        if (!pick_pair(&a, &b)) continue;

        int ra[2], rb[2], nr = 0;
        if (deg[a] == d) {
            int x = nb[a][rndint(deg[a])];
            remove_edge(a, x);
            ra[nr] = a;
            rb[nr] = x;
            nr++;
        }
        if (deg[b] == d) {
            int y = nb[b][rndint(deg[b])];
            remove_edge(b, y);
            ra[nr] = b;
            rb[nr] = y;
            nr++;
        }
        add_edge(a, b);

        long long c2 = cost_bad();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            remove_edge(a, b);
            for (int k = 0; k < nr; k++) add_edge(ra[k], rb[k]);
        }
    }
    emit_best();
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
# Bipartite voltage lifts over small groups.
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
# Large-neighbourhood search (kill, repair, regrow).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# C annealing from the best Python graph (eviction-based edge insertion).
# ----------------------------------------------------------------------------

def _c_anneal(d, D, n, edges, seed, budget):
    """Run the C annealer for `budget` CPU seconds. Returns (n, edges); raises on failure."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=budget + 20.0)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Driver. Phases (fractions of T = 0.85 * time_limit, hard stop at 0.90):
#   A  structured base (W(q) or PG(2,q)) grown, twin trials, short LNS
#   L  voltage lifts over cyclic / semidirect groups
#   C  C annealer with eviction moves, grows the best graph by one vertex at a time
# Every candidate passes lib.is_valid before it is kept. The fallback is
# haar_graph(d, range(d)), which is valid for every d >= 1 and D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit
    hard_end = start + 0.90 * time_limit

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
            n1, e1 = _grow(n0, e0, d, D, at(0.06), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.10)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
        _lns(best_n, best_e, d, D, at(0.16), rng, consider)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.30):
        _lift_search(d, D, best_n, rng, at(0.30), consider)

    # Phase C: C annealer from the best valid graph found so far.
    if D >= 2 and d >= 3:
        budget = hard_end - time.monotonic() - 4.0
        if budget >= 3.0:
            try:
                n2, e2 = _c_anneal(d, D, best_n, best_e, seed, budget)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
