# Voltage-lift search in C (new stage), with the parent's Python pipeline kept as fallback.
#
# New routine: a C annealer over lifts of a base bipartite multigraph with A vertices on each
# side and degree d, lifted over a group G = Z_m x| Z_k (k = 1 gives cyclic). Each side vertex
# (i, x) joins (j, x*g) for every dart (i, j, g). The B-endpoints of darts are a permutation of
# the multiset {i repeated d}, so every vertex keeps degree d. Moves change one voltage or swap
# two B-endpoints. The cost is the number of (representative, vertex) pairs at distance > D from
# the 2A orbit representatives, which is exact because left translation is an automorphism.
# Duplicate darts are penalised. The C stage tries random groups with order just above the
# current best and uses C speed to run many more anneal steps than the Python version.
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double runif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int d, D, A, m, k, ord, N, T;
static int *pw, *mulT, *dA, *dB, *dG, *adj, *cnt, *vis, *queue;
static int stamp = 0;

/* element code a*k+b represents (a,b) in Z_m x| Z_k with (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a1 = x / k, b1 = x % k, c1 = y / k, e1 = y % k;
    int a2 = (a1 + pw[b1] * c1) % m;
    int b2 = (b1 + e1) % k;
    return a2 * k + b2;
}

static long long cost_eval(void) {
    long long dup = 0;
    int off = A * ord;
    for (int s = 0; s < T; s++)
        for (int t = s + 1; t < T; t++)
            if (dA[s] == dA[t] && dB[s] == dB[t] && dG[s] == dG[t]) dup++;
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int t = 0; t < T; t++) {
        int i = dA[t], j = dB[t], g = dG[t];
        for (int x = 0; x < ord; x++) {
            int u = i * ord + x;
            int v = off + j * ord + mulT[x * ord + g];
            if (cnt[u] < d) adj[u * d + cnt[u]++] = v;
            if (cnt[v] < d) adj[v * d + cnt[v]++] = u;
        }
    }
    long long total = dup * 2LL * N;
    if (stamp > 1000000000) { memset(vis, 0, sizeof(int) * N); stamp = 0; }
    for (int si = 0; si < 2 * A; si++) {
        int src = si < A ? si * ord : off + (si - A) * ord;
        stamp++;
        int tail = 0, h = 0;
        queue[tail++] = src;
        vis[src] = stamp;
        for (int lev = 0; lev < D && h < tail; lev++) {
            int end = tail;
            for (; h < end; h++) {
                int u = queue[h];
                for (int q = 0; q < d; q++) {
                    int v = adj[u * d + q];
                    if (vis[v] != stamp) { vis[v] = stamp; queue[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    A = atoi(argv[5]);
    m = atoi(argv[6]);
    k = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d < 2 || D < 2 || A < 1 || m < 1 || k < 1) { printf("0 0\n"); return 0; }
    ord = m * k;
    if (ord > 1000) { printf("0 0\n"); return 0; }
    N = 2 * A * ord;
    T = A * d;

    pw = malloc(sizeof(int) * k);
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);

    mulT = malloc(sizeof(int) * ord * ord);
    for (int x = 0; x < ord; x++)
        for (int y = 0; y < ord; y++)
            mulT[x * ord + y] = gmul(x, y);

    dA = malloc(sizeof(int) * T);
    dB = malloc(sizeof(int) * T);
    dG = malloc(sizeof(int) * T);
    adj = malloc(sizeof(int) * N * d);
    cnt = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(int));
    queue = malloc(sizeof(int) * N);

    double tstart = now(), tend = tstart + tl;
    int found = 0;
    while (!found && now() < tend) {
        for (int t = 0; t < T; t++) {
            dA[t] = t / d;
            dB[t] = t / d;
            dG[t] = rint_(ord);
        }
        for (int t = T - 1; t > 0; t--) {
            int q = rint_(t + 1);
            int tmp = dB[t]; dB[t] = dB[q]; dB[q] = tmp;
        }
        long long cur = cost_eval();
        if (cur == 0) { found = 1; break; }
        double c0 = (double)(cur > 1 ? cur : 1);
        double T0 = 0.04 * c0 + 2.0, T1 = 0.3;
        const int EPOCH = 20000;
        for (int it = 0; it < EPOCH && !found; it++) {
            if ((it & 127) == 0 && now() >= tend) break;
            double temp = T0 * pow(T1 / T0, (double)it / (double)EPOCH);
            int k1 = rint_(T), k2 = rint_(T);
            int kind = rint_(10) < 7 ? 0 : 1;
            int og = dG[k1], ob1 = dB[k1], ob2 = dB[k2];
            if (kind == 0) {
                dG[k1] = rint_(ord);
            } else {
                int tmp = dB[k1]; dB[k1] = dB[k2]; dB[k2] = tmp;
            }
            long long c2 = cost_eval();
            if (c2 <= cur || runif() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
                if (cur == 0) { found = 1; break; }
            } else {
                if (kind == 0) dG[k1] = og;
                else { dB[k1] = ob1; dB[k2] = ob2; }
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    int off = A * ord;
    printf("%d %d\n", N, T * ord);
    for (int t = 0; t < T; t++)
        for (int x = 0; x < ord; x++)
            printf("%d %d\n", dA[t] * ord + x, off + dB[t] * ord + mulT[x * ord + dG[t]]);
    return 0;
}
'''


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
# Voltage lifts over small groups.
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
    """Pure-Python fallback: repeatedly search voltage lifts over random groups above the best order."""
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


def _c_lift_stage(d, D, get_best, rng, deadline, consider):
    """Run the C voltage annealer on random groups just above the current best order.

    Returns False if the C engine keeps failing (so the caller can use the Python fallback).
    """
    moore = lib.moore_bound(d, D)
    failures = 0
    while time.monotonic() < deadline - 2.5:
        best = get_best()
        pool = [a for a in (1, 2, 2, 3, 3) if best // (2 * a) + 1 <= moore // (2 * a)]
        if not pool:
            return True
        a = rng.choice(pool)
        lo = best // (2 * a) + 1
        hi = min(moore // (2 * a), lo + 20)
        specs = _group_specs(lo, hi)
        if not specs:
            continue
        spec = rng.choice(specs)
        if spec[0] == "cyc":
            m, k, r = spec[1], 1, 1
        else:
            _, m, k, r = spec
        remaining = deadline - time.monotonic()
        budget = min(rng.uniform(2.0, 5.0), remaining - 2.0)
        if budget < 0.5:
            break
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1 << 30), f"{budget:.2f}", a, m, k, r],
                            timeout=budget + 10.0)
            n, e = lib.parse_graph_text(out)
            failures = 0
        except Exception:
            failures += 1
            if failures >= 2:
                return False
            continue
        if n > best and lib.is_valid(n, e, d, D):
            consider(n, e)
    return True


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
# Redundant-edge pruning, then regrow.
# ----------------------------------------------------------------------------

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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Voltage-lift search: C annealer first, Python annealer if the C engine fails.
    lift_end = start + 0.60 * time_limit
    if time.monotonic() < lift_end:
        ok = _c_lift_stage(d, D, lambda: best_n, rng, lift_end, consider)
        if not ok and time.monotonic() < lift_end:
            _lift_stage(d, D, lambda: best_n, rng, lift_end, consider)

    # The best lift becomes the base for the randomized pipelines.
    base_n, base_e = best_n, list(best_e)

    # Randomized twin-duplication pipelines.
    trial_end = start + 0.70 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # Kill-repair-regrow search from the best valid graph found so far.
    if time.monotonic() < deadline:
        lns_end = start + 0.85 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # Prune redundant edges to free degree, then regrow from the best graph.
    if time.monotonic() < deadline:
        prune_end = start + 0.88 * time_limit
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
