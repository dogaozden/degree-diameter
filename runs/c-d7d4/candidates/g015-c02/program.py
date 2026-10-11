import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite double-edge-switch annealing with vertex insertion.
# Starts from a valid graph, repeatedly adds a vertex (evicting edges from
# saturated neighbours if needed), fills spare degree, and anneals the number
# of bad pairs (distance > D) back to zero. Each success is kept and the
# vertex count grows. Only zero-cost states are ever printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 8000
#define MAXD 40
#define MAXE 200000

static int N, DG, DIAM;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static int dist_[MAXN];
static int que[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double t_end = 0.0;

static int sN;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];

static int bestN = -1, bestM = 0;
static int bestA[MAXE], bestB[MAXE];

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
    }
}
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

static long long cost(void) {
    long long bad = 0;
    for (int s = 0; s < N; s++) {
        for (int i = 0; i < N; i++) dist_[i] = -1;
        int h = 0, t = 0, reached = 1;
        que[t++] = s;
        dist_[s] = 0;
        while (h < t) {
            int u = que[h++];
            if (dist_[u] >= DIAM) continue;
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (dist_[w] < 0) {
                    dist_[w] = dist_[u] + 1;
                    que[t++] = w;
                    reached++;
                }
            }
        }
        bad += N - reached;
    }
    return bad / 2;
}

static void snap(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) memcpy(sadj[v], adj[v], sizeof(int) * (size_t)deg[v]);
}

static void restore(void) {
    N = sN;
    memcpy(deg, sdeg, sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) memcpy(adj[v], sadj[v], sizeof(int) * (size_t)deg[v]);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int w = adj[u][i];
            if (u < w && m < MAXE) { bestA[m] = u; bestB[m] = w; m++; }
        }
    }
    bestM = m;
    bestN = N;
}

static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DG) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    if (nl == 0 || nr == 0) return;
    int tries = 20 * (nl + nr);
    for (int k = 0; k < tries; k++) {
        int a = L[rndi(nl)], b = R[rndi(nr)];
        if (deg[a] < DG && deg[b] < DG && !has_edge(a, b)) add_edge(a, b);
    }
}

static long long anneal(long long cur, int iters, double T0, double T1) {
    static int S0[MAXN];
    int ns0 = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0) S0[ns0++] = v;
    if (ns0 < 2) return cur;
    for (int it = 0; it < iters && cur > 0; it++) {
        if (now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a = S0[rndi(ns0)];
        if (deg[a] == 0) continue;
        int b = adj[a][rndi(deg[a])];
        int c = S0[rndi(ns0)];
        if (c == a || deg[c] == 0) continue;
        int e = adj[c][rndi(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long long nw = cost();
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
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

static void add_vertex(int side) {
    int v = N++;
    deg[v] = 0;
    col[v] = side;
    int added = 0, tries = 0;
    while (added < DG && tries < 50 * DG) {
        tries++;
        int u = rndi(v);
        if (col[u] == side || has_edge(u, v)) continue;
        if (deg[u] >= DG) {
            int w = adj[u][rndi(deg[u])];
            del_edge(u, w);
        }
        add_edge(u, v);
        added++;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= ((uint64_t)atoll(argv[3]) + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    int iters = argc > 5 ? atoi(argv[5]) : 400;
    if (iters < 10) iters = 10;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > MAXN - 4 ||
        DG < 1 || DG > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= N || b >= N || a == b) continue;
        if (deg[a] >= DG || deg[b] >= DG || has_edge(a, b)) continue;
        add_edge(a, b);
    }

    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        que[t++] = s;
        while (h < t) {
            int u = que[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) { col[w] = 1 - col[u]; que[t++] = w; }
            }
        }
    }
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (col[adj[u][i]] == col[u]) { printf("0 0\n"); return 0; }
        }
    }

    t_end = now() + budget;
    long long cur = cost();
    if (cur > 0) cur = anneal(cur, 20 * iters, 1.5, 0.05);
    if (cur == 0) save_best();

    while (cur == 0 && now() < t_end && N + 2 < MAXN) {
        snap();
        add_vertex(rndi(2));
        fill();
        long long c = cost();
        c = anneal(c, iters, 1.5, 0.05);
        if (c == 0) save_best();
        else restore();
    }

    if (bestN < 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestA[i], bestB[i]);
    return 0;
}
'''


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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
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
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Bipartite voltage lifts over small groups (cyclic or semidirect).
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
# C repair call.
# ----------------------------------------------------------------------------

def _c_repair(d, D, n, edges, budget, seed, iters):
    """Run the C annealing engine from a valid graph. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), iters],
                        stdin_graph=(n, edges), timeout=budget + 4.0)
        n2, e2 = lib.parse_graph_text(out)
        if n2 <= 0:
            return None
        return n2, e2
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Driver. Fractions of the usable span S = 0.88 * time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, twin trials
#   L  bipartite voltage lifts over small groups
#   C  C annealing with vertex insertion from the best valid graph, then regrow
# Every candidate passes lib.is_valid before it is kept. The fallback is
# haar_graph(d, range(d)), valid for every d >= 1 and D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = 0.88 * time_limit
    end = start + span

    def at(f):
        return start + f * span

    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # D = 2: K_{d,d} is the Moore-optimal graph.
    if D == 2:
        return best_n, list(best_e)

    # D = 3 with d-1 a prime power: PG(2, d-1) meets the bound; no search needed.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best_n, list(best_e)

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
            n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
            consider(n1, e1)

    trial_end = at(0.22)
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # Phase L: voltage lifts over small groups.
    if d >= 2 and time.monotonic() < at(0.35):
        _lift_search(d, D, best_n, rng, at(0.35), consider)

    # Phase C: C annealing from the best valid graph, then regrow in Python.
    budget = end - time.monotonic() - 3.0
    if budget >= 3.0 and d >= 2:
        res = _c_repair(d, D, best_n, best_e, budget, seed, 400)
        if res is not None:
            n_c, e_c = res
            consider(n_c, e_c)
            if time.monotonic() < end - 0.5:
                n2, e2 = _grow(best_n, best_e, d, D, end - 0.5, rng)
                consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
