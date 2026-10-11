import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar-graph search.
#
# H(m, S) has parts a_i, b_j (i, j in Z_m) and edges a_i - b_{i+s} for s in S,
# so it is bipartite and |S|-regular on 2m vertices. Let P = S - S (contains 0).
# Then a_0 reaches a_x within distance D iff x is in P^(floor(D/2)), and a_0
# reaches b_x within distance D iff x is in P^(floor((D-1)/2)) + S. Every pair
# of vertices is related by a translation (and the side swap is symmetric), so
# diameter <= D holds exactly when both sets cover Z_m. The engine searches
# S by simulated annealing for the largest m it can cover.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 2048
#define MAXD 24
#define MAXDIAM 12

static uint64_t rs = 88172645463325252ULL;
static int M = 1, Dd = 1, Dg = 1, ns = 0;
static int S[MAXD];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}

static double urand(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double cpu_now(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

/* out = X (+) Y, where X is a 0/1 mask over Z_M and Y is a list of residues. */
static void sumset_mask_list(const unsigned char *X, const int *Y, int ny, unsigned char *out) {
    memset(out, 0, (size_t)M);
    for (int x = 0; x < M; x++) {
        if (!X[x]) continue;
        for (int k = 0; k < ny; k++) {
            int z = x + Y[k];
            if (z >= M) z -= M;
            out[z] = 1;
        }
    }
}

/* Number of (a, b) pairs-of-residues left uncovered; 0 means diameter <= Dg. */
static int cover_cost(const int *Sv, int nsv) {
    static unsigned char inP[MAXM], A[MAXM], B[MAXM];
    static int P[MAXM];
    int np = 0;
    memset(inP, 0, (size_t)M);
    for (int i = 0; i < nsv; i++) {
        for (int j = 0; j < nsv; j++) {
            int r = Sv[i] - Sv[j];
            if (r < 0) r += M;
            if (!inP[r]) { inP[r] = 1; P[np++] = r; }
        }
    }
    /* same-side cover: P^(Dg/2) */
    memset(A, 0, (size_t)M);
    A[0] = 1;
    int K = Dg / 2;
    for (int k = 0; k < K; k++) {
        sumset_mask_list(A, P, np, B);
        memcpy(A, B, (size_t)M);
    }
    int ce = 0;
    for (int x = 0; x < M; x++) ce += A[x];
    /* opposite-side cover: P^((Dg-1)/2) (+) S */
    memset(A, 0, (size_t)M);
    A[0] = 1;
    int K2 = (Dg - 1) / 2;
    for (int k = 0; k < K2; k++) {
        sumset_mask_list(A, P, np, B);
        memcpy(A, B, (size_t)M);
    }
    sumset_mask_list(A, Sv, nsv, B);
    int co = 0;
    for (int x = 0; x < M; x++) co += B[x];
    return (M - ce) + (M - co);
}

static int in_S(int v) {
    for (int i = 0; i < ns; i++) if (S[i] == v) return 1;
    return 0;
}

static void random_init(void) {
    ns = Dd;
    for (int i = 0; i < Dd; i++) {
        int v;
        int clash;
        do {
            v = (int)(rnd64() % (uint64_t)M);
            clash = 0;
            for (int j = 0; j < i; j++) if (S[j] == v) { clash = 1; break; }
        } while (clash);
        S[i] = v;
    }
}

static int anneal(int iters) {
    int cur = cover_cost(S, ns);
    for (int it = 0; it < iters && cur > 0; it++) {
        int i = (int)(rnd64() % (uint64_t)ns);
        int old = S[i];
        int v;
        do { v = (int)(rnd64() % (uint64_t)M); } while (in_S(v));
        S[i] = v;
        int nc = cover_cost(S, ns);
        int delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / 0.7)) {
            cur = nc;
        } else {
            S[i] = old;
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    Dd = atoi(argv[1]);
    Dg = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    int mstart = argc > 5 ? atoi(argv[5]) : Dd + 1;
    if (Dd < 2 || Dd > MAXD || Dg < 2 || Dg > MAXDIAM) { printf("0 0\n"); return 0; }

    double end = cpu_now() + tl;
    int best_m = 0;
    int bestS[MAXD];
    M = mstart > Dd + 1 ? mstart : Dd + 1;

    while (M < MAXM) {
        double slice = tl * 0.12;
        if (slice < 0.2) slice = 0.2;
        double slice_end = cpu_now() + slice;
        if (slice_end > end) slice_end = end;
        int ok = 0;
        while (!ok && cpu_now() < slice_end) {
            random_init();
            ok = anneal(20000);
            if (ok) {
                memcpy(bestS, S, sizeof(int) * (size_t)Dd);
                best_m = M;
            }
        }
        if (!ok) break;
        M++;
        if (cpu_now() >= end) break;
    }

    if (best_m == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * best_m, best_m * Dd);
    for (int i = 0; i < best_m; i++) {
        for (int k = 0; k < Dd; k++) {
            printf("%d %d\n", i, best_m + (i + bestS[k]) % best_m);
        }
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
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """A dense structured graph whose degree is at least d (q = smallest prime power >= d)."""
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
# Thinning a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

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
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


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
# Driver.
#   H  NEW: cyclic Haar graphs H(Z_m, S) searched in C (about 35% of the budget)
#   A  structured small base (W(q) or PG(2,q)) grown, twin trials, LNS
#   B  thinned dense graph (degree reduction + vertex deletion), repeated
#   C  LNS from the best valid graph found so far
#   D  redundant-edge pruning and regrowth from the best graph
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

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

    # Phase H: cyclic Haar search in C. Any failure leaves the fallback in place.
    if D >= 3 and 2 <= d <= 24:
        h_budget = 0.35 * T
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(h_budget, 2), d + 1],
                            timeout=h_budget + 4.0)
            hn, he = lib.parse_graph_text(out)
            consider(hn, he)
        except (RuntimeError, ValueError):
            pass

    # The remaining phases share what is left of the budget.
    t0 = time.monotonic()
    span = max(0.0, start + T - t0)

    def at(f):
        return t0 + f * span

    # Phase A: structured small base, as in the parent.
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
        _lns(best_n, best_e, d, D, at(0.40), rng, consider)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.55):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.55):
                r = _deletion_trial(d, D, rn, re, rng, at(0.55))
                if r is None:
                    break
                consider(*r)

    # Phase C: LNS from the best valid graph of any construction.
    if D >= 2 and time.monotonic() < at(0.75):
        _lns(best_n, best_e, d, D, at(0.75), rng, consider)

    # Phase D: prune redundant edges and regrow from the best graph.
    if D >= 2 and time.monotonic() < at(1.0):
        _prune_regrow(best_n, best_e, d, D, at(1.0), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
