import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (Haar-type) graph search over finite groups.
#
# Group G = Z_A x|_r Z_K, order N = A*K, element a*K+b. The graph has vertices
# (0,g) and (1,g), with (0,g) ~ (1,g*s) for s in S, |S| = d. It is d-regular and
# bipartite. Left multiplication is an automorphism, so only the two identity
# roots need BFS. Simulated annealing over S minimises the number of vertices
# beyond distance D from either root. Groups come from argv, and each group is
# tried in order (ascending order), so the last success is the largest.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define TEMP 0.6
#define STALL 3000
#define GROUP_CAP 0.2

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int dd, DD;
static int NG, KG, AG;
static int *mt = NULL;
static int *iv = NULL;
static int *S = NULL;
static int *Si = NULL;
static char *inS = NULL;
static int *vis = NULL;
static int *qu = NULL;
static int stamp = 0;
static clock_t t_start;
static unsigned long long steps = 0;

static double elapsed(void) {
    return (double)(clock() - t_start) / (double)CLOCKS_PER_SEC;
}

static void build_group(int A, int K, int r) {
    int N = A * K;
    NG = N; KG = K; AG = A;
    free(mt); free(iv); free(S); free(Si); free(inS); free(vis); free(qu);
    mt = malloc(sizeof(int) * (size_t)N * (size_t)N);
    iv = malloc(sizeof(int) * (size_t)N);
    S = malloc(sizeof(int) * (size_t)dd);
    Si = malloc(sizeof(int) * (size_t)dd);
    inS = calloc((size_t)N, 1);
    vis = calloc((size_t)(2 * N), sizeof(int));
    qu = malloc(sizeof(int) * (size_t)(2 * N));
    int *pw = malloc(sizeof(int) * (size_t)K);
    pw[0] = 1 % A;
    for (int b = 1; b < K; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % A);
    for (int x = 0; x < N; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < N; y++) {
            int c = y / K, e = y % K;
            int pa = (int)((a + (long long)pw[b] * c) % A);
            int pb = (b + e) % K;
            mt[x * N + y] = pa * K + pb;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x * N + y] == 0) { iv[x] = y; break; }
    free(pw);
}

static int reach_count(int root) {
    int N = NG;
    stamp++;
    int tail = 0, head = 0;
    qu[tail++] = root;
    vis[root] = stamp;
    for (int depth = 0; depth < DD && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            if (v < N) {
                const int *row = mt + (size_t)v * (size_t)N;
                for (int i = 0; i < dd; i++) {
                    int w = N + row[S[i]];
                    if (vis[w] != stamp) { vis[w] = stamp; qu[tail++] = w; }
                }
            } else {
                const int *row = mt + (size_t)(v - N) * (size_t)N;
                for (int i = 0; i < dd; i++) {
                    int w = row[Si[i]];
                    if (vis[w] != stamp) { vis[w] = stamp; qu[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

static int cost(void) {
    int n2 = 2 * NG;
    return (n2 - reach_count(0)) + (n2 - reach_count(NG));
}

static int search_group(double cap) {
    int N = NG;
    while (elapsed() < cap) {
        memset(inS, 0, (size_t)N);
        int cnt = 0;
        while (cnt < dd) {
            int c = rndint(N);
            if (!inS[c]) { inS[c] = 1; S[cnt++] = c; }
        }
        for (int i = 0; i < dd; i++) Si[i] = iv[S[i]];
        int cur = cost();
        int stall = 0;
        while (cur > 0 && stall < STALL) {
            steps++;
            if ((steps & 255ULL) == 0 && elapsed() >= cap) break;
            int i = rndint(dd);
            int c = rndint(N);
            if (inS[c]) continue;
            int old = S[i];
            inS[old] = 0; inS[c] = 1; S[i] = c; Si[i] = iv[c];
            int nw = cost();
            int accept = 0;
            if (nw <= cur) accept = 1;
            else if (rnd01() < exp(-(double)(nw - cur) / TEMP)) accept = 1;
            if (accept) {
                if (nw < cur) stall = 0; else stall++;
                cur = nw;
            } else {
                inS[c] = 0; inS[old] = 1; S[i] = old; Si[i] = iv[old];
                stall++;
            }
        }
        if (cur == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = 88172645463325252ULL ^ (seed * 0x9E3779B97F4A7C15ULL);
    if (rs == 0) rs = 1;
    t_start = clock();

    int G = (argc - 5) / 3;
    int bestN = 0, bestA = 0, bestK = 0, bestR = 0;
    int *bestS = malloc(sizeof(int) * (size_t)(dd > 0 ? dd : 1));

    for (int g = 0; g < G; g++) {
        int A = atoi(argv[5 + 3 * g]);
        int K = atoi(argv[6 + 3 * g]);
        int r = atoi(argv[7 + 3 * g]);
        int N = A * K;
        if (N < dd || N <= bestN) continue;
        if (elapsed() >= budget) break;
        build_group(A, K, r);
        double cap = elapsed() + GROUP_CAP;
        if (cap > budget) cap = budget;
        if (search_group(cap)) {
            bestN = N; bestA = A; bestK = K; bestR = r;
            memcpy(bestS, S, sizeof(int) * (size_t)dd);
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    build_group(bestA, bestK, bestR);
    int N = bestN;
    printf("%d %d\n", 2 * N, N * dd);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < dd; i++)
            printf("%d %d\n", g, N + mt[g * N + bestS[i]]);
    return 0;
}
"""


def _group_specs(N, limit=3):
    """Group descriptors (A, K, r) for order N: cyclic first, then semidirect and direct products."""
    specs = [(N, 1, 1)]
    for K in range(2, N):
        if N % K:
            continue
        A = N // K
        if A < 2:
            continue
        specs.append((A, K, 1))
        for r in range(2, A):
            if math.gcd(r, A) == 1 and pow(r, K, A) == 1:
                specs.append((A, K, r))
    return specs[:limit]


# ----------------------------------------------------------------------------
# Parent pipeline (unchanged search; used as the structured fallback).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list.

    Adding cross-side edges keeps the graph bipartite and degrees <= d, and can only
    shorten distances, so a valid graph stays valid.
    """
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


def _spare_matching_base(n0, e0, d, rng, keep_free):
    n = n0
    half = n // 2
    adj = _to_sets(n, e0)
    rounds = d - max(len(a) for a in adj)
    for _ in range(max(0, rounds)):
        order = [p for p in range(half) if len(adj[p]) < d]
        rng.shuffle(order)
        target = max(0, len(order) - keep_free)
        count = 0
        for p in order:
            if count >= target:
                break
            cands = [L for L in range(half, n) if len(adj[L]) < d and L not in adj[p]]
            if not cands:
                continue
            L = rng.choice(cands)
            adj[p].add(L)
            adj[L].add(p)
            count += 1
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


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


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


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


def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
            pe = _prune_redundant(m, e, D, rng, deadline, 200)
            adj = _to_sets(m, pe)
            color = _bipartition(m, adj)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
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

    base_n, base_e = best_n, list(best_e)
    base_is_gq = False
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is not None:
            base_is_gq = True
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            grow_end = start + 0.2 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.10 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if base_is_gq and D >= 4 and time.monotonic() < deadline:
        spare_end = start + 0.20 * time_limit
        while time.monotonic() < spare_end:
            keep = rng.choice((0, 2, 4, 8, 12, 20))
            sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
            gn, ge = _grow(sn, se, d, D, spare_end, rng)
            consider(gn, ge)

    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.55 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        prune_end = start + 0.75 * time_limit
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    # Structured parent first (safe fallback, about 40% of the budget).
    pn, pe = _parent_build(d, D, seed, 0.4 * time_limit)
    if not lib.is_valid(pn, pe, d, D):
        pn, pe = lib.haar_graph(d, range(d))
    best_n, best_e = pn, list(pe)

    moore = lib.moore_bound(d, D)
    if D < 2 or d < 3 or best_n >= moore:
        return best_n, best_e

    # Bi-Cayley search over groups of order N, aiming for 2N > best_n.
    lo = best_n // 2 + 1
    hi = min(moore // 2, lo + 120)
    if lo > hi:
        return best_n, best_e
    specs = []
    for N in range(lo, hi + 1):
        if N >= d:
            specs += _group_specs(N)
    if not specs:
        return best_n, best_e

    elapsed = time.monotonic() - t0
    c_budget = 0.85 * time_limit - elapsed - 2.0
    if c_budget < 1.0:
        return best_n, best_e

    args = [d, D, seed, round(c_budget, 2)]
    for A, K, r in specs:
        args += [A, K, r]
    try:
        timeout = max(5.0, time_limit - (time.monotonic() - t0) - 1.0)
        text = lib.run_c(C_SOURCE, args, timeout=timeout)
        n, e = lib.parse_graph_text(text)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
    except Exception:
        pass

    return best_n, best_e
