import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley hill climbing over a group Z_m x| Z_k.
#
# Vertices a_g = g and b_g = N + g, with N = m*k. Edges a_g -- b_{g s} for s in S,
# |S| = d. Left multiplication is an automorphism transitive on each side, so the
# diameter is at most D iff the eccentricities of a_e and b_e are at most D.
# The search minimises the number of vertices not reached within D steps from
# a_e and b_e, using swaps with sideways moves and random restarts.
# ----------------------------------------------------------------------------

BICAYLEY_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int d_, D_, N_, K_, M_, R_;
static int *mul_t = NULL;
static int *inv_t = NULL;
static int *S = NULL;
static char *inS = NULL;
static int *dist = NULL;
static int *queue = NULL;

static int group_mul(int x, int y, const int *pw) {
    int a = x / K_, b = x % K_;
    int c = y / K_, e = y % K_;
    long long t = ((long long)a + (long long)pw[b] * c) % M_;
    return (int)(t * K_ + (b + e) % K_);
}

static int build_group(void) {
    int *pw = malloc(sizeof(int) * (size_t)K_);
    if (!pw) return 0;
    pw[0] = 1 % M_;
    for (int b = 1; b < K_; b++) pw[b] = (int)(((long long)pw[b - 1] * R_) % M_);
    if ((((long long)pw[K_ - 1] * R_) % M_) != (1 % M_)) { free(pw); return 0; }
    mul_t = malloc(sizeof(int) * (size_t)N_ * (size_t)N_);
    inv_t = malloc(sizeof(int) * (size_t)N_);
    if (!mul_t || !inv_t) { free(pw); return 0; }
    for (int x = 0; x < N_; x++)
        for (int y = 0; y < N_; y++)
            mul_t[x * N_ + y] = group_mul(x, y, pw);
    free(pw);
    for (int x = 0; x < N_; x++) {
        inv_t[x] = -1;
        for (int y = 0; y < N_; y++) {
            if (mul_t[x * N_ + y] == 0) { inv_t[x] = y; break; }
        }
        if (inv_t[x] < 0) return 0;
    }
    return 1;
}

static int cost(void) {
    int d = d_, D = D_, N = N_;
    int total = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = (src == 0) ? 0 : N;
        for (int i = 0; i < 2 * N; i++) dist[i] = -1;
        int head = 0, tail = 0;
        dist[s0] = 0;
        queue[tail++] = s0;
        while (head < tail) {
            int v = queue[head++];
            int dv = dist[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = mul_t + (size_t)v * N;
                for (int j = 0; j < d; j++) {
                    int u = N + row[S[j]];
                    if (dist[u] < 0) { dist[u] = dv + 1; queue[tail++] = u; }
                }
            } else {
                int g = v - N;
                const int *row = mul_t + (size_t)g * N;
                for (int j = 0; j < d; j++) {
                    int u = row[inv_t[S[j]]];
                    if (dist[u] < 0) { dist[u] = dv + 1; queue[tail++] = u; }
                }
            }
        }
        total += 2 * N - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    M_ = atoi(argv[5]);
    K_ = atoi(argv[6]);
    R_ = atoi(argv[7]);
    if (d_ < 1 || D_ < 1 || M_ < 2 || K_ < 1 || R_ < 1 || R_ >= M_ || M_ * K_ > 2000) {
        printf("0 0\n");
        return 0;
    }
    N_ = M_ * K_;
    if (N_ < d_) { printf("0 0\n"); return 0; }
    if (!build_group()) { printf("0 0\n"); return 0; }
    S = malloc(sizeof(int) * (size_t)d_);
    inS = malloc((size_t)N_);
    dist = malloc(sizeof(int) * (size_t)(2 * N_));
    queue = malloc(sizeof(int) * (size_t)(2 * N_));
    if (!S || !inS || !dist || !queue) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd64();

    clock_t t0 = clock();
    int found = 0;
    long long evals = 0;
    while (!found) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC >= budget) break;
        memset(inS, 0, (size_t)N_);
        for (int j = 0; j < d_; j++) {
            int x;
            do { x = rnd_int(N_); } while (inS[x]);
            S[j] = x;
            inS[x] = 1;
        }
        int cur = cost();
        evals++;
        int stall = 0;
        while (cur > 0 && stall < 4000) {
            if ((evals & 63) == 0 &&
                (double)(clock() - t0) / CLOCKS_PER_SEC >= budget) break;
            int j = rnd_int(d_);
            int x = rnd_int(N_);
            if (inS[x]) { stall++; continue; }
            int old = S[j];
            inS[old] = 0;
            S[j] = x;
            inS[x] = 1;
            int nc = cost();
            evals++;
            if (nc < cur) {
                stall = 0;
                cur = nc;
            } else if (nc == cur) {
                stall++;
                cur = nc;
            } else if (rnd_int(1000) < 2) {
                stall++;
                cur = nc;
            } else {
                inS[x] = 0;
                S[j] = old;
                inS[old] = 1;
                stall++;
            }
        }
        if (cur == 0) found = 1;
    }
    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * N_, N_ * d_);
    for (int g = 0; g < N_; g++)
        for (int j = 0; j < d_; j++)
            printf("%d %d\n", g, N_ + mul_t[g * N_ + S[j]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions (unchanged from the parent for the structured bases).
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
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices.

    `attempts` bounds the randomized cover retries per growth step; the search
    loops use a small value so that failing cover checks do not dominate time.
    """
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
# Twin duplication.
#
# A vertex v' with N(v') = N(v), v' not adjacent to v, is a "twin" of v. In any
# graph, non-adjacent twins are at the same distance from every other vertex,
# and at distance 2 from each other. So duplicating a vertex never breaks the
# diameter bound (for D >= 2), keeps the graph bipartite (v' is on v's side),
# and needs only spare degree on the neighbours of v.
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
# Bi-Cayley ladder (new stage).
#
# Groups Z_m x| Z_k of order N give bipartite graphs of order 2N and degree d
# that are automatically vertex-transitive on each side. For each order N we ask
# the C engine for a diameter-D connection set, climbing N upward until several
# consecutive orders fail.
# ----------------------------------------------------------------------------

def _groups(N, rng, cap):
    """Candidate groups of order N as (m, k, r): Z_m x| Z_k with r^k = 1 mod m, plus cyclic Z_N."""
    cands = [(N, 1, 1)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    return cands[:cap]


def _bicayley_stage(d, D, deadline, rng, consider, seed):
    """Climb group orders N with the C bi-Cayley search; each success is passed to consider()."""
    max_N = lib.moore_bound(d, D) // 2
    N = max(d, lib.moore_bound(d, D) // 4, 2)
    misses = 0
    calls = 0
    while N <= max_N and misses < 3:
        if deadline - time.monotonic() < 0.5:
            break
        found = False
        for m, k, r in _groups(N, rng, 5):
            left = deadline - time.monotonic()
            budget = min(0.4, left - 0.3)
            if budget < 0.05:
                break
            calls += 1
            try:
                out = lib.run_c(BICAYLEY_C,
                                [d, D, seed * 7919 + calls, f"{budget:.3f}", m, k, r],
                                timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
            except Exception:
                continue
            if n > 0 and lib.is_valid(n, e, d, D):
                consider(n, e)
                found = True
                break
        misses = 0 if found else misses + 1
        N += 1


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
#
# Delete 1-3 vertices from a valid graph. Their neighbours regain spare degree,
# but distances may grow. Repair the diameter with bipartite double-edge
# switches (degrees preserved), then regrow with cover vertices and saturation.
# Cover growth keeps the diameter bound, so every accepted state stays valid.
# The walk is anchored: if it drifts too far below its best graph, it returns
# to that best graph instead of wandering off the plateau.
# ----------------------------------------------------------------------------

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
        # Switch a-b, c-e into a-e, c-b (a, c on side 0; b, e on side 1).
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
        k = rng.choice((1, 1, 2, 3))
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
        # Small retry budget per regrow step: the search needs many cheap rounds more than
        # exhaustive cover retries on each one.
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        # Accept sideways and slightly downward moves to drift across the plateau.
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            # Drifted too far below the best graph: return to it.
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
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured bases: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.2 * time_limit, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.3 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Kill-repair-regrow search from the best valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        _lns(best_n, best_e, d, D, start + 0.55 * time_limit, rng, consider)

    # New stage: bi-Cayley ladder over groups of growing order (C engine).
    if D >= 2 and d >= 2 and time.monotonic() < deadline:
        try:
            _bicayley_stage(d, D, start + 0.75 * time_limit, rng, consider, seed)
        except Exception:
            pass

    # Second LNS pass from the largest valid graph (possibly a bi-Cayley graph now).
    if D >= 2 and time.monotonic() < deadline:
        _lns(best_n, best_e, d, D, start + 0.8 * time_limit, rng, consider)

    # Bold stage: repeated add-and-repair from the largest valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
