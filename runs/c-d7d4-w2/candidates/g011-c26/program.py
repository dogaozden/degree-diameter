import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite Cayley (group Haar) graph search.
#
# Group G = Z_m x|_r Z_k (element (a,b) coded as a*k+b). Connection set S of size d.
# Vertices a_x (0..N-1) and b_y (N..2N-1), edges a_x -- b_{x s} for s in S.
# Left multiplication is an automorphism, so the diameter is <= D iff BFS from a_e
# and from b_e reaches everything within D. Local search over S minimises the
# number of bad pairs; the first valid graph found at the largest order is printed.
# ----------------------------------------------------------------------------

GROUP_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 512
#define MAXD 64
#define MAXC 4096
#define ITER 3000

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int d_, D_;
static int N_, M_, K_, R_;
static int powr[MAXN];
static int mulT[MAXN][MAXN];
static int invT[MAXN];
static int S_[MAXD];

typedef struct { int m, k, r; } Grp;
static Grp cands[MAXC];
static int ncand;

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static long powmod(long b, int e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gmul(int x, int y) {
    int a = x / K_, b = x % K_, c = y / K_, e = y % K_;
    int aa = (a + powr[b] * c) % M_;
    int bb = (b + e) % K_;
    return aa * K_ + bb;
}

static void build_cands(int N) {
    ncand = 0;
    for (int k = 1; k <= 12 && k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m == 1) {
            if (ncand < MAXC) { cands[ncand].m = 1; cands[ncand].k = k; cands[ncand].r = 0; ncand++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ncand < MAXC) { cands[ncand].m = m; cands[ncand].k = k; cands[ncand].r = r; ncand++; }
        }
    }
}

static void set_group(Grp g) {
    M_ = g.m; K_ = g.k; R_ = g.r;
    N_ = M_ * K_;
    powr[0] = 1 % M_;
    for (int b = 1; b < K_; b++) powr[b] = (int)((long)powr[b - 1] * R_ % M_);
    for (int x = 0; x < N_; x++)
        for (int y = 0; y < N_; y++)
            mulT[x][y] = gmul(x, y);
    for (int x = 0; x < N_; x++) {
        invT[x] = -1;
        for (int t = 0; t < N_; t++)
            if (mulT[x][t] == 0) { invT[x] = t; break; }
    }
}

/* Number of (source, vertex) pairs at distance > D_, sources a_e and b_e. */
static int cost(void) {
    int N = N_, d = d_;
    int invs[MAXD];
    for (int i = 0; i < d; i++) invs[i] = invT[S_[i]];
    static int dist[2 * MAXN];
    static int q[2 * MAXN];
    int total = 0;
    for (int src = 0; src < 2; src++) {
        for (int v = 0; v < 2 * N; v++) dist[v] = -1;
        int s0 = src ? N : 0;
        int head = 0, tail = 0;
        dist[s0] = 0;
        q[tail++] = s0;
        while (head < tail) {
            int v = q[head++];
            int dv = dist[v];
            if (dv >= D_) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int w = N + mulT[v][S_[i]];
                    if (dist[w] < 0) { dist[w] = dv + 1; q[tail++] = w; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int w = mulT[y][invs[i]];
                    if (dist[w] < 0) { dist[w] = dv + 1; q[tail++] = w; }
                }
            }
        }
        total += 2 * N - tail;
    }
    return total;
}

static void print_graph(int N, int d) {
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + mulT[x][S_[i]]);
}

static int search_N(int N, double deadline, int d) {
    build_cands(N);
    if (ncand == 0) return 0;
    while (now_sec() < deadline) {
        set_group(cands[rndint(ncand)]);
        for (int i = 0; i < d; i++) {
            int t, ok;
            do {
                t = rndint(N);
                ok = 1;
                for (int j = 0; j < i; j++) if (S_[j] == t) ok = 0;
            } while (!ok);
            S_[i] = t;
        }
        int cur = cost();
        for (int it = 0; it < ITER && cur > 0; it++) {
            int i = rndint(d);
            int t = rndint(N);
            int dup = 0;
            for (int j = 0; j < d; j++) if (S_[j] == t) dup = 1;
            if (dup) continue;
            int old = S_[i];
            S_[i] = t;
            int c = cost();
            if (c <= cur || rndint(64) == 0) cur = c;
            else S_[i] = old;
        }
        if (cur == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d_ < 2 || D_ < 2) { printf("0 0\n"); return 0; }

    double t0 = now_sec();
    double end = t0 + budget;

    /* Per-side Moore-type bound: sum_{i<D} (d-1)^i. */
    long hi = 0, p = 1;
    for (int i = 0; i < D_; i++) {
        hi += p;
        p *= (d_ - 1);
        if (p > 100000) p = 100000;
    }
    if (hi > MAXN - 1) hi = MAXN - 1;
    long lo = hi * 6 / 10;
    if (lo < d_ + 1) lo = d_ + 1;
    if (hi < d_ + 1) { printf("0 0\n"); return 0; }

    for (long N = hi; N >= lo; N--) {
        double tnow = now_sec();
        double slot = (end - tnow) / (double)(N - lo + 1);
        if (slot <= 0) break;
        if (search_N((int)N, tnow + slot, d_)) {
            print_graph((int)N, d_);
            return 0;
        }
    }
    printf("0 0\n");
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
# Large-neighbourhood search (kill, repair, regrow).
#
# Delete 1-4 vertices from a valid graph. Their neighbours regain spare degree,
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


def _local_kill(n, adj, k, rng):
    """Pick k vertices forming a connected cluster (BFS-like from a random seed vertex).

    Removing a contiguous cluster frees degree exactly where the repair has to
    reconnect, which is usually more productive than scattered random deletions.
    """
    v = rng.randrange(n)
    kill = {v}
    frontier = [v]
    while len(kill) < k and frontier:
        x = frontier.pop(rng.randrange(len(frontier)))
        nb = list(adj[x])
        rng.shuffle(nb)
        for u in nb:
            if len(kill) >= k:
                break
            if u not in kill:
                kill.add(u)
                frontier.append(u)
    while len(kill) < k:
        kill.add(rng.randrange(n))
    return kill


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        if rng.random() < 0.6:
            full_adj = _to_sets(cur_n, cur_e)
            kill = _local_kill(cur_n, full_adj, k, rng)
        else:
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
        # Accept sideways and slightly downward moves to drift across the plateau.
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            # Drifted too far below the best graph: return to it.
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Redundant-edge pruning, then regrow.
#
# An edge is redundant if deleting it keeps every pair within distance D. Deleting
# redundant edges frees degree on both endpoints without breaking validity. The
# freed slots are then used by cover growth, which can add new vertices that a
# fixed edge set could not accommodate. Every intermediate graph is checked with
# the exact bad-pair count, so the walk only moves through valid graphs.
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


# ----------------------------------------------------------------------------
# Repair with pruning between additions.
#
# After each successful vertex addition, redundant edges are pruned. This frees
# degree on the current graph, so the next added vertex has more room to attach
# before annealing has to repair the diameter. Pruning keeps the diameter bound,
# so the state stays valid throughout.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Driver pieces.
# ----------------------------------------------------------------------------

def _group_search(d, D, seed, budget):
    """Run the C group-Cayley search. Returns a valid (n, edges) or None."""
    try:
        out = lib.run_c(GROUP_C, [d, D, seed, round(budget, 2)], timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 2 or not lib.is_valid(n, e, d, D):
        return None
    return n, e


def _pipeline(d, D, rng, t0, tl, best_n, best_e):
    """Parent pipeline, with its time fractions measured from t0 over a budget of tl seconds."""
    best = [best_n, list(best_e)]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, list(e)

    base_n, base_e = best[0], list(best[1])
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            if n0 > base_n:
                base_n, base_e = n0, list(e0)
        n1, e1 = _grow(base_n, base_e, d, D, t0 + 0.2 * tl, rng)
        consider(n1, e1)

    # Randomized twin-duplication pipelines from the base (short, cheap).
    if D >= 2:
        trial_end = t0 + 0.10 * tl
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    deadline = t0 + 0.88 * tl

    # Kill-repair-regrow search from the best valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        _lns(best[0], best[1], d, D, t0 + 0.55 * tl, rng, consider)

    # Prune redundant edges to free degree, then regrow from the best graph.
    if D >= 2 and time.monotonic() < deadline:
        _prune_regrow(best[0], best[1], d, D, t0 + 0.75 * tl, rng, consider)

    # Add-and-repair (with pruning) from the best valid graph.
    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best[0], best[1], deadline, rng, consider)

    return best[0], best[1]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    # New stage: bipartite Cayley (group Haar) graphs over Z_m x| Z_k, searched in C.
    if D >= 4 and d >= 4:
        g = _group_search(d, D, seed, 0.35 * time_limit)
        if g is not None and g[0] > best_n:
            best_n, best_e = g

    # Parent pipeline from the best base so far, using the remaining time.
    rest = 0.85 * time_limit - (time.monotonic() - start)
    if D >= 2 and rest > 2.0:
        best_n, best_e = _pipeline(d, D, rng, time.monotonic(), rest, best_n, best_e)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
