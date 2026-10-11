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

/* Search for a bipartite Cayley ("Haar-type") graph on a finite group G:
 *   A-vertex x is adjacent to B-vertex x*s for s in S, |S| = DEG.
 * Left multiplication is an automorphism that is transitive on each side, so the
 * diameter is at most DIAM iff A-vertex 0 and B-vertex 0 both reach everything
 * within DIAM steps. Simulated annealing over S minimises the number of unreached
 * vertices. Input: "n m" then m lines "idx value" giving the multiplication table
 * mul[idx] with idx = x*G + y and identity element 0. Output: "OK s1 .. sDEG" or "FAIL".
 * argv: DEG DIAM seed time_limit G
 */

#define RESTART_ITERS 400000
#define TEMP 0.6

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int G, DEG, DIAM;
static int *mul, *inv_, *S, *inS, *dist, *queue;

static int reach_count(int src) {
    int N2 = 2 * G;
    for (int i = 0; i < N2; i++) dist[i] = -1;
    int head = 0, tail = 0;
    queue[tail++] = src;
    dist[src] = 0;
    while (head < tail) {
        int u = queue[head++];
        int du = dist[u];
        if (du >= DIAM) continue;
        if (u < G) {
            const int *row = mul + (size_t)u * G;
            for (int j = 0; j < DEG; j++) {
                int w = G + row[S[j]];
                if (dist[w] < 0) { dist[w] = du + 1; queue[tail++] = w; }
            }
        } else {
            int z = u - G;
            const int *row = mul + (size_t)z * G;
            for (int j = 0; j < DEG; j++) {
                int w = row[inv_[S[j]]];
                if (dist[w] < 0) { dist[w] = du + 1; queue[tail++] = w; }
            }
        }
    }
    return tail;
}

static int cost_of(void) {
    int a = reach_count(0);
    int b = reach_count(G);
    return (2 * G - a) + (2 * G - b);
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    double tl = atof(argv[4]);
    G = atoi(argv[5]);
    if (DEG < 1 || G < DEG || DIAM < 1) { printf("FAIL\n"); return 0; }

    long long cells = (long long)G * G;
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("FAIL\n"); return 0; }
    mul = malloc(sizeof(int) * (size_t)cells);
    inv_ = malloc(sizeof(int) * (size_t)G);
    S = malloc(sizeof(int) * (size_t)DEG);
    inS = malloc(sizeof(int) * (size_t)G);
    dist = malloc(sizeof(int) * (size_t)(2 * G));
    queue = malloc(sizeof(int) * (size_t)(2 * G));
    if (!mul || !inv_ || !S || !inS || !dist || !queue) { printf("FAIL\n"); return 0; }

    for (long long i = 0; i < cells; i++) mul[i] = -1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u >= 0 && (long long)u < cells && v >= 0 && v < G) mul[u] = v;
    }
    for (long long i = 0; i < cells; i++) if (mul[i] < 0) { printf("FAIL\n"); return 0; }
    for (int x = 0; x < G; x++) {
        inv_[x] = -1;
        for (int y = 0; y < G; y++) if (mul[(size_t)x * G + y] == 0) inv_[x] = y;
        if (inv_[x] < 0) { printf("FAIL\n"); return 0; }
    }

    clock_t t0 = clock();
    int found = 0;
    int timed_out = 0;
    long long iter = 0;
    while (!found && !timed_out) {
        memset(inS, 0, sizeof(int) * (size_t)G);
        for (int j = 0; j < DEG; j++) {
            int x;
            do { x = rndint(G); } while (inS[x]);
            S[j] = x;
            inS[x] = 1;
        }
        int cur = cost_of();
        if (cur == 0) { found = 1; break; }
        for (long long it = 0; it < RESTART_ITERS; it++) {
            if ((iter++ & 255) == 0) {
                if ((double)(clock() - t0) / CLOCKS_PER_SEC > tl) { timed_out = 1; break; }
            }
            int i = rndint(DEG);
            int x = rndint(G);
            if (inS[x]) continue;
            int old = S[i];
            inS[old] = 0;
            inS[x] = 1;
            S[i] = x;
            int nc = cost_of();
            int accept = (nc <= cur) || (rnd01() < exp(-(double)(nc - cur) / TEMP));
            if (accept) {
                cur = nc;
                if (cur == 0) { found = 1; break; }
            } else {
                inS[x] = 0;
                inS[old] = 1;
                S[i] = old;
            }
        }
    }

    if (found) {
        printf("OK");
        for (int j = 0; j < DEG; j++) printf(" %d", S[j]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (from the previous program).
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


# ----------------------------------------------------------------------------
# NEW bold stage: Cayley-type bipartite graphs on finite groups, searched in C.
#
# Group G of order N, connection set S of d distinct elements. Vertices A_x and
# B_x (x in G), with A_x ~ B_{x s} for s in S. Order 2N, degree d. Searching for
# S with diameter <= D is a much smaller problem than searching graphs directly,
# and the group can be cyclic or a semidirect product Z_a x|_r Z_k.
# ----------------------------------------------------------------------------

GROUP_SLICE = 1.2  # seconds of C annealing per (order, group) attempt


class _Best:
    """Holds the best valid graph found so far."""

    def __init__(self, n, e):
        self.n, self.e = n, list(e)

    def consider(self, d, D, n, e):
        if n > self.n and lib.is_valid(n, e, d, D):
            self.n, self.e = n, list(e)
            return True
        return False


def _group_candidates(N, rng):
    """Cyclic group of order N first, then up to two random semidirect products of order N."""
    cands = [("cyc",)]
    opts = []
    for k in range(2, N):
        if N % k != 0:
            continue
        a = N // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                opts.append((a, k, r))
    rng.shuffle(opts)
    cands += [("sd",) + o for o in opts[:2]]
    return cands


def _group_table(N, cand):
    """Flat multiplication table T[x*N + y] = x*y, with identity 0."""
    if cand[0] == "cyc":
        return [(x + y) % N for x in range(N) for y in range(N)]
    _, a, k, r = cand
    _, mulf, _ = lib.semidirect_group(a, k, r)
    return [mulf(x, y) for x in range(N) for y in range(N)]


def _try_group(N, cand, d, D, seed, tl):
    """Run the C annealer on one group. Returns (2N, edges) or None."""
    T = _group_table(N, cand)
    pairs = [(i, T[i]) for i in range(N * N)]
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{tl:.2f}", N],
                    stdin_graph=(N * N, pairs), timeout=tl + 30.0)
    toks = out.split()
    if len(toks) < 1 + d or toks[0] != "OK":
        return None
    S = [int(t) for t in toks[1:1 + d]]
    edges = [(x, N + T[x * N + s]) for x in range(N) for s in S]
    return 2 * N, edges


def _group_search(d, D, rng, deadline, best):
    """Sweep the group order upward from the current best, trying each candidate group."""
    hi = lib.moore_bound(d, D) // 2
    N = max(d, best.n // 2 + 1)
    while N <= hi:
        if time.monotonic() > deadline - 1.0:
            return
        success = False
        for cand in _group_candidates(N, rng):
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                return
            tl = min(GROUP_SLICE, remaining - 0.5)
            try:
                res = _try_group(N, cand, d, D, rng.randrange(1 << 30), tl)
            except Exception:
                res = None
            if res is not None:
                best.consider(d, D, res[0], res[1])
                success = True
                break
        N = max(N + 1, best.n // 2 + 1) if success else N + 1


def _optimize(d, D, rng, start, T, best):
    """Stages 2-4. Any exception leaves `best` at its last valid value."""
    # Stage 2: group search (bold, new construction).
    if D >= 2:
        _group_search(d, D, rng, start + 0.55 * T, best)

    # Stage 3: twin-duplication trials from the current best.
    if D >= 2 and time.monotonic() < start + 0.72 * T:
        trial_end = start + 0.72 * T
        while time.monotonic() < trial_end:
            n, e = _trial(best.n, best.e, d, D, rng, trial_end)
            best.consider(d, D, n, e)

    # Stage 4: add-and-repair from the current best.
    deadline = start + 0.85 * T
    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best.n, best.e, deadline, rng,
                lambda n, e: best.consider(d, D, n, e))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = _Best(fb_n, fb_e)
    moore = lib.moore_bound(d, D)

    try:
        # Stage 1: structured base (generalized quadrangle for D >= 4, projective plane for D = 3).
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                n0, e0 = base
                best.consider(d, D, n0, e0)
                n1, e1 = _grow(n0, e0, d, D, start + 0.12 * T, rng)
                best.consider(d, D, n1, e1)

        if best.n < moore:
            _optimize(d, D, rng, start, T, best)
    except Exception:
        pass

    if not lib.is_valid(best.n, best.e, d, D):
        return fb_n, list(fb_e)
    return best.n, list(best.e)
