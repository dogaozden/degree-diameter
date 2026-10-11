import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley graphs over semidirect products Z_M x|_r Z_K.
#
# Vertices: A-vertex x and B-vertex y (group elements). A x ~ B (x*s) for s in S,
# |S| = d. The group acts on each side by left multiplication, so the graph is
# valid iff BFS from A-identity and from B-identity reaches everything within D.
# Local search over S minimises the number of unreached vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXD 16

static int dd_, DD_, G_;
static int mulT[MAXG * MAXG];
static int invT[MAXG];
static int pw_[MAXG];
static int S_[MAXD], Si_[MAXD];
static char inS_[MAXG];
static int distv[2 * MAXG], stampv[2 * MAXG], queue_[2 * MAXG];
static int curstamp = 0;
static uint64_t rs_ = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) / 9007199254740992.0;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double now_s(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int build_group(int M, int K, int R) {
    int G = M * K;
    if (M < 1 || K < 1 || G > MAXG) return 0;
    G_ = G;
    pw_[0] = 1 % M;
    for (int b = 1; b < K; b++) pw_[b] = (pw_[b - 1] * (R % M)) % M;
    for (int x = 0; x < G; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < G; y++) {
            int c = y / K, e = y % K;
            int A = (a + pw_[b] * c) % M;
            int B = (b + e) % K;
            mulT[x * G + y] = A * K + B;
        }
    }
    for (int x = 0; x < G; x++) {
        invT[x] = -1;
        for (int y = 0; y < G; y++) {
            if (mulT[x * G + y] == 0) { invT[x] = y; break; }
        }
        if (invT[x] < 0) return 0;
    }
    return 1;
}

static int bfs_visits(int src) {
    int G = G_;
    curstamp++;
    int head = 0, tail = 0, visited = 1;
    queue_[tail++] = src;
    stampv[src] = curstamp;
    distv[src] = 0;
    while (head < tail) {
        int u = queue_[head++];
        int du = distv[u];
        if (du >= DD_) continue;
        if (u < G) {
            for (int i = 0; i < dd_; i++) {
                int v = G + mulT[u * G + S_[i]];
                if (stampv[v] != curstamp) {
                    stampv[v] = curstamp;
                    distv[v] = du + 1;
                    queue_[tail++] = v;
                    visited++;
                }
            }
        } else {
            int y = u - G;
            for (int i = 0; i < dd_; i++) {
                int v = mulT[y * G + Si_[i]];
                if (stampv[v] != curstamp) {
                    stampv[v] = curstamp;
                    distv[v] = du + 1;
                    queue_[tail++] = v;
                    visited++;
                }
            }
        }
    }
    return visited;
}

static int cost_now(void) {
    return (2 * G_ - bfs_visits(0)) + (2 * G_ - bfs_visits(G_));
}

static int search(double until) {
    int best = 1 << 30;
    while (now_s() < until) {
        for (int i = 0; i < G_; i++) inS_[i] = 0;
        for (int i = 0; i < dd_; i++) {
            int t;
            do { t = rndint(G_); } while (inS_[t]);
            inS_[t] = 1;
            S_[i] = t;
            Si_[i] = invT[t];
        }
        int cur = cost_now();
        int stall = 0;
        long it = 0;
        while (1) {
            if (cur == 0) return 1;
            if ((it & 127) == 0 && now_s() >= until) return 0;
            it++;
            int i = rndint(dd_);
            int t = rndint(G_);
            if (inS_[t]) continue;
            int old = S_[i];
            inS_[old] = 0;
            inS_[t] = 1;
            S_[i] = t;
            Si_[i] = invT[t];
            int nc = cost_now();
            int delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-2.0 * (double)delta)) {
                cur = nc;
            } else {
                inS_[t] = 0;
                inS_[old] = 1;
                S_[i] = old;
                Si_[i] = invT[old];
            }
            if (cur < best) {
                best = cur;
                stall = 0;
            } else if (++stall > 30000) {
                break;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd_ = atoi(argv[1]);
    DD_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double total = atof(argv[4]);
    rs_ = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs_ == 0) rs_ = 1;
    if (dd_ < 1 || dd_ > MAXD) { printf("0 0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0 0\n"); return 0; }
    int T = n;
    if (T <= 0 || T > 4096 || m != 2 * T) { printf("0 0 0\n"); return 0; }
    int *Mv = malloc(sizeof(int) * T);
    int *Kv = malloc(sizeof(int) * T);
    int *Rv = malloc(sizeof(int) * T);
    for (int i = 0; i < T; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) { printf("0 0 0\n"); return 0; }
        Mv[i] = a;
        Kv[i] = b;
    }
    for (int i = 0; i < T; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) { printf("0 0 0\n"); return 0; }
        Rv[i] = a;
    }

    double t0 = now_s();
    int bestG = 0, bM = 0, bK = 0, bR = 0;
    int bestS[MAXD];
    for (int ti = 0; ti < T; ti++) {
        double remain = total - (now_s() - t0);
        if (remain <= 0) break;
        int M = Mv[ti], K = Kv[ti], R = Rv[ti];
        int G = M * K;
        if (G <= bestG || G < dd_ || G > MAXG) continue;
        if (!build_group(M, K, R)) continue;
        double slice = remain / (double)(T - ti);
        if (search(now_s() + slice)) {
            bestG = G;
            bM = M; bK = K; bR = R;
            for (int i = 0; i < dd_; i++) bestS[i] = S_[i];
        }
    }
    if (bestG > 0) {
        printf("%d %d %d\n", bM, bK, bR);
        for (int i = 0; i < dd_; i++) printf("%d ", bestS[i]);
        printf("\n");
    } else {
        printf("0 0 0\n");
    }
    free(Mv);
    free(Kv);
    free(Rv);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Bi-Cayley search driver.
# ----------------------------------------------------------------------------

def _group_triples(lo, hi, rng):
    """One semidirect product (M, K, r) per group order g in [lo, hi], preferring non-abelian."""
    out = []
    for g in range(lo, hi + 1):
        opts = []
        for M in range(1, g + 1):
            if g % M:
                continue
            K = g // M
            if M == 1:
                opts.append((1, K, 0, True))
                continue
            for r in range(1, M):
                if math.gcd(r, M) == 1 and pow(r, K, M) == 1:
                    opts.append((M, K, r, r == 1))
        if not opts:
            continue
        nonab = [o for o in opts if not o[3]]
        pool = nonab if nonab and rng.random() < 0.75 else opts
        M, K, r, _ = rng.choice(pool)
        out.append((M, K, r))
    return out


def _bicayley(d, D, seed, budget):
    """Search bi-Cayley graphs over many groups; return (n, edges) or None."""
    hi = lib.moore_bound(d, D) // 2
    lo = max(d + 1, (2 * hi) // 3)
    if hi < lo:
        return None
    rng = random.Random(seed * 7919 + 17)
    trip = _group_triples(lo, hi, rng)
    if not trip:
        return None
    T = len(trip)
    edges_in = [(M, K) for M, K, _ in trip] + [(r, 0) for _, _, r in trip]
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(T, edges_in), timeout=budget * 1.5 + 10)
    tok = out.split()
    if len(tok) < 3 + d:
        return None
    M, K, r = int(tok[0]), int(tok[1]), int(tok[2])
    if M * K == 0:
        return None
    S = [int(x) for x in tok[3:3 + d]]
    order, mul, _ = lib.semidirect_group(M, K, r)
    edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
    n = 2 * order
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


# ----------------------------------------------------------------------------
# Previous pipeline (generalized quadrangle / projective plane growth,
# twin duplication, large-neighbourhood search). Kept as a strong fallback.
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
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
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
        trial_end = start + 0.12 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.8 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


# ----------------------------------------------------------------------------
# Entry point: bi-Cayley search first (bold), then the previous pipeline with
# the remaining time. Return the largest graph that passes lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best_n, best_e = lib.haar_graph(d, range(d))  # safe fallback, valid for D >= 2

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    if 3 <= d <= 15 and D >= 2:
        try:
            res = _bicayley(d, D, seed, 0.4 * time_limit)
        except Exception:
            res = None
        if res is not None and res[0] > best_n:
            best_n, best_e = res

    remain = 0.85 * time_limit - (time.monotonic() - t0)
    if remain > 2:
        try:
            n, e = _parent_build(d, D, seed, remain / 0.88)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, list(e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
