import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (voltage lift) search over a small group.
#
# The base graph has S vertices on each side, each of degree DEG. Dart k joins
# A-vertex i to B-vertex sig[k][i] with voltage vol[k][i] in the group G.
# The lift has vertices (side, fibre, x) and edges (A,i,x)-(B,j,x*g). Left
# multiplication by any h in G is an automorphism, so the diameter check only
# needs BFS from the 2S fibre representatives (x = identity). Simulated
# annealing on bad-pair cost; prints the lift when cost reaches 0.
# Group: typ 0 = cyclic Z_M; typ 1 = semidirect Z_m x| Z_k, element a*k+b.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXS 16
#define MAXD 16

static int S, DEG, DIAM, M, N;
static int *mt;
static int sig[MAXD][MAXS];
static int vol[MAXD][MAXS];
static int *adj, *cnt, *dist, *qb;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void build_group(int typ, int m, int k, int r) {
    mt = (int *)malloc(sizeof(int) * (size_t)M * (size_t)M);
    if (typ == 0) {
        for (int x = 0; x < M; x++)
            for (int y = 0; y < M; y++)
                mt[x * M + y] = (x + y) % M;
        return;
    }
    int *pw = (int *)malloc(sizeof(int) * (size_t)k);
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (pw[b - 1] * r) % m;
    for (int x = 0; x < M; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < M; y++) {
            int c = y / k, dd = y % k;
            mt[x * M + y] = ((a + pw[b] * c) % m) * k + (b + dd) % k;
        }
    }
    free(pw);
}

static void build_adj(void) {
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int i = 0; i < S; i++)
        for (int x = 0; x < M; x++) {
            int u = i * M + x;
            for (int k = 0; k < DEG; k++) {
                int w = (S + sig[k][i]) * M + mt[x * M + vol[k][i]];
                adj[u * DEG + cnt[u]++] = w;
                adj[w * DEG + cnt[w]++] = u;
            }
        }
}

static int cost(void) {
    int total = 0;
    for (int s = 0; s < 2 * S; s++) {
        int src = s * M;
        for (int v = 0; v < N; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        qb[tail++] = src;
        while (head < tail) {
            int u = qb[head++];
            if (dist[u] >= DIAM) continue;
            for (int k = 0; k < DEG; k++) {
                int w = adj[u * DEG + k];
                if (dist[w] < 0) { dist[w] = dist[u] + 1; qb[tail++] = w; }
            }
        }
        total += N - tail;
    }
    return total;
}

static int dup_ok(void) {
    for (int i = 0; i < S; i++)
        for (int k = 0; k < DEG; k++)
            for (int k2 = 0; k2 < k; k2++)
                if (sig[k][i] == sig[k2][i] && vol[k][i] == vol[k2][i]) return 0;
    return 1;
}

static int eval(void) { build_adj(); return cost(); }

static void random_init(void) {
    for (int k = 0; k < DEG; k++) {
        for (int i = 0; i < S; i++) sig[k][i] = i;
        for (int i = S - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = sig[k][i]; sig[k][i] = sig[k][j]; sig[k][j] = t;
        }
        for (int i = 0; i < S; i++) vol[k][i] = rndi(M);
    }
}

int main(int argc, char **argv) {
    if (argc < 11) return 1;
    S = atoi(argv[1]); M = atoi(argv[2]); DEG = atoi(argv[3]); DIAM = atoi(argv[4]);
    int typ = atoi(argv[5]), mm = atoi(argv[6]), kk = atoi(argv[7]), rr = atoi(argv[8]);
    uint64_t seed = (uint64_t)strtoull(argv[9], NULL, 10);
    double secs = atof(argv[10]);
    if (S < 1 || S > MAXS || DEG < 1 || DEG > MAXD || M < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    N = 2 * S * M;
    build_group(typ, mm, kk, rr);
    adj = (int *)malloc(sizeof(int) * (size_t)N * DEG);
    cnt = (int *)malloc(sizeof(int) * (size_t)N);
    dist = (int *)malloc(sizeof(int) * (size_t)N);
    qb = (int *)malloc(sizeof(int) * (size_t)N);

    clock_t t0 = clock();
    int found = 0;
    long total_iters = 0;
    while (!found) {
        int tries = 0;
        do { random_init(); } while (!dup_ok() && ++tries < 100000);
        if (!dup_ok()) break;
        int cur = eval();
        double T = 0.8;
        long since = 0;
        int best = cur;
        for (;;) {
            if (cur == 0) { found = 1; break; }
            total_iters++;
            if ((total_iters & 1023) == 0 &&
                (double)(clock() - t0) / CLOCKS_PER_SEC > secs)
                goto done;
            since++;
            if (since > 400000) break;  /* restart from a fresh random state */
            int k = rndi(DEG), i = rndi(S);
            int mv = rndi(2);
            int old_v = 0, i2 = -1;
            if (mv == 0) {
                old_v = vol[k][i];
                int nv = rndi(M);
                if (nv == old_v) continue;
                vol[k][i] = nv;
            } else {
                i2 = rndi(S);
                if (i2 == i) continue;
                int t = sig[k][i]; sig[k][i] = sig[k][i2]; sig[k][i2] = t;
            }
            int nc = dup_ok() ? eval() : -1;
            if (nc >= 0 && (nc <= cur || rndu() < exp(-(double)(nc - cur) / T))) {
                cur = nc;
                if (cur < best) { best = cur; since = 0; }
            } else {
                if (mv == 0) {
                    vol[k][i] = old_v;
                } else {
                    int t = sig[k][i]; sig[k][i] = sig[k][i2]; sig[k][i2] = t;
                }
            }
        }
    }

done:
    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", N, S * M * DEG);
    for (int i = 0; i < S; i++)
        for (int x = 0; x < M; x++)
            for (int k = 0; k < DEG; k++) {
                int u = i * M + x;
                int w = (S + sig[k][i]) * M + mt[x * M + vol[k][i]];
                printf("%d %d\n", u, w);
            }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue for the voltage-lift search.
# ----------------------------------------------------------------------------

def _group_specs(M):
    """Group descriptors (typ, m, k, r) of order M: cyclic first, then up to two semidirect products."""
    specs = [(0, M, 1, 0)]
    for k in range(2, M):
        if M % k:
            continue
        m = M // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append((1, m, k, r))
                break
        if len(specs) >= 3:
            break
    return specs


def _lift_stage(d, D, base_n, deadline, seed):
    """Run the C lift search on several (S, M, group) candidates above base_n. Returns (n, edges) or None."""
    moore = lib.moore_bound(d, D)
    cap = min(moore, 4000)
    cands = []
    for S in range(1, 9):
        lo = base_n // (2 * S) + 1
        hi = cap // (2 * S)
        for M in range(lo, min(hi, lo + 4, 1000) + 1):
            N = 2 * S * M
            if base_n < N <= cap:
                cands.append((N, S, M))
    cands.sort()
    tries = []
    for N, S, M in cands[:12]:
        for spec in _group_specs(M):
            tries.append((N, S, M, spec))
    best = None
    best_n = base_n
    fails = 0
    rounds = 0
    while tries and fails < 2 * len(tries):
        ran = False
        for N, S, M, spec in tries:
            left = deadline - time.monotonic()
            if left < 1.5:
                return best
            if N <= best_n:
                continue
            secs = min(2.5, left - 0.5)
            typ, mm, kk, rr = spec
            ran = True
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [S, M, d, D, typ, mm, kk, rr, seed * 7919 + rounds * 104729 + N, f"{secs:.2f}"],
                    timeout=secs + 30.0,
                )
                n, e = lib.parse_graph_text(out)
            except Exception:
                fails += 1
                continue
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best = n, (n, e)
        rounds += 1
        if not ran:
            break
    return best


# ----------------------------------------------------------------------------
# Legacy pipeline (projective / generalized quadrangle bases, growth, LNS).
# Kept as a strong, validated fallback.
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


# ----------------------------------------------------------------------------
# Cross-matching doubling with annealed repair.
# ----------------------------------------------------------------------------

def _double_cross(n, edges, d, D, rng, deadline):
    """Try to build a valid 2n-vertex graph from two cross-matched copies of a base graph.

    Returns (N, edges) when the repaired graph has zero bad pairs, else None.
    """
    N = 2 * n
    if N > lib.moore_bound(d, D):
        return None
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    B = [set() for _ in range(N)]
    for u in range(n):
        for v in adj[u]:
            B[u].add(v)
            B[u + n].add(v + n)
    spare = [d - len(adj[v]) for v in range(n)]
    s0 = [v for v in range(n) if color[v] == 0 for _ in range(spare[v])]
    s1 = [v for v in range(n) if color[v] == 1 for _ in range(spare[v])]
    rng.shuffle(s0)
    rng.shuffle(s1)
    t0 = list(s0)
    t1 = list(s1)
    rng.shuffle(t0)
    rng.shuffle(t1)
    for x, w in zip(s0, s1):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    for x, w in zip(t1, t0):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    color2 = color + [1 - c for c in color]
    _fill(B, color2, d, rng)
    while time.monotonic() < deadline:
        if _anneal(B, color2, d, D, rng, 3000, deadline):
            return N, [(u, v) for u in range(N) for v in B[u] if u < v]
        return None
    return None


def _try_doubling(n, edges, d, D, deadline, rng, consider):
    """Repeatedly attempt cross-matching doubling of the base until the deadline."""
    while time.monotonic() < deadline:
        res = _double_cross(n, edges, d, D, rng, deadline)
        if res is not None:
            N, e = res
            consider(N, e)
            return True
    return False


# ----------------------------------------------------------------------------
# Repair with an added vertex.
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
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
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

    if D >= 2 and 2 * base_n <= lib.moore_bound(d, D):
        dbl_end = start + 0.20 * time_limit
        _try_doubling(base_n, base_e, d, D, dbl_end, rng, consider)

    if D >= 2:
        trial_end = start + 0.10 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

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
    start = time.monotonic()
    deadline = start + 0.9 * time_limit

    # Legacy pipeline gives a validated structured graph first (guaranteed fallback).
    n_leg, e_leg = _legacy_build(d, D, seed, 0.5 * time_limit)
    best_n, best_e = n_leg, list(e_leg)

    # Bold stage: voltage lifts over small groups, searched in C, aiming above the legacy order.
    if d >= 3 and D >= 2 and best_n < lib.moore_bound(d, D):
        res = _lift_stage(d, D, best_n, deadline, seed)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best_n, best_e = res[0], list(res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
