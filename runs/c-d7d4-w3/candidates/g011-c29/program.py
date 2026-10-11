# New in this version: the voltage-lift search moves into C. A C annealer searches
# lifts of base graphs with a in {1, 2, 3} sides over cyclic and semidirect groups.
# Each base side has degree d, and the cost is the number of (representative, vertex)
# pairs at distance > D, from one representative per side. Left translation is an
# automorphism, so this count is exact. The Python gluing (group tables, edge
# expansion, validation) and the parent's GQ/PG base, twin duplication, LNS and
# pruning stages are kept.
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

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int A, DEG, DD, M, NV;
static int *RT;      /* RT[g*M + x] = x*g in the group */
static int *adj;     /* NV*DEG neighbour slots */
static int *fillc;
static int *stamp;
static int curstamp = 0;
static int *fr, *nf;

static void build_adj(const int *G, const int *J) {
    int nd = A * DEG;
    for (int v = 0; v < NV; v++) fillc[v] = 0;
    for (int k = 0; k < nd; k++) {
        int i = k / DEG, j = J[k], g = G[k];
        const int *Rg = RT + (size_t)g * M;
        for (int x = 0; x < M; x++) {
            int u = i * M + x;
            int v = A * M + j * M + Rg[x];
            adj[(size_t)u * DEG + fillc[u]++] = v;
            adj[(size_t)v * DEG + fillc[v]++] = u;
        }
    }
}

static long cost_eval(void) {
    long total = 0;
    int nsrc = 2 * A;
    for (int s = 0; s < nsrc; s++) {
        int src = (s < A) ? s * M : A * M + (s - A) * M;
        if (curstamp >= 0x7ffffff0) {
            memset(stamp, 0, sizeof(int) * (size_t)NV);
            curstamp = 0;
        }
        curstamp++;
        int fs = 0, reached = 1;
        fr[fs++] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DD && fs > 0; lvl++) {
            int ns = 0;
            for (int q = 0; q < fs; q++) {
                int u = fr[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        nf[ns++] = v;
                    }
                }
            }
            reached += ns;
            int *tmp = fr; fr = nf; nf = tmp;
            fs = ns;
        }
        total += NV - reached;
    }
    return total;
}

static void fresh_state(int *G, int *J) {
    int nd = A * DEG;
    for (int k = 0; k < nd; k++) {
        J[k] = k / DEG;
        G[k] = rndint(M);
    }
    for (int k = nd - 1; k > 0; k--) {
        int r = rndint(k + 1);
        int t = J[k]; J[k] = J[r]; J[r] = t;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("FAIL usage\n"); return 0; }
    A = atoi(argv[1]);
    DEG = atoi(argv[2]);
    DD = atoi(argv[3]);
    double secs = atof(argv[4]);
    rs ^= (uint64_t)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 16; w++) rnd64();

    int hn = 0, cnt = 0;
    if (scanf("%d %d", &hn, &cnt) != 2 || hn < 1 || cnt != hn * hn) {
        printf("FAIL input\n");
        return 0;
    }
    M = hn;
    RT = malloc(sizeof(int) * (size_t)cnt);
    for (int p = 0; p < cnt; p++) {
        int u = 0, v = 0;
        if (scanf("%d %d", &u, &v) != 2 || v < 0 || v >= M) {
            printf("FAIL input\n");
            return 0;
        }
        RT[p] = v;
    }
    if (A < 1 || DEG < 1 || DD < 1) { printf("FAIL params\n"); return 0; }

    NV = 2 * A * M;
    int nd = A * DEG;
    adj = malloc(sizeof(int) * (size_t)NV * DEG);
    fillc = malloc(sizeof(int) * (size_t)NV);
    stamp = calloc((size_t)NV, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NV);
    nf = malloc(sizeof(int) * (size_t)NV);
    int *G = malloc(sizeof(int) * (size_t)nd);
    int *J = malloc(sizeof(int) * (size_t)nd);
    int *G2 = malloc(sizeof(int) * (size_t)nd);
    int *J2 = malloc(sizeof(int) * (size_t)nd);
    int *bG = malloc(sizeof(int) * (size_t)nd);
    int *bJ = malloc(sizeof(int) * (size_t)nd);

    fresh_state(G, J);
    clock_t t0 = clock();
    build_adj(G, J);
    long cur = cost_eval();
    long best = cur;
    memcpy(bG, G, sizeof(int) * (size_t)nd);
    memcpy(bJ, J, sizeof(int) * (size_t)nd);

    const long CYC = 40000;
    const double Ts = 2.0, Te = 0.05;
    long it = 0;
    long cycle = 0;

    while (best > 0) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
        }
        if (it % CYC == 0 && it > 0) {
            cycle++;
            if (cycle & 1) {
                fresh_state(G, J);
            } else {
                memcpy(G, bG, sizeof(int) * (size_t)nd);
                memcpy(J, bJ, sizeof(int) * (size_t)nd);
            }
            build_adj(G, J);
            cur = cost_eval();
        }
        double frac = (double)(it % CYC) / (double)CYC;
        double T = Ts * pow(Te / Ts, frac);

        memcpy(G2, G, sizeof(int) * (size_t)nd);
        memcpy(J2, J, sizeof(int) * (size_t)nd);
        if (rndu() < 0.6) {
            int k = rndint(nd);
            G2[k] = rndint(M);
        } else {
            int k1 = rndint(nd), k2 = rndint(nd);
            if (J2[k1] == J2[k2]) { it++; continue; }
            int t = J2[k1]; J2[k1] = J2[k2]; J2[k2] = t;
        }
        build_adj(G2, J2);
        long nc = cost_eval();
        if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) {
            memcpy(G, G2, sizeof(int) * (size_t)nd);
            memcpy(J, J2, sizeof(int) * (size_t)nd);
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(bG, G, sizeof(int) * (size_t)nd);
                memcpy(bJ, J, sizeof(int) * (size_t)nd);
            }
        }
        it++;
    }

    if (best == 0) {
        printf("OK\n");
        for (int k = 0; k < nd; k++) printf("%d %d\n", bJ[k], bG[k]);
    } else {
        printf("FAIL %ld\n", best);
    }
    return 0;
}
"""


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
# Groups and C-annealed voltage lifts.
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


def _group_table(spec):
    """Return (order, flat) where flat[g*order + x] = (0, x*g) encodes the right-multiplication table."""
    order, mul, _ = _make_group(spec)
    flat = []
    for g in range(order):
        for x in range(order):
            flat.append((0, mul(x, g)))
    return order, flat


def _c_lift_stage(d, D, get_best, rng, deadline, consider):
    """Search voltage lifts with a in {1,2,3} base sides using the C annealer, above the current best order."""
    moore = lib.moore_bound(d, D)
    misses = 0
    while time.monotonic() < deadline and misses < 200:
        best = get_best()
        avail = [a for a in (1, 2, 3) if best // (2 * a) + 1 <= moore // (2 * a)]
        if not avail:
            return
        a = rng.choice(avail)
        lo = best // (2 * a) + 1
        hi = min(moore // (2 * a), lo + 40)
        specs = _group_specs(lo, hi)
        if not specs:
            misses += 1
            continue
        spec = rng.choice(specs)
        order, flat = _group_table(spec)
        remaining = deadline - time.monotonic()
        if remaining < 0.6:
            return
        secs = min(3.0, remaining - 0.3)
        try:
            out = lib.run_c(C_SOURCE, [a, d, D, f"{secs:.2f}", rng.randrange(1 << 30)],
                            stdin_graph=(order, flat), timeout=secs + 5.0)
        except RuntimeError:
            return
        toks = out.split()
        if not toks or toks[0] != "OK":
            misses += 1
            continue
        vals = list(map(int, toks[1:]))
        nd = a * d
        if len(vals) < 2 * nd:
            continue
        E = set()
        for k in range(nd):
            j, g = vals[2 * k], vals[2 * k + 1]
            i = k // d
            for x in range(order):
                u = i * order + x
                v = a * order + j * order + flat[g * order + x][1]
                E.add((min(u, v), max(u, v)))
        consider(2 * a * order, sorted(E))


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
            if best_n >= moore:
                return best_n, list(best_e)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # C-annealed voltage lifts over cyclic and semidirect groups, a in {1, 2, 3}.
    lift_end = start + 0.50 * time_limit
    if time.monotonic() < lift_end:
        try:
            _c_lift_stage(d, D, lambda: best_n, rng, lift_end, consider)
        except Exception:
            pass

    # Randomized twin-duplication pipelines from the structured base.
    trial_end = start + 0.60 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # Kill-repair-regrow search from the best valid graph found so far.
    if time.monotonic() < deadline:
        lns_end = start + 0.80 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # Prune redundant edges to free degree, then regrow from the best graph.
    if time.monotonic() < deadline:
        prune_end = start + 0.88 * time_limit
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
