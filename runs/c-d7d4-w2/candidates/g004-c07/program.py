"""d7D4-oriented program: parent pipeline as a safe baseline, then a bold C-accelerated
search over bi-Cayley lifts of small bipartite bases over ALL semidirect groups of each
order, scanning lift sizes upward from the parent's order. Every return is validated, with
K_{d,d} as the final fallback."""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over permutation/label voltages of a lift over a
# finite group G (given as a multiplication table on stdin). Diameter test uses
# BFS from (u, identity) for each of the 2*KB base vertices (left translation is an
# automorphism). Prints the lifted graph on success, "0 0" otherwise.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 64

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int KB, G, DEG, D, NN;
static int *T, *tgt, *lab, *adj, *seen, *bufA, *bufB;

static void build_adj(void) {
    for (int i = 0; i < KB; i++)
        for (int x = 0; x < G; x++) {
            int u = i * G + x;
            for (int t = 0; t < DEG; t++) {
                int j = tgt[t * KB + i];
                int g = lab[t * KB + i];
                int v = KB * G + j * G + T[x * G + g];
                adj[u * DEG + t] = v;
                adj[v * DEG + t] = u;
            }
        }
}

static long cost(void) {
    build_adj();
    long total = 0;
    for (int s0 = 0; s0 < 2 * KB; s0++) {
        int s = s0 * G;
        memset(seen, 0, sizeof(int) * (size_t)NN);
        int *fr = bufA, *nx = bufB;
        int fl = 0, cnt = 1;
        fr[fl++] = s;
        seen[s] = 1;
        for (int r = 0; r < D && fl > 0; r++) {
            int nl = 0;
            for (int a = 0; a < fl; a++) {
                int v = fr[a];
                for (int t = 0; t < DEG; t++) {
                    int w = adj[v * DEG + t];
                    if (!seen[w]) { seen[w] = 1; nx[nl++] = w; }
                }
            }
            cnt += nl;
            int *tmp = fr; fr = nx; nx = tmp;
            fl = nl;
        }
        total += NN - cnt;
    }
    return total;
}

static int uniq(int u, int *nb) {
    int k = 0;
    for (int t = 0; t < DEG; t++) {
        int w = adj[u * DEG + t];
        int dup = 0;
        for (int q = 0; q < k; q++) if (nb[q] == w) { dup = 1; break; }
        if (!dup) nb[k++] = w;
    }
    return k;
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    KB = atoi(argv[1]);
    G = atoi(argv[2]);
    DEG = atoi(argv[3]);
    D = atoi(argv[4]);
    rs ^= (uint64_t)strtoull(argv[5], NULL, 10) * 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[6]);
    if (KB < 1 || G < 1 || DEG < 1 || DEG > MAXDEG || D < 1) return 1;

    int gn, m;
    if (scanf("%d %d", &gn, &m) != 2) return 2;
    if (gn != G || m != G * G) return 2;
    T = malloc(sizeof(int) * (size_t)(G * G));
    for (int k = 0; k < m; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 2;
        if (u < 0 || u >= G * G || v < 0 || v >= G) return 2;
        T[u] = v;
    }

    NN = 2 * KB * G;
    tgt = malloc(sizeof(int) * (size_t)(DEG * KB));
    lab = malloc(sizeof(int) * (size_t)(DEG * KB));
    adj = malloc(sizeof(int) * (size_t)(NN * DEG));
    seen = malloc(sizeof(int) * (size_t)NN);
    bufA = malloc(sizeof(int) * (size_t)NN);
    bufB = malloc(sizeof(int) * (size_t)NN);
    int *perm = malloc(sizeof(int) * (size_t)KB);

    for (int t = 0; t < DEG; t++) {
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < KB; i++) {
            tgt[t * KB + i] = perm[i];
            lab[t * KB + i] = rndi(G);
        }
    }

    long cur = cost();
    clock_t t0 = clock();
    long it = 0;
    while (cur > 0) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;
        double temp = 0.25 + 1.5 * pow(0.9997, (double)(it % 20000));
        int t = rndi(DEG);
        if (KB >= 2 && rndu() < 0.3) {
            int i1 = rndi(KB), i2 = rndi(KB);
            if (i1 == i2) continue;
            int *p = tgt + t * KB;
            int tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
            long c = cost();
            if (c <= cur || rndu() < exp(-(double)(c - cur) / temp)) {
                cur = c;
            } else {
                tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
            }
        } else {
            int i = rndi(KB);
            int *lp = lab + t * KB + i;
            int old = *lp;
            int nw = rndi(G);
            if (nw == old) continue;
            *lp = nw;
            long c = cost();
            if (c <= cur || rndu() < exp(-(double)(c - cur) / temp)) {
                cur = c;
            } else {
                *lp = old;
            }
        }
    }

    if (cur == 0) {
        build_adj();
        int nb[MAXDEG];
        long cnt = 0;
        for (int u = 0; u < KB * G; u++) cnt += uniq(u, nb);
        printf("%d %ld\n", NN, cnt);
        for (int u = 0; u < KB * G; u++) {
            int k = uniq(u, nb);
            for (int q = 0; q < k; q++) printf("%d %d\n", u, nb[q]);
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


_C_OK = [True]
_SLICE = 3.0


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
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
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


# ----------------------------------------------------------------------------
# Bi-Cayley lift search over all semidirect groups of each order (C-accelerated).
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All (m, k, r) with m*k = G giving a semidirect product Z_m x| Z_k."""
    out = []
    for m in range(1, G + 1):
        if G % m:
            continue
        k = G // m
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _c_lift(kb, G, d, D, seed, slice_s, mul):
    """Run the C annealer for one (kb, group) pair. Returns (n, edges) or None.

    The group table is passed as a graph with edges (x*G+g) -> x*g, which the C side reads
    with the standard "n m" + pairs format.
    """
    table = [(x * G + g, mul(x, g)) for x in range(G) for g in range(G)]
    out = lib.run_c(C_SOURCE, [kb, G, d, D, seed, f"{slice_s:.2f}"],
                    stdin_graph=(G, table), timeout=slice_s + 8.0)
    n, E = lib.parse_graph_text(out)
    if n <= 0 or not E:
        return None
    return n, E


def _lift_stage_c(d, D, seed, deadline, floor_n, limit_n):
    """Scan lift sizes upward from floor_n; return the best valid lift found, or None."""
    rng = random.Random(seed)
    cands = []
    for kb in range(1, 9):
        for G in range(floor_n // (2 * kb) + 1, limit_n // (2 * kb) + 1):
            n = 2 * kb * G
            if floor_n < n <= limit_n:
                cands.append((n, kb, G))
    cands.sort()

    best_n, best = floor_n, None
    for n, kb, G in cands:
        if n <= best_n:
            continue
        groups = _groups_of_order(G)
        if not groups:
            continue
        rng.shuffle(groups)
        for m, k, r in groups[:2]:
            now = time.monotonic()
            if now >= deadline - 0.5 or not _C_OK[0]:
                return best
            try:
                _, mul, _ = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            slice_s = min(_SLICE, deadline - now - 0.5)
            try:
                res = _c_lift(kb, G, d, D, rng.randrange(1 << 30), slice_s, mul)
            except Exception:
                _C_OK[0] = False
                return best
            if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                best_n, best = res[0], (res[0], list(res[1]))
                break
    return best


# ----------------------------------------------------------------------------
# Parent pipeline (safe baseline).
# ----------------------------------------------------------------------------

def _parent_build(d, D, seed, time_limit):
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
        trial_end = start + 0.3 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.75 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    if D >= 4 and d >= 3 and time_limit >= 10:
        # Baseline pipeline gets a modest share; the C lift search takes the rest.
        try:
            n1, e1 = _parent_build(d, D, seed, 0.3 * time_limit)
        except Exception:
            n1, e1 = fallback
        if not lib.is_valid(n1, e1, d, D):
            n1, e1 = fallback
        if n1 >= best_n:
            best_n, best_e = n1, list(e1)

        if _C_OK[0]:
            try:
                limit_n = min(lib.moore_bound(d, D), 1200)
                res = _lift_stage_c(d, D, seed * 7919 + 1, start + 0.85 * time_limit,
                                    best_n, limit_n)
                if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                    best_n, best_e = res[0], list(res[1])
            except Exception:
                pass
    else:
        try:
            n1, e1 = _parent_build(d, D, seed, time_limit)
        except Exception:
            n1, e1 = fallback
        if lib.is_valid(n1, e1, d, D):
            best_n, best_e = n1, list(e1)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
