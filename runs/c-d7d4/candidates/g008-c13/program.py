import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over Z_m x| Z_k voltage lifts of small bipartite
# base multigraphs (kb vertices per side, dd-regular). The lift is vertex-transitive
# on each fibre, so only 2*kb BFS sources are needed to measure the diameter.
# Prints a valid lift (cost 0) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXDEG 16
#define MAXKB 8

static int d, D, kb, dd, mm, kk, rr, M, N, nd;
static int pw[4096];
static int dsrc[MAXKB * MAXDEG], dtgt[MAXKB * MAXDEG], dvol[MAXKB * MAXDEG];
static int adj[MAXN][MAXDEG];
static int degc[MAXN];
static unsigned int stamp[MAXN];
static unsigned int curstamp = 0;
static int qbuf[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Element x = a*kk + b, (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / kk, b = x % kk;
    int c = y / kk, e = y % kk;
    int na = (a + (int)(((long)pw[b] * c) % mm)) % mm;
    int nb = (b + e) % kk;
    return na * kk + nb;
}

static void build_graph(void) {
    for (int v = 0; v < N; v++) degc[v] = 0;
    for (int t = 0; t < nd; t++) {
        int ia = dsrc[t], jb = dtgt[t], g = dvol[t];
        for (int x = 0; x < M; x++) {
            int A = ia * M + x;
            int B = kb * M + jb * M + gmul(x, g);
            adj[A][degc[A]++] = B;
            adj[B][degc[B]++] = A;
        }
    }
}

/* Number of vertices at distance > D from source s (unreached counted). */
static int src_bad(int s) {
    curstamp++;
    int head = 0, tail = 0;
    qbuf[tail++] = s;
    stamp[s] = curstamp;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            for (int k = 0; k < degc[v]; k++) {
                int w = adj[v][k];
                if (stamp[w] != curstamp) {
                    stamp[w] = curstamp;
                    qbuf[tail++] = w;
                }
            }
        }
    }
    return N - tail;
}

static int total_cost(void) {
    int c = 0;
    for (int i = 0; i < kb; i++) c += src_bad(i * M);
    for (int j = 0; j < kb; j++) c += src_bad(kb * M + j * M);
    return c;
}

static void emit(void) {
    static int pu[MAXN * MAXDEG], pv[MAXN * MAXDEG];
    int ne = 0;
    int nA = kb * M;
    for (int v = 0; v < nA; v++) {
        for (int k = 0; k < degc[v]; k++) {
            int w = adj[v][k], dup = 0;
            for (int q = 0; q < k; q++) {
                if (adj[v][q] == w) { dup = 1; break; }
            }
            if (!dup) { pu[ne] = v; pv[ne] = w; ne++; }
        }
    }
    printf("%d %d\n", N, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", pu[e], pv[e]);
}

int main(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    mm = atoi(argv[5]);
    kk = atoi(argv[6]);
    rr = atoi(argv[7]);
    kb = atoi(argv[8]);
    dd = atoi(argv[9]);
    if (mm == 1) rr = 0;
    if (d < 1 || D < 1 || mm < 1 || kk < 1 || kb < 1 || kb > MAXKB) { printf("0 0\n"); return 0; }
    if (dd < 1 || dd > d || dd > MAXDEG) { printf("0 0\n"); return 0; }
    if (rr < 0 || rr >= mm) { printf("0 0\n"); return 0; }
    M = mm * kk;
    if (M < 2 || M > 2048) { printf("0 0\n"); return 0; }
    N = 2 * kb * M;
    if (N > MAXN) { printf("0 0\n"); return 0; }
    if (gcd_int(rr, mm) != 1) { printf("0 0\n"); return 0; }
    pw[0] = 1 % mm;
    for (int b = 1; b < kk; b++) pw[b] = (int)(((long)pw[b - 1] * rr) % mm);
    if ((((long)pw[kk - 1] * rr) % mm) != (1 % mm)) { printf("0 0\n"); return 0; }

    rs = (uint64_t)seed * 2654435761ULL + 12345ULL;
    if (rs == 0) rs = 1;

    nd = kb * dd;
    int perm[MAXKB];
    for (int s = 0; s < dd; s++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < kb; i++) {
            int t = s * kb + i;
            dsrc[t] = i;
            dtgt[t] = perm[i];
            dvol[t] = rndint(M);
        }
    }

    build_graph();
    int cur = total_cost();
    if (cur == 0) { emit(); return 0; }

    const double T0 = 2.0, T1 = 0.05, CYC = 3.0;
    clock_t c0 = clock();
    for (;;) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        double ph = fmod(el, CYC) / CYC;
        double T = T0 * pow(T1 / T0, ph);

        int kind = 0, t1 = 0, t2 = 0, ov = 0, otgt1 = 0, otgt2 = 0;
        if (kb > 1 && rndint(10) < 4) {
            t1 = rndint(nd);
            int found = 0;
            for (int tries = 0; tries < 16; tries++) {
                t2 = rndint(nd);
                if (t2 != t1 && dsrc[t2] == dsrc[t1] && dtgt[t2] != dtgt[t1]) { found = 1; break; }
            }
            if (found) {
                kind = 1;
                otgt1 = dtgt[t1];
                otgt2 = dtgt[t2];
                dtgt[t1] = otgt2;
                dtgt[t2] = otgt1;
            }
        }
        if (kind == 0) {
            t1 = rndint(nd);
            ov = dvol[t1];
            dvol[t1] = (ov + 1 + rndint(M - 1)) % M;
        }

        build_graph();
        int nc = total_cost();
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) { emit(); return 0; }
        } else {
            if (kind == 1) {
                dtgt[t1] = otgt1;
                dtgt[t2] = otgt2;
            } else {
                dvol[t1] = ov;
            }
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases and Python helpers (generalized quadrangle / projective plane).
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
    """Greedily join deficient opposite-side vertices in random order."""
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


def _random_lift(k, m, d, rng):
    """Random Z_m lift of a d-regular bipartite multigraph on k + k base vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append((i, k + perm[i], rng.randrange(m)))
    return lib.voltage_lift(2 * k, darts, m)


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


def _lift_search(d, D, deadline, rng, best_n, consider):
    """Search random voltage lifts whose order is slightly above best_n, repair, then grow."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        if best_n >= moore:
            return
        k = rng.choice((1, 1, 2, 3))
        target = min(moore, best_n + rng.randint(1, 12))
        m = -(-target // (2 * k))
        if 2 * k * m > moore:
            m = moore // (2 * k)
        if m < 2 or 2 * k * m <= best_n:
            continue
        n, e = _random_lift(k, m, d, rng)
        adj = _to_sets(n, e)
        color = [0 if v < k * m else 1 for v in range(n)]
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(n) for v in adj[u] if u < v]
        consider(n, e3)
        n4, e4 = _grow(n, e3, d, D, deadline, rng, attempts=30)
        consider(n4, e4)
        if n4 > best_n:
            best_n = n4


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
# Best-so-far tracking and the two stages of the pipeline.
# ----------------------------------------------------------------------------

class _Best:
    def __init__(self, n, e, d, D):
        self.n, self.e, self.d, self.D = n, list(e), d, D

    def consider(self, n, e):
        if n > self.n and lib.is_valid(n, e, self.d, self.D):
            self.n, self.e = n, list(e)


def _parent_stage(d, D, rng, start, tl, best):
    """Structured base, twin trials, Python lifts, LNS and repair. Ends at start + 0.85*tl."""
    deadline = start + 0.85 * tl
    base_n, base_e = best.n, list(best.e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            best.consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.2 * tl, rng)
            best.consider(n1, e1)
    if D >= 2:
        trial_end = start + 0.3 * tl
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            best.consider(n, e)
        if time.monotonic() < deadline:
            _lift_search(d, D, start + 0.5 * tl, rng, best.n, best.consider)
        if time.monotonic() < deadline:
            _lns(best.n, best.e, d, D, start + 0.75 * tl, rng, best.consider)
        if time.monotonic() < deadline:
            _repair(d, D, best.n, best.e, deadline, rng, best.consider)


def _groups(M, rng):
    """All semidirect groups Z_m x| Z_k of order M (r = 1 for cyclic-type), shuffled."""
    out = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        if m == 1:
            out.append((1, k, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    rng.shuffle(out)
    return out


def _run_lift(d, D, seed, budget, grp, kb, dd):
    """Run the C annealer on one group. Returns (n, edges) for a valid lift, or None."""
    m, k, r = grp
    try:
        txt = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", m, k, r, kb, dd],
                        timeout=budget + 15.0)
        n, e = lib.parse_graph_text(txt)
    except Exception:
        return None
    if n < 1 or not e:
        return None
    return n, e


def _lift_stage(d, D, rng, deadline, best):
    """Anneal voltage lifts in C for increasing orders; grow each success with spare degree."""
    SLICE = 3.0
    configs = [(1, d), (2, d), (1, d - 1)]
    configs = [(kb, dd) for kb, dd in configs if dd >= 2]
    if not configs:
        return
    tries = {}
    for kb, dd in configs:
        if dd == d:
            tries[(kb, dd)] = max(2, best.n // (2 * kb) + 1)
        else:
            tries[(kb, dd)] = max(2, best.n // (2 * kb) - 8)
    fails = {c: 0 for c in configs}
    idx = 0
    while True:
        active = [c for c in configs if fails[c] < 3]
        if not active:
            break
        if deadline - time.monotonic() < 2.0:
            break
        cfg = active[idx % len(active)]
        idx += 1
        kb, dd = cfg
        M = tries[cfg]
        grps = _groups(M, rng)[:2]
        ok = False
        for grp in grps:
            left = deadline - time.monotonic()
            if left < 1.5:
                break
            out = _run_lift(d, D, rng.randrange(1, 10 ** 9), min(SLICE, left - 1.0),
                            grp, kb, dd)
            if out:
                n, e = out
                best.consider(n, e)
                n2, e2 = _grow(n, e, d, D, deadline, rng, attempts=30)
                best.consider(n2, e2)
                ok = True
                break
        if ok:
            tries[cfg] = M + 1
        else:
            fails[cfg] += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = _Best(fb_n, fb_e, d, D)

    if D >= 2:
        # Parent pipeline gets about 40% of the budget.
        _parent_stage(d, D, rng, start, 0.4 * time_limit / 0.85, best)
        # Bold stage: C annealing over group voltage lifts for larger orders.
        lift_deadline = start + 0.9 * time_limit - 1.0
        _lift_stage(d, D, rng, lift_deadline, best)

    if not lib.is_valid(best.n, best.e, d, D):
        return fb_n, list(fb_e)
    return best.n, list(best.e)
