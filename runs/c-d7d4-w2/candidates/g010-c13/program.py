import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: fixed-target simulated annealing over bipartite graphs.
#
# It starts from a valid graph and keeps all degrees <= d with fixed sides. Moves:
#   A  add an edge between two deficient opposite-side vertices,
#   B  bipartite double-edge switch (degrees unchanged),
#   C  endpoint move: an edge (y, x) becomes (w, x) for a deficient w, which
#      shifts spare degree to y.
# Cost = number of unordered pairs at distance > D, computed by bitset balls.
# Whenever cost hits 0 the graph is saved and grown by a pair of vertices (one
# per side), so the spare degree is created where the search can use it. If
# growth stalls, it restores the best graph and tries again.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define PATIENCE 120000LL

static int dg, DD;
static int nmax, n, W, Wmax;
static int *adjv, *deg, *side;
static int *badj, *bdeg, *bside;
static int bestn = 0, bestvalid = 0;
static u64 *ballA, *ballB;
static int *defl[2];
static u64 rs = 88172645463325252ULL;

#define NB(v, k) adjv[(size_t)(v) * (size_t)dg + (size_t)(k)]

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int m) { return m <= 0 ? 0 : (int)(rnd() % (u64)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (NB(a, k) == b) return 1;
    return 0;
}
static void add_arc(int a, int b) { NB(a, deg[a]) = b; deg[a]++; }
static void add_edge(int a, int b) { add_arc(a, b); add_arc(b, a); }
static void del_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (NB(a, k) == b) { NB(a, k) = NB(a, deg[a] - 1); deg[a]--; return; }
}
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

static long long cost_full(void) {
    int N = n;
    size_t WW = (size_t)W;
    u64 *cur = ballA, *nxt = ballB;
    memset(cur, 0, sizeof(u64) * (size_t)N * WW);
    for (int v = 0; v < N; v++) cur[(size_t)v * WW + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * WW;
            memcpy(dst, cur + (size_t)v * WW, sizeof(u64) * WW);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *src = cur + (size_t)NB(v, k) * WW;
                for (size_t w = 0; w < WW; w++) dst[w] |= src[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const u64 *s = cur + (size_t)v * WW;
        for (size_t w = 0; w < WW; w++) c += popc(s[w]);
        bad += N - c;
    }
    return bad / 2;
}

static void save_best(void) {
    memcpy(badj, adjv, sizeof(int) * (size_t)n * (size_t)dg);
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(bside, side, sizeof(int) * (size_t)n);
    bestn = n;
    bestvalid = 1;
}

static void restore_best(void) {
    memcpy(adjv, badj, sizeof(int) * (size_t)bestn * (size_t)dg);
    memcpy(deg, bdeg, sizeof(int) * (size_t)bestn);
    memcpy(side, bside, sizeof(int) * (size_t)bestn);
    n = bestn;
    W = (n + 63) / 64;
}

static void grow_pair(void) {
    int v0 = n, v1 = n + 1;
    side[v0] = 0; side[v1] = 1;
    deg[v0] = 0; deg[v1] = 0;
    n += 2;
    W = (n + 63) / 64;
}

static int pick_side_deg(int s) {
    for (int t = 0; t < 40; t++) {
        int v = rndint(n);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

static void undo_move(int mt, int a, int b, int c, int e) {
    if (mt == 0) {
        del_edge(a, b);
    } else if (mt == 1) {
        del_edge(a, e); del_edge(c, b);
        add_edge(a, b); add_edge(c, e);
    } else if (mt == 2) {
        /* forward: del (y,x), add (w,x) with a=w, b=x, c=y */
        del_edge(a, b);
        add_edge(c, b);
    }
}

static void print_graph(const int *ad, const int *dd, int N) {
    long long m = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < dd[v]; k++)
            if (v < ad[(size_t)v * (size_t)dg + (size_t)k]) m++;
    printf("%d %lld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < dd[v]; k++) {
            int u = ad[(size_t)v * (size_t)dg + (size_t)k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dg = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    int extra = argc > 5 ? atoi(argv[5]) : 64;
    if (extra < 0) extra = 0;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || dg < 1 || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    nmax = n0 + extra;
    Wmax = (nmax + 63) / 64;
    adjv = malloc(sizeof(int) * (size_t)nmax * (size_t)dg);
    deg = calloc((size_t)nmax, sizeof(int));
    side = calloc((size_t)nmax, sizeof(int));
    badj = malloc(sizeof(int) * (size_t)nmax * (size_t)dg);
    bdeg = calloc((size_t)nmax, sizeof(int));
    bside = calloc((size_t)nmax, sizeof(int));
    ballA = malloc(sizeof(u64) * (size_t)Wmax * (size_t)nmax);
    ballB = malloc(sizeof(u64) * (size_t)Wmax * (size_t)nmax);
    defl[0] = malloc(sizeof(int) * (size_t)nmax);
    defl[1] = malloc(sizeof(int) * (size_t)nmax);
    if (!adjv || !deg || !side || !badj || !bdeg || !bside || !ballA || !ballB || !defl[0] || !defl[1]) {
        printf("0 0\n");
        return 0;
    }

    n = n0;
    W = (n + 63) / 64;
    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { bad = 1; break; }
        if (deg[u] >= dg || deg[v] >= dg || has_edge(u, v)) { bad = 1; break; }
        add_edge(u, v);
    }
    if (!bad) {
        int *q = malloc(sizeof(int) * (size_t)n);
        for (int v = 0; v < n; v++) side[v] = -1;
        for (int s = 0; s < n && !bad; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt && !bad) {
                int u = q[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int v = NB(u, k);
                    if (side[v] < 0) { side[v] = 1 - side[u]; q[qt++] = v; }
                    else if (side[v] == side[u]) { bad = 1; break; }
                }
            }
        }
        free(q);
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    long long cur = cost_full();
    if (cur == 0) save_best();

    clock_t t0 = clock();
    long long iter = 0, lastimp = 0;
    for (;;) {
        if (cur == 0) {
            if (!bestvalid || n > bestn) save_best();
            if (n + 2 > nmax) break;
            grow_pair();
            cur = cost_full();
            lastimp = iter;
            continue;
        }
        iter++;
        if ((iter & 127) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC >= budget) break;
        if (bestvalid && iter - lastimp > PATIENCE) {
            restore_best();
            cur = cost_full();
            lastimp = iter;
            continue;
        }

        int nd[2] = {0, 0};
        for (int v = 0; v < n; v++)
            if (deg[v] < dg) defl[side[v]][nd[side[v]]++] = v;

        int mt = -1, ma = 0, mb = 0, mc = 0, me = 0;
        double r = rnd01();
        if (r < 0.25) {
            if (nd[0] > 0 && nd[1] > 0) {
                int a = defl[0][rndint(nd[0])];
                int b = defl[1][rndint(nd[1])];
                if (!has_edge(a, b)) { add_edge(a, b); mt = 0; ma = a; mb = b; }
            }
        } else if (r < 0.55) {
            int s = (int)(rnd() & 1ULL);
            if (nd[s] > 0) {
                int w = defl[s][rndint(nd[s])];
                int x = -1;
                for (int t = 0; t < 20; t++) {
                    int c = rndint(n);
                    if (side[c] == 1 - s && deg[c] > 0 && !has_edge(w, c)) { x = c; break; }
                }
                if (x >= 0) {
                    int y = NB(x, rndint(deg[x]));
                    del_edge(y, x);
                    add_edge(w, x);
                    mt = 2; ma = w; mb = x; mc = y;
                }
            }
        } else {
            int a = pick_side_deg(0), c = pick_side_deg(0);
            if (a >= 0 && c >= 0 && a != c) {
                int b = NB(a, rndint(deg[a]));
                int e = NB(c, rndint(deg[c]));
                if (b != e && !has_edge(a, e) && !has_edge(c, b)) {
                    del_edge(a, b);
                    del_edge(c, e);
                    add_edge(a, e);
                    add_edge(c, b);
                    mt = 1; ma = a; mb = b; mc = c; me = e;
                }
            }
        }
        if (mt < 0) continue;

        long long nc = cost_full();
        long long delta = nc - cur;
        double Tm = 0.3 + 0.9 * (1.0 - (double)((iter - lastimp) % 100000LL) / 100000.0);
        if (delta <= 0 || rnd01() < exp(-(double)delta / Tm)) {
            cur = nc;
        } else {
            undo_move(mt, ma, mb, mc, me);
        }
    }

    if (bestvalid) print_graph(badj, bdeg, bestn);
    else printf("0 0\n");
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
# Large-neighbourhood search (kill, repair, regrow), anchored to the best graph.
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


# ----------------------------------------------------------------------------
# Bold change: bipartite Cayley ("bi-Cayley") graphs over small finite groups.
# ----------------------------------------------------------------------------

def _groups_of_order(N):
    """All (m, k, r) with the semidirect product Z_m x|_r Z_k of order N = m*k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k; element (a, b) is coded a*k + b, identity 0."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    table = [[0] * N for _ in range(N)]
    for x in range(N):
        a1, b1 = divmod(x, k)
        row = table[x]
        for y in range(N):
            c, d2 = divmod(y, k)
            row[y] = ((a1 + pw[b1] * c) % m) * k + (b1 + d2) % k
    return table


def _bicayley_adj(N, table, S):
    """Adjacency lists of the bi-Cayley graph: a_g = g, b_x = N + x, a_g ~ b_{g*s}."""
    adj = [[] for _ in range(2 * N)]
    for g in range(N):
        row = table[g]
        ag = adj[g]
        for s in S:
            b = N + row[s]
            ag.append(b)
            adj[b].append(g)
    return adj


def _cayley_cost(adj, D):
    """Vertices farther than D from a_e or from b_e (both sources, both sides)."""
    total = 0
    N2 = len(adj)
    N = N2 // 2
    for src in (0, N):
        dist = [-1] * N2
        dist[src] = 0
        frontier = [src]
        cnt = 1
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - cnt
    return total


def _climb(N, table, d, D, rng, iters, deadline):
    """Hill-climb a d-element generating set S minimising the Cayley cost. Returns S or None."""
    S = rng.sample(range(N), d)
    cur = _cayley_cost(_bicayley_adj(N, table, S), D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        cand = rng.randrange(N)
        if cand in S:
            continue
        newS = list(S)
        newS[i] = cand
        c2 = _cayley_cost(_bicayley_adj(N, table, newS), D)
        if c2 <= cur or (c2 == cur + 1 and rng.random() < 0.05):
            S, cur = newS, c2
    return S if cur == 0 else None


def _bicayley_search(d, D, rng, deadline, consider, lo_n):
    """Search bi-Cayley graphs of increasing order N (n = 2N) that beat lo_n vertices."""
    lo = max(d, lo_n // 2 + 1)
    hi = lib.moore_bound(d, D) // 2
    N = lo
    while N <= hi and time.monotonic() < deadline:
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        for (m, k, r) in groups[:4]:
            if time.monotonic() >= deadline:
                break
            table = _group_table(m, k, r)
            S = _climb(N, table, d, D, rng, 200, deadline)
            if S is not None:
                edges = [(g, N + table[g][s]) for g in range(N) for s in S]
                consider(2 * N, edges)
                break
        N += 1


# ----------------------------------------------------------------------------
# C annealer driver.
# ----------------------------------------------------------------------------

def _sa_refine(best_n, best_e, d, D, seed, budget, timeout):
    """Run the C annealer from the best graph; returns the (n, edges) it prints."""
    extra = max(0, min(lib.moore_bound(d, D) - best_n, max(16, best_n // 4)))
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", extra],
                     stdin_graph=(best_n, best_e), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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

    # Phase A (to 0.12 T): structured base, growth, and twin pipelines.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * T, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.15 * T
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase C (to 0.25 T): bi-Cayley search over small groups.
    if D >= 2 and d >= 2 and time.monotonic() < start + 0.25 * T:
        _bicayley_search(d, D, rng, start + 0.25 * T, consider, best_n)

    # Phase B (to 0.4 T): kill-repair-regrow from the best valid graph.
    if D >= 2 and time.monotonic() < start + 0.4 * T:
        _lns(best_n, best_e, d, D, start + 0.4 * T, rng, consider)

    # Phase D (rest of budget): C annealer that grows the best graph by vertex pairs.
    if D >= 2 and d >= 3:
        moore = lib.moore_bound(d, D)
        if best_n < moore and moore <= 6000:
            remaining = start + 0.92 * T - time.monotonic()
            budget = min(0.5 * T, remaining - 2.5)
            if budget >= 2.0:
                try:
                    n_c, e_c = _sa_refine(best_n, best_e, d, D,
                                          seed % 1000003 + 1, budget, remaining)
                    consider(n_c, e_c)
                except Exception:
                    pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
