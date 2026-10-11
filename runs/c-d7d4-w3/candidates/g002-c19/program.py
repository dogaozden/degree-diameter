import itertools
import random
import sys
import time

import lib

sys.setrecursionlimit(10000)


# ----------------------------------------------------------------------------
# Native engine: bitset-cost annealing on bipartite graphs with vertex growth.
#
# State: a bipartite graph with max degree d. Cost = number of unordered pairs
# at distance > D (unreachable pairs count). Moves preserve bipartiteness and
# the degree bound:
#   M1  attach a deficient vertex v to a random opposite vertex w (if w is full,
#       steal one of w's edges and rewire it to v),
#   M2  bipartite double-edge switch (degrees unchanged).
# Phase loop: add one vertex to the best valid graph, anneal the cost to 0,
# save the new best, repeat until the clock runs out.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXD 64
#define MAXE 70000

static int d_, D_;
static int n;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static uint64_t rng_s = 88172645463325252ULL;

static int snap_n = 0, snap_m = 0;
static int snap_side[MAXN];
static int snap_eu[MAXE], snap_ev[MAXE];

typedef struct { int type; int u, v; } Op;
static Op oplog[16];
static int nops = 0;

static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
    return 0;
}

static void add_edge_raw(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge_raw(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

static void op_add(int u, int v) {
    add_edge_raw(u, v);
    oplog[nops].type = 0; oplog[nops].u = u; oplog[nops].v = v; nops++;
}

static void op_del(int u, int v) {
    del_edge_raw(u, v);
    oplog[nops].type = 1; oplog[nops].u = u; oplog[nops].v = v; nops++;
}

static void undo(void) {
    while (nops > 0) {
        Op o = oplog[--nops];
        if (o.type == 0) del_edge_raw(o.u, o.v);
        else add_edge_raw(o.u, o.v);
    }
}

/* Number of unordered pairs at distance > D_ (unreachable pairs included). */
static long cost(void) {
    int W = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        uint64_t *p = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) p[w] = 0;
        p[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *self = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) out[w] = self[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
            for (int w = 0; w < W; w++) if (out[w] != self[w]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *p = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(p[w]);
        bad += n - c;
    }
    return bad / 2;
}

/* One random move; records ops in oplog. Returns 1 if a move was applied. */
static int move(void) {
    static int cand[MAXN];
    nops = 0;
    int nc = 0;
    for (int v = 0; v < n; v++) if (deg[v] < d_) cand[nc++] = v;
    if (nc > 0 && rnd01() < 0.5) {
        int v = cand[rndint(nc)];
        int w = -1;
        for (int t = 0; t < 20; t++) {
            int x = rndint(n);
            if (side[x] != side[v] && !has_edge(v, x)) { w = x; break; }
        }
        if (w < 0) return 0;
        if (deg[w] < d_) {
            op_add(v, w);
            return 1;
        }
        int x = adj[w][rndint(deg[w])];
        op_del(w, x);
        op_add(v, w);
        return 1;
    }
    for (int t = 0; t < 20; t++) {
        int a = rndint(n);
        if (deg[a] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int c = rndint(n);
        if (c == a || side[c] != side[a] || deg[c] == 0) continue;
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        op_del(a, b);
        op_del(c, e);
        op_add(a, e);
        op_add(c, b);
        return 1;
    }
    return 0;
}

static void save_snapshot(void) {
    snap_n = n;
    snap_m = 0;
    for (int v = 0; v < n; v++) {
        snap_side[v] = side[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (v < u && snap_m < MAXE) {
                snap_eu[snap_m] = v;
                snap_ev[snap_m] = u;
                snap_m++;
            }
        }
    }
}

static void load_snapshot(void) {
    n = snap_n;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        side[v] = snap_side[v];
    }
    for (int i = 0; i < snap_m; i++) add_edge_raw(snap_eu[i], snap_ev[i]);
}

/* Add an isolated vertex on the lighter side. */
static int grow_one(void) {
    if (n >= MAXN) return 0;
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) { if (side[v] == 0) c0++; else c1++; }
    side[n] = (c0 <= c1) ? 0 : 1;
    deg[n] = 0;
    n++;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rng_s ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rng_s == 0) rng_s = 1;
    double limit = atof(argv[4]);
    if (d_ < 1 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }
    clock_t t0 = clock();

    int in_n = 0, in_m = 0;
    if (scanf("%d %d", &in_n, &in_m) != 2 || in_n <= 0 || in_n > MAXN || in_m < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(in_m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(in_m + 1));
    if (!eu || !ev) { printf("0 0\n"); return 0; }
    int cnt = 0;
    for (int i = 0; i < in_m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || a >= in_n || b < 0 || b >= in_n || a == b) continue;
        eu[cnt] = a;
        ev[cnt] = b;
        cnt++;
    }

    n = in_n;
    for (int v = 0; v < n; v++) { deg[v] = 0; side[v] = -1; }
    for (int i = 0; i < cnt; i++) {
        int u = eu[i], v = ev[i];
        if (deg[u] < d_ && deg[v] < d_ && !has_edge(u, v)) add_edge_raw(u, v);
    }

    /* 2-colour; reject non-bipartite input. */
    int *stack = malloc(sizeof(int) * (size_t)(n + 1));
    int bip = 1;
    for (int s = 0; s < n && bip; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0 && bip) {
            int u = stack[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    stack[sp++] = w;
                } else if (side[w] == side[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }

    int have_best = 0;
    if (cost() == 0) {
        save_snapshot();
        have_best = 1;
    }

    while (elapsed(t0) < limit) {
        if (have_best) {
            load_snapshot();
            if (!grow_one()) break;
        }
        long c = cost();
        int ok = (c == 0);
        const long R = 25000;
        for (long it = 0; !ok && it < R; it++) {
            if ((it & 15) == 0 && elapsed(t0) >= limit) break;
            double frac = (double)it / (double)R;
            double T = 0.9 * pow(0.02 / 0.9, frac);
            if (!move()) continue;
            long nc = cost();
            if (nc <= c || rnd01() < exp(-(double)(nc - c) / T)) {
                c = nc;
            } else {
                undo();
            }
            if (c == 0) ok = 1;
        }
        nops = 0;
        if (c == 0) {
            save_snapshot();
            have_best = 1;
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++) printf("%d %d\n", snap_eu[i], snap_ev[i]);
    free(stack);
    free(eu);
    free(ev);
    return 0;
}
'''


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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """A dense structured graph whose degree is at least d (q = smallest prime power >= d)."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
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
# Thin a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _perfect_matching(n, adj, color, rng):
    """Random perfect matching of the bipartite graph (Kuhn augmentation). dict left->right, or None."""
    left = [v for v in range(n) if color[v] == 0]
    nb = {}
    for u in left:
        lst = list(adj[u])
        rng.shuffle(lst)
        nb[u] = lst
    match_l = {}
    match_r = {}
    for u in left:
        for v in nb[u]:
            if v not in match_r:
                match_l[u] = v
                match_r[v] = u
                break

    def augment(u, seen):
        for v in nb[u]:
            if v in seen:
                continue
            seen.add(v)
            w = match_r.get(v)
            if w is None or augment(w, seen):
                match_l[u] = v
                match_r[v] = u
                return True
        return False

    for u in left:
        if u not in match_l:
            if not augment(u, set()):
                return None
    if len(match_l) != len(left):
        return None
    return match_l


def _regular_thin(n, edges, d, rng):
    """For a (d+1)-regular bipartite graph, drop a random perfect matching. Returns edges or None."""
    adj = _to_sets(n, edges)
    if any(len(a) != d + 1 for a in adj):
        return None
    color = _bipartition(n, adj)
    match = _perfect_matching(n, adj, color, rng)
    if match is None:
        return None
    drop = {(min(u, v), max(u, v)) for u, v in match.items()}
    return [(u, v) for u, v in edges if (min(u, v), max(u, v)) not in drop]


def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = None
    if rng.random() < 0.8:
        e = _regular_thin(raw_n, raw_e, d, rng)
    if e is None:
        e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


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


def _local_kill(n, edges, k, rng):
    """Vertex set of size <= k grown by BFS from a random vertex (a local 'wound')."""
    adj = _to_sets(n, edges)
    s = rng.randrange(n)
    seen = [s]
    seen_set = {s}
    i = 0
    while len(seen) < k and i < len(seen):
        nbrs = list(adj[seen[i]])
        rng.shuffle(nbrs)
        for u in nbrs:
            if len(seen) >= k:
                break
            if u not in seen_set:
                seen_set.add(u)
                seen.append(u)
        i += 1
    return seen_set


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4, 6))
        if k >= cur_n:
            break
        if rng.random() < 0.5:
            kill = set(rng.sample(range(cur_n), k))
        else:
            kill = _local_kill(cur_n, cur_e, k, rng)
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


# ----------------------------------------------------------------------------
# Driver. Python phases build and thin structured starts; the native annealer
# then grows the best valid graph by one vertex at a time for the rest of the budget.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.9 * time_limit - 0.5
    span = max(0.1, end - start)

    def at(f):
        return start + f * span

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

    # Phase A: structured small base, twin trials, short LNS.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.05), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.08)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
        _lns(best_n, best_e, d, D, at(0.15), rng, consider)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.25):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.25):
                r = _deletion_trial(d, D, rn, re, rng, at(0.25))
                if r is None:
                    break
                consider(*r)

    # Phase C: native bitset annealer grows the best valid graph (main search).
    native_ran = False
    if d >= 4 and d <= 60 and D >= 2 and best_n <= 1900:
        remaining = end - time.monotonic()
        if remaining > 2.0:
            margin = min(1.5, 0.1 * time_limit)
            budget = remaining - margin
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=remaining)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
                native_ran = True
            except (RuntimeError, ValueError):
                native_ran = False

    # Fallback: Python LNS if the native engine did not run.
    if not native_ran and D >= 2 and time.monotonic() < end:
        _lns(best_n, best_e, d, D, end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
