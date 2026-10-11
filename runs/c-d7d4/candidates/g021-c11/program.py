import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost annealed vertex insertion with plateau walks.
#
# The state is always a valid graph (bad pairs = 0). Each round:
#   1. Optionally run a plateau walk: degree-preserving bipartite switches that
#      keep the diameter bound, which reshapes the graph without losing validity.
#   2. Insert one vertex on a random side, joined to a greedy set cover of the
#      opposite side's radius-(D-1) balls (stealing one edge from saturated
#      neighbours). Then fill spare degree across sides.
#   3. Anneal with switches, minimising the exact number of pairs at distance > D
#      (bitset BFS). Accept the new graph only at zero cost, otherwise restore.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 64
#define ANNEAL_ITERS 600

static int d_, D_;
static long long moore_;
static int N;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t ballA[MAXN][MAXW];
static uint64_t ballR[MAXN][MAXW];
static uint64_t tmpB[MAXN][MAXW];

static int sN;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];
static int scol[MAXN];

static int bN;
static int bdeg[MAXN];
static int badj[MAXN][MAXD];
static int bestOK;

static int L0[MAXN];
static int nL0;
static int stk[MAXN];

static uint64_t rs = 88172645463325252ULL;
static clock_t t_end;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int pc64(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void compute_balls(int r, uint64_t out[][MAXW]) {
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) tmpB[v][w] = out[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = out[adj[v][k]];
                for (int w = 0; w < W; w++) tmpB[v][w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) out[v][w] = tmpB[v][w];
    }
}

static long long bad_pairs(void) {
    int W = (N + 63) / 64;
    compute_balls(D_, ballA);
    long long s = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(ballA[v][w]);
        s += N - c;
    }
    return s / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void del_at(int a, int k) { adj[a][k] = adj[a][--deg[a]]; }
static void del_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) { del_at(a, k); break; }
    for (int k = 0; k < deg[b]; k++) if (adj[b][k] == a) { del_at(b, k); break; }
}

static int colour_graph(void) {
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] == -1) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    return 1;
}

static void set_kdd(void) {
    N = 2 * d_;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < d_; i++)
        for (int j = 0; j < d_; j++)
            add_edge(i, d_ + j);
    colour_graph();
}

static void save_best(void) {
    bN = N;
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(badj, adj, sizeof(int) * MAXD * (size_t)N);
    bestOK = 1;
}

static void save_state(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof(int) * (size_t)N);
    memcpy(sadj, adj, sizeof(int) * MAXD * (size_t)N);
    memcpy(scol, col, sizeof(int) * (size_t)N);
}

static void restore_state(void) {
    N = sN;
    memcpy(deg, sdeg, sizeof(int) * (size_t)N);
    memcpy(adj, sadj, sizeof(int) * MAXD * (size_t)N);
    memcpy(col, scol, sizeof(int) * (size_t)N);
}

static void rebuild_L0(void) {
    nL0 = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0) L0[nL0++] = v;
}

/* Degree-preserving bipartite switch: a-b, c-e -> a-e, c-b with a, c on side 0. */
static int do_switch(int *a_out, int *b_out, int *c_out, int *e_out) {
    if (nL0 < 2) return 0;
    int a = L0[rndi(nL0)];
    int c = L0[rndi(nL0)];
    if (a == c || deg[a] == 0 || deg[c] == 0) return 0;
    int b = adj[a][rndi(deg[a])];
    int e = adj[c][rndi(deg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    *a_out = a; *b_out = b; *c_out = c; *e_out = e;
    return 1;
}

static void undo_switch(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Metropolis annealing on bad-pair count. Returns 1 if the graph became valid. */
static int anneal(int iters, double T0, double T1) {
    rebuild_L0();
    long long cur = bad_pairs();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && clock() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a, b, c, e;
        if (!do_switch(&a, &b, &c, &e)) continue;
        long long nw = bad_pairs();
        long long delta = nw - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cur = nw;
        else undo_switch(a, b, c, e);
    }
    return cur == 0;
}

/* Plateau walk: only zero-cost switches are kept, so the graph stays valid. */
static void plateau(int steps) {
    rebuild_L0();
    for (int i = 0; i < steps; i++) {
        int a, b, c, e;
        if (!do_switch(&a, &b, &c, &e)) continue;
        if (bad_pairs() != 0) undo_switch(a, b, c, e);
    }
}

/* Insert one vertex joined to a greedy cover of the opposite side's (D-1)-balls. */
static void grow_once(void) {
    int W = (N + 63) / 64;
    int s = rndi(2);
    int cs = 1 - s;
    compute_balls(D_ - 1, ballR);
    uint64_t covered[MAXW];
    for (int w = 0; w < W; w++) covered[w] = 0;
    char used[MAXN];
    memset(used, 0, sizeof(used));
    int chosen[MAXD];
    int nc = 0;
    int ncand = 0;
    for (int v = 0; v < N; v++) if (col[v] == cs) ncand++;
    int want = d_ < ncand ? d_ : ncand;
    while (nc < want) {
        int best = -1;
        double bestkey = -1.0;
        for (int c = 0; c < N; c++) {
            if (col[c] != cs || used[c]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(ballR[c][w] & ~covered[w]);
            double key = (double)g + 0.5 * rndu();
            if (key > bestkey) { bestkey = key; best = c; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) covered[w] |= ballR[best][w];
    }
    int v = N;
    N++;
    deg[v] = 0;
    col[v] = s;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (deg[c] >= d_) {
            int y = adj[c][rndi(deg[c])];
            del_edge(c, y);
        }
        add_edge(v, c);
    }
}

/* Add cross-side edges between deficient vertices (only lowers distances). */
static void fill(void) {
    int tries = 30 * N;
    for (int t = 0; t < tries; t++) {
        int a = rndi(N), b = rndi(N);
        if (col[a] == col[b] || deg[a] >= d_ || deg[b] >= d_) continue;
        if (has_edge(a, b)) continue;
        add_edge(a, b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = strtod(argv[4], NULL);
    if (d_ < 2 || d_ > MAXD - 4 || D_ < 2) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd();
    t_end = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);

    long long mb = 0, pw = 1;
    for (int i = 0; i < D_; i++) {
        mb += pw;
        if (mb > MAXN) break;
        pw *= (d_ - 1);
    }
    moore_ = 2 * mb;
    if (moore_ > MAXN) moore_ = MAXN;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int ok = 1;
    if (n < 1 || n > MAXN || m < 0) ok = 0;
    if (ok) {
        N = n;
        for (int v = 0; v < N; v++) deg[v] = 0;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
            if (has_edge(u, v)) continue;
            if (deg[u] >= d_ || deg[v] >= d_) { ok = 0; break; }
            add_edge(u, v);
        }
    }
    if (ok && !colour_graph()) ok = 0;
    if (!ok) set_kdd();

    bestOK = 0;
    if (bad_pairs() != 0) set_kdd();
    save_best();

    int fails = 0;
    while (clock() < t_end) {
        if ((long long)N + 1 > moore_) break;
        if (fails >= 40) { plateau(2000); fails = 0; }
        else if (rndi(4) == 0) plateau(150);
        save_state();
        grow_once();
        fill();
        if (anneal(ANNEAL_ITERS, 1.2, 0.08)) {
            save_best();
            fails = 0;
        } else {
            restore_state();
            fails++;
        }
    }

    if (!bestOK) { printf("0 0\n"); return 0; }
    long long M = 0;
    for (int v = 0; v < bN; v++)
        for (int k = 0; k < bdeg[v]; k++)
            if (badj[v][k] > v) M++;
    printf("%d %lld\n", bN, M);
    for (int v = 0; v < bN; v++)
        for (int k = 0; k < bdeg[v]; k++)
            if (badj[v][k] > v) printf("%d %d\n", v, badj[v][k]);
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
#
# Change: each trial first measures its bad-pair count and skips hopeless
# trials (too many bad pairs to repair cheaply), and uses a shorter annealing
# budget. Many more kill-repair-regrow trials fit in the same time.
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
        # Skip trials whose damage is too large to repair in a short anneal.
        if _cost(adj, D) > 40:
            continue
        if not _anneal(adj, color, d, D, rng, 60, deadline):
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
# Cross-matching doubling with annealed repair.
#
# Take two copies A and B of a valid base graph G (n vertices, max degree d).
# Each vertex v has spare = d - deg(v). Within each copy, edges stay as they are.
# Spare stubs are joined across the copies: an A-vertex of colour c is matched to
# a B-copy of a vertex of colour 1 - c. Because the copy has the same colouring,
# every cross edge joins opposite colours, so the result is bipartite, degrees
# stay <= d, and every vertex keeps its own spare quota in each role. The 2n-vertex
# graph is then repaired with degree-preserving bipartite switches (the same
# annealer as LNS), accepted only at zero bad pairs. The Moore bound is checked
# first, so no hopeless attempt is made.
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
    # Matching 1: A colour-0 stubs with B colour-1 copies.
    for x, w in zip(s0, s1):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    # Matching 2: A colour-1 stubs with B colour-0 copies.
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
        # Restart the annealer from a fresh cross matching.
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
# Vertex splitting with neighbour partition, then annealed repair.
#
# Pick a vertex v with at least two neighbours and split it into v and a new
# twin-like vertex w on the same side. The neighbours of v are partitioned at
# random: S1 stays joined to v, S2 is moved to w. Every neighbour keeps exactly
# one edge into {v, w}, so its degree is unchanged, and v and w each have degree
# at most deg(v) <= d. Distances can grow, because v and w no longer share their
# neighbourhood. Spare degree is then used by _fill, and degree-preserving
# switches repair the diameter. A split is kept only at zero bad pairs, so the
# walk stays on valid graphs and each success adds one vertex.
# ----------------------------------------------------------------------------

def _split_repair(n, edges, d, D, deadline, rng, consider):
    """Repeatedly split a random vertex of the current valid graph and repair it."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        cur_n = len(adj)
        cands = [v for v in range(cur_n) if len(adj[v]) >= 2]
        if not cands:
            break
        v = rng.choice(cands)
        nb = list(adj[v])
        rng.shuffle(nb)
        k = rng.randint(1, len(nb) - 1)
        S1, S2 = nb[:k], nb[k:]
        w = cur_n
        adj.append(set(S2))
        color.append(color[v])
        adj[v] = set(S1)
        for u in S2:
            adj[u].discard(v)
            adj[u].add(w)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(a, b) for a in range(m) for b in adj[a] if a < b]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _prune_then_split(n, edges, d, D, deadline, rng, consider):
    """Prune redundant edges first (frees degree), then run split-repair from the result."""
    if time.monotonic() >= deadline:
        return
    pe = _prune_redundant(n, edges, D, rng, deadline, 160)
    n2, e2 = _grow(n, pe, d, D, deadline, rng)
    consider(n2, e2)
    _split_repair(n2, e2, d, D, deadline, rng, consider)


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


def _python_build(d, D, seed, time_limit):
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
            grow_end = start + 0.2 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Cross-matching doubling of the best base that fits under the Moore bound.
    if D >= 2 and 2 * base_n <= lib.moore_bound(d, D):
        dbl_end = start + 0.20 * time_limit
        _try_doubling(base_n, base_e, d, D, dbl_end, rng, consider)

    # Randomized twin-duplication pipelines from the structured base (short, cheap).
    if D >= 2:
        trial_end = start + 0.10 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Kill-repair-regrow search from the best valid graph found so far (main improver).
    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.60 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # Prune redundant edges to free degree, then regrow from the best graph.
    if D >= 2 and time.monotonic() < deadline:
        prune_end = start + 0.72 * time_limit
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    # Prune, regrow, then split vertices and repair the diameter.
    if D >= 2 and time.monotonic() < deadline:
        split_end = start + 0.84 * time_limit
        _prune_then_split(best_n, best_e, d, D, split_end, rng, consider)

    # Bold stage: repeated add-and-repair from the largest valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    # Python constructions and LNS use the first ~40% of the budget.
    base_n, base_e = _python_build(d, D, seed, 0.45 * time_limit)
    if not lib.is_valid(base_n, base_e, d, D):
        base_n, base_e = lib.haar_graph(d, range(d))
    best = (base_n, list(base_e))
    if D < 2 or d < 2 or d > 60:
        return best

    # The C engine grows the base with bitset-cost annealing and plateau walks.
    avail = time_limit - (time.monotonic() - t0) - 0.12 * time_limit - 1.0
    if avail < 2.0:
        return best
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{0.8 * avail:.2f}"],
                        stdin_graph=best, timeout=avail)
        n, e = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))
    except Exception:
        pass
    return best
