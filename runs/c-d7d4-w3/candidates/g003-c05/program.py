import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: vertex insertion with bipartite annealing repair.
#
# State: a valid bipartite graph with max degree DEGMAX and diameter <= DIAM.
# Growth step: add one vertex on a random side, joined to a greedy cover of
# radius DIAM-1 balls on the other side (stealing one edge from full vertices).
# Repair: degree-preserving bipartite double-edge switches, Metropolis-accepted,
# minimising the number of vertex pairs at distance > DIAM. Each attempt either
# returns to a valid graph one vertex larger, or restores the last valid snapshot.
# The best valid graph is printed before the deadline.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXDEG 32
#define WMAX (MAXN / 64)

typedef uint64_t u64;

static int DEGMAX = 3, DIAM = 2;
static int N = 0;
static int adj[MAXN][MAXDEG];
static int dg[MAXN];
static int col[MAXN];
static u64 bufA[MAXN][WMAX];
static u64 bufB[MAXN][WMAX];
static int sN = 0;
static int sAdj[MAXN][MAXDEG];
static int sDg[MAXN];
static int sCol[MAXN];
static u64 rs = 88172645463325252ULL;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (u64)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    for (int i = 0; i < dg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][dg[a] - 1];
            dg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    adj[a][dg[a]++] = b;
    adj[b][dg[b]++] = a;
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* X <- bitset of vertices within distance r of each vertex. Y is scratch. */
static void compute_balls(int r, u64 X[][WMAX], u64 Y[][WMAX]) {
    int n = N, w = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int j = 0; j < w; j++) X[v][j] = 0;
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            for (int j = 0; j < w; j++) Y[v][j] = X[v][j];
            for (int i = 0; i < dg[v]; i++) {
                const u64 *src = X[adj[v][i]];
                for (int j = 0; j < w; j++) Y[v][j] |= src[j];
            }
        }
        for (int v = 0; v < n; v++)
            for (int j = 0; j < w; j++) X[v][j] = Y[v][j];
    }
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static long bad_pairs(void) {
    int n = N, w = (n + 63) >> 6;
    compute_balls(DIAM, bufA, bufB);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int j = 0; j < w; j++) c += pc64(bufA[v][j]);
        bad += n - c;
    }
    return bad / 2;
}

static int color_graph(void) {
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int qh = 0, qt = 0;
        col[s] = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < dg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[qt++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Add one vertex on a random side, joined to a greedy cover of the other side. */
static int insert_vertex(void) {
    int n = N;
    if (n + 1 > MAXN - 1) return 0;
    int s = rndint(2);
    int w = (n + 63) >> 6;
    compute_balls(DIAM - 1, bufA, bufB);
    u64 covered[WMAX];
    for (int j = 0; j < WMAX; j++) covered[j] = 0;
    int chosen[MAXDEG];
    int nch = 0;
    for (int k = 0; k < DEGMAX; k++) {
        int best = -1;
        double bestsc = -1.0;
        for (int t = 0; t < n; t++) {
            if (col[t] != 1 - s) continue;
            int used = 0;
            for (int i = 0; i < nch; i++)
                if (chosen[i] == t) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int j = 0; j < w; j++) g += pc64(bufA[t][j] & ~covered[j]);
            double sc = g + 0.5 * rnd01();
            if (sc > bestsc) { bestsc = sc; best = t; }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        for (int j = 0; j < w; j++) covered[j] |= bufA[best][j];
    }
    if (nch == 0) return 0;
    int v = n;
    N = n + 1;
    dg[v] = 0;
    col[v] = s;
    for (int i = 0; i < nch; i++) {
        int t = chosen[i];
        if (dg[t] >= DEGMAX) {
            int x = adj[t][rndint(dg[t])];
            del_edge(t, x);
        }
        add_edge(v, t);
    }
    return 1;
}

/* Add cross-colour edges between deficient vertices (never hurts validity). */
static void fill(void) {
    static int L0[MAXN], L1[MAXN];
    int c0 = 0, c1 = 0;
    for (int v = 0; v < N; v++) {
        if (dg[v] >= DEGMAX) continue;
        if (col[v] == 0) L0[c0++] = v;
        else L1[c1++] = v;
    }
    for (int i = c0 - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = L0[i]; L0[i] = L0[j]; L0[j] = t;
    }
    for (int i = c1 - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = L1[i]; L1[i] = L1[j]; L1[j] = t;
    }
    for (int i = 0; i < c0; i++) {
        int a = L0[i];
        for (int j = 0; j < c1 && dg[a] < DEGMAX; j++) {
            int b = L1[j];
            if (dg[b] < DEGMAX && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static long anneal(long iters, long cur, double deadline) {
    static int L0[MAXN];
    int c0 = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == 0) L0[c0++] = v;
    if (c0 == 0) return cur;
    const double T = 0.5;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && now() > deadline) break;
        int a = L0[rndint(c0)];
        if (dg[a] == 0) continue;
        int b = adj[a][rndint(dg[a])];
        int c = L0[rndint(c0)];
        if (c == a || dg[c] == 0) continue;
        int e = adj[c][rndint(dg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nc = bad_pairs();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

static void save_snapshot(void) {
    sN = N;
    for (int v = 0; v < N; v++) {
        sDg[v] = dg[v];
        sCol[v] = col[v];
        for (int i = 0; i < dg[v]; i++) sAdj[v][i] = adj[v][i];
    }
}

static void load_snapshot(void) {
    N = sN;
    for (int v = 0; v < N; v++) {
        dg[v] = sDg[v];
        col[v] = sCol[v];
        for (int i = 0; i < dg[v]; i++) adj[v][i] = sAdj[v][i];
    }
}

static void print_snapshot(void) {
    int m = 0;
    for (int v = 0; v < sN; v++)
        for (int i = 0; i < sDg[v]; i++)
            if (sAdj[v][i] > v) m++;
    printf("%d %d\n", sN, m);
    for (int v = 0; v < sN; v++)
        for (int i = 0; i < sDg[v]; i++)
            if (sAdj[v][i] > v) printf("%d %d\n", v, sAdj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DEGMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double deadline = budget * 0.95 - 0.2;
    if (DEGMAX < 1 || DEGMAX > MAXDEG || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) dg[v] = 0;
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { bad = 1; continue; }
        if (has_edge(u, v)) continue;
        if (dg[u] >= DEGMAX || dg[v] >= DEGMAX) { bad = 1; continue; }
        add_edge(u, v);
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    if (N == 0) {
        /* No start graph given: K_{d,d} is valid for DIAM >= 2. */
        N = 2 * DEGMAX;
        for (int i = 0; i < DEGMAX; i++)
            for (int j = 0; j < DEGMAX; j++)
                add_edge(i, DEGMAX + j);
    }
    if (!color_graph()) {
        printf("0 0\n");
        return 0;
    }

    long cur = bad_pairs();
    if (cur != 0) cur = anneal(300000, cur, deadline);
    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    save_snapshot();

    int fails = 0;
    while (now() < deadline) {
        if (!insert_vertex()) break;
        fill();
        long c = bad_pairs();
        long iters = 15000 + 3000L * (fails < 60 ? fails : 60);
        c = anneal(iters, c, deadline);
        if (c == 0) {
            fill();
            save_snapshot();
            fails = 0;
        } else {
            load_snapshot();
            fails++;
        }
    }
    print_snapshot();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (unchanged parent pipeline, now with an explicit budget).
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
    """Try to build a valid 2n-vertex graph from two cross-matched copies of a base graph."""
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


# ----------------------------------------------------------------------------
# Python pipeline (budget = time_limit given by the caller).
# ----------------------------------------------------------------------------

def _py_build(d, D, rng, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit

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
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    rng = random.Random(seed)
    # Phase 1: Python constructions and structured search (about 40% of the budget).
    best_n, best_e = _py_build(d, D, rng, 0.45 * time_limit)
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))

    # Phase 2: C insertion-annealing engine, seeded with the best Python graph.
    left = 0.86 * time_limit - (time.monotonic() - t0) - 3.0
    if (d <= 30 and D >= 2 and left > 2.0
            and best_n < lib.moore_bound(d, D) and best_n + 1 < 2048):
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(left, 2)],
                            stdin_graph=(best_n, best_e), timeout=left + 3.0)
            n2, e2 = lib.parse_graph_text(out)
            if n2 > best_n and lib.is_valid(n2, e2, d, D):
                best_n, best_e = n2, e2
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
