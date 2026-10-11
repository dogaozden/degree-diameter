import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: annealed kill/add/repair LNS on bipartite graphs.
#
# Each step copies the current valid graph, either adds a vertex (joined to a
# random set of opposite-side vertices, stealing an edge from saturated ones) or
# kills one vertex and then adds one back, fills spare degree across sides, and
# repairs the diameter with degree-preserving bipartite switches that minimise
# the number of pairs at distance > D. A successful repair is accepted; the
# best graph is kept. Distances are computed with bitsets.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXD 40
#define MAXW (MAXN / 64)
#define ANN_IT 900

static int N = 0, DEG = 0, DIA = 0;
static int nb[MAXN][MAXD];
static int dg[MAXN];
static int col[MAXN];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static double t_end = 0.0;
static int side0[MAXN];
static int ns0 = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has(int u, int v) {
    for (int k = 0; k < dg[u]; k++) if (nb[u][k] == v) return 1;
    return 0;
}

static void add_e(int u, int v) {
    nb[u][dg[u]++] = v;
    nb[v][dg[v]++] = u;
}

static void del_from(int u, int v) {
    for (int k = 0; k < dg[u]; k++) {
        if (nb[u][k] == v) {
            nb[u][k] = nb[u][--dg[u]];
            return;
        }
    }
}

static void del_e(int u, int v) {
    del_from(u, v);
    del_from(v, u);
}

/* Number of unordered pairs at distance > DIA (unreachable pairs count). */
static long long cost(void) {
    int nw = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIA; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < dg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Degree-preserving bipartite switches minimising bad pairs. True if cost reaches 0. */
static int anneal(int iters) {
    long long cur = cost();
    ns0 = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0) side0[ns0++] = v;
    if (ns0 < 2) return cur == 0;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now_s() > t_end) break;
        int a = side0[rint_(ns0)];
        if (dg[a] == 0) continue;
        int b = nb[a][rint_(dg[a])];
        int c = side0[rint_(ns0)];
        if (c == a || dg[c] == 0) continue;
        int e = nb[c][rint_(dg[c])];
        if (has(a, e) || has(c, b)) continue;
        del_e(a, b);
        del_e(c, e);
        add_e(a, e);
        add_e(c, b);
        long long nc = cost();
        if (nc <= cur || (nc == cur + 1 && rint_(10) == 0)) {
            cur = nc;
        } else {
            del_e(a, e);
            del_e(c, b);
            add_e(a, b);
            add_e(c, e);
        }
    }
    return cur == 0;
}

/* Add cross-side edges between deficient vertices. */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (dg[v] < DEG) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    if (nl == 0 || nr == 0) return;
    long iters = 40L * (nl + nr) + 50;
    for (long it = 0; it < iters; it++) {
        int a = L[rint_(nl)];
        int b = R[rint_(nr)];
        if (dg[a] < DEG && dg[b] < DEG && !has(a, b)) add_e(a, b);
    }
}

/* Append a vertex on a random side, joined to up to DEG opposite-side vertices. */
static void add_vertex(void) {
    if (N + 1 >= MAXN) return;
    int s = rint_(2);
    int v = N++;
    col[v] = s;
    dg[v] = 0;
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < v; u++) if (col[u] == 1 - s) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int chosen = 0;
    for (int i = 0; i < nc && chosen < DEG; i++) {
        int u = cand[i];
        if (dg[u] < DEG) {
            add_e(u, v);
            chosen++;
        }
    }
    for (int i = 0; i < nc && chosen < DEG; i++) {
        int u = cand[i];
        if (dg[u] >= DEG) {
            int w = nb[u][rint_(dg[u])];
            del_e(u, w);
            add_e(u, v);
            chosen++;
        }
    }
}

/* Delete vertex x, moving the last vertex into its slot. */
static void remove_vertex(int x) {
    for (int k = 0; k < dg[x]; k++) del_from(nb[x][k], x);
    dg[x] = 0;
    int L = N - 1;
    if (x != L) {
        for (int k = 0; k < dg[L]; k++) {
            int y = nb[L][k];
            for (int j = 0; j < dg[y]; j++) if (nb[y][j] == L) nb[y][j] = x;
        }
        memcpy(nb[x], nb[L], sizeof(int) * (size_t)dg[L]);
        dg[x] = dg[L];
        col[x] = col[L];
    }
    dg[L] = 0;
    N--;
}

static void copy_state(int (*dnb)[MAXD], int *ddg, int *dcol, int *dN,
                       int (*snb)[MAXD], const int *sdg, const int *scol, int sN) {
    memcpy(dnb, snb, sizeof(int) * MAXD * (size_t)sN);
    memcpy(ddg, sdg, sizeof(int) * (size_t)sN);
    memcpy(dcol, scol, sizeof(int) * (size_t)sN);
    *dN = sN;
}

static int bipart(void) {
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < dg[u]; k++) {
                int v = nb[u][k];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void output_graph(int n, int (*xnb)[MAXD], const int *xdg) {
    long long m = 0;
    for (int v = 0; v < n; v++) m += xdg[v];
    m /= 2;
    printf("%d %lld\n", n, m);
    for (int u = 0; u < n; u++) {
        for (int k = 0; k < xdg[u]; k++) {
            int v = xnb[u][k];
            if (u < v) printf("%d %d\n", u, v);
        }
    }
}

static int cnb[MAXN][MAXD], cdg[MAXN], ccol[MAXN], cN;
static int bnb[MAXN][MAXD], bdg[MAXN], bcol[MAXN], bN;

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now_s() + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN || DEG < 2 || DEG >= MAXD || DIA < 2) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (dg[u] >= DEG || dg[v] >= DEG || has(u, v)) continue;
        add_e(u, v);
    }
    if (!bipart() || cost() != 0) {
        printf("0 0\n");
        return 0;
    }

    copy_state(cnb, cdg, ccol, &cN, nb, dg, col, N);
    copy_state(bnb, bdg, bcol, &bN, nb, dg, col, N);

    while (now_s() < t_end) {
        copy_state(nb, dg, col, &N, cnb, cdg, ccol, cN);
        if (rint_(2) == 0 || N < 3) {
            add_vertex();
        } else {
            remove_vertex(rint_(N));
            add_vertex();
        }
        fill();
        if (anneal(ANN_IT)) {
            copy_state(cnb, cdg, ccol, &cN, nb, dg, col, N);
            if (cN > bN) copy_state(bnb, bdg, bcol, &bN, cnb, cdg, ccol, cN);
        }
        if (cN < bN - 3) copy_state(cnb, cdg, ccol, &cN, bnb, bdg, bcol, bN);
    }
    output_graph(bN, bnb, bdg);
    return 0;
}
"""


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
    """Dense structured graph with degree at least d, later thinned into a valid graph."""
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
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Python annealer (used by cross-matching doubling).
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
    if time.monotonic() < deadline and _anneal(B, color2, d, D, rng, 3000, deadline):
        return N, [(u, v) for u in range(N) for v in B[u] if u < v]
    return None


def _try_doubling(n, edges, d, D, deadline, rng, consider):
    """Attempt cross-matching doubling of the base until the deadline."""
    while time.monotonic() < deadline:
        res = _double_cross(n, edges, d, D, rng, deadline)
        if res is not None:
            N, e = res
            consider(N, e)
            return True
    return False


# ----------------------------------------------------------------------------
# C engine glue.
# ----------------------------------------------------------------------------

def _c_engine(d, D, n, e, seconds, seed):
    """Run the C LNS from a valid start graph. Returns (n, edges) or None on any failure."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(seconds, 2)],
                        stdin_graph=(n, e), timeout=seconds + 5.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) or PG(2,q)) grown, doubling and twin trials
#   B  thinned dense graph (degree reduction + vertex deletion)
#   C  C annealed kill/add/repair LNS from the best valid graph, most of the budget
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

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

    # Phase A: structured base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            consider(*_grow(n0, e0, d, D, at(0.05), rng))
    if D >= 2 and 2 * base_n <= lib.moore_bound(d, D):
        _try_doubling(base_n, base_e, d, D, at(0.08), rng, consider)
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            consider(*_trial(base_n, base_e, d, D, rng, trial_end))

    # Phase B: thinned dense graph.
    if D >= 2 and time.monotonic() < at(0.20):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.20):
                r = _deletion_trial(d, D, rn, re, rng, at(0.20))
                if r is None:
                    break
                consider(*r)

    # Phase C: C annealed LNS from the best valid graph found so far.
    if D >= 2 and 2 <= d < 40:
        c_secs = start + 0.84 * time_limit - time.monotonic() - 1.0
        if c_secs > 1.0:
            res = _c_engine(d, D, best_n, best_e, c_secs, seed)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
