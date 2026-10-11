import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: bipartite edge-switch annealing with vertex add/kill moves.
# Every accepted state has zero bad pairs; the best valid graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXD 64
#define ITERS 1000

typedef uint64_t row_t[WORDS];

static int N, Dg, DIAM;
static int deg[MAXN], col[MAXN];
static int adj[MAXN][MAXD];
static int sN, sDeg[MAXN], sCol[MAXN], sAdj[MAXN][MAXD];
static int bN, bDeg[MAXN], bCol[MAXN], bAdj[MAXN][MAXD];
static row_t bufA[MAXN], bufB[MAXN];
static uint64_t rs = 1;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}

static int rndint(int m) {
    return m <= 0 ? 0 : (int)(rnd64() % (uint64_t)m);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void rm1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
    }
}

static void add_e(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void rem_e(int a, int b) {
    rm1(a, b);
    rm1(b, a);
}

/* Bitmask of vertices within distance r of each vertex. */
static row_t *balls(int r) {
    int W = (N + 63) >> 6;
    row_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(row_t));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        row_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static long cost(void) {
    int W = (N + 63) >> 6;
    row_t *R = balls(DIAM);
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(R[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

static void save_state(int *n_out, int *deg_out, int *col_out, int (*adj_out)[MAXD]) {
    *n_out = N;
    for (int v = 0; v < N; v++) {
        deg_out[v] = deg[v];
        col_out[v] = col[v];
        memcpy(adj_out[v], adj[v], sizeof(int) * MAXD);
    }
}

static void load_state(int n_in, const int *deg_in, const int *col_in, int (*adj_in)[MAXD]) {
    N = n_in;
    for (int v = 0; v < N; v++) {
        deg[v] = deg_in[v];
        col[v] = col_in[v];
        memcpy(adj[v], adj_in[v], sizeof(int) * MAXD);
    }
}

static void kill_vertex(int v) {
    int dv = deg[v];
    for (int i = 0; i < dv; i++) rm1(adj[v][i], v);
    deg[v] = 0;
    int L = N - 1;
    if (v != L) {
        for (int i = 0; i < deg[L]; i++) {
            int u = adj[L][i];
            for (int j = 0; j < deg[u]; j++) {
                if (adj[u][j] == L) { adj[u][j] = v; break; }
            }
        }
        deg[v] = deg[L];
        col[v] = col[L];
        memcpy(adj[v], adj[L], sizeof(int) * MAXD);
    }
    deg[L] = 0;
    N--;
}

/* Add a vertex joined to a cover of radius DIAM-1 balls on one side. */
static int add_vertex(void) {
    if (N + 1 > MAXN || DIAM < 2) return 0;
    int side = rndint(2);
    int W = (N + 63) >> 6;
    row_t *R = balls(DIAM - 1);
    row_t covered;
    memset(covered, 0, sizeof covered);
    int chosen[MAXD];
    int nc = 0;
    int ncov = 0;
    while (ncov < N && nc < Dg) {
        int best = -1;
        long bestsc = -1;
        for (int s = 0; s < N; s++) {
            if (col[s] != side) continue;
            int used = 0;
            for (int k = 0; k < nc; k++) if (chosen[k] == s) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc64(R[s][w] & ~covered[w]);
            if (g == 0) continue;
            long sc = (long)g * 1000 + rndint(1000);
            if (sc > bestsc) { bestsc = sc; best = s; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) covered[w] |= R[best][w];
        ncov = 0;
        for (int w = 0; w < W; w++) ncov += popc64(covered[w]);
    }
    if (ncov < N) return 0;
    int v = N;
    N++;
    deg[v] = 0;
    col[v] = 1 - side;
    for (int k = 0; k < nc; k++) {
        int s = chosen[k];
        if (deg[s] >= Dg) {
            int t = adj[s][rndint(deg[s])];
            rem_e(s, t);
        }
        add_e(s, v);
    }
    return 1;
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    static int Lf[MAXN], Rf[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < Dg) {
            if (col[v] == 0) Lf[nl++] = v; else Rf[nr++] = v;
        }
    }
    if (nl == 0 || nr == 0) return;
    for (int t = 0; t < 20000; t++) {
        int a = Lf[rndint(nl)], b = Rf[rndint(nr)];
        if (deg[a] >= Dg || deg[b] >= Dg || has_edge(a, b)) continue;
        add_e(a, b);
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static long anneal(int iters, clock_t deadline) {
    long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && clock() > deadline) break;
        int s = rndint(2);
        int a = -1, c = -1;
        for (int tr = 0; tr < 60 && a < 0; tr++) {
            int x = rndint(N);
            if (col[x] == s && deg[x] > 0) a = x;
        }
        for (int tr = 0; tr < 60 && c < 0; tr++) {
            int x = rndint(N);
            if (x != a && col[x] == s && deg[x] > 0) c = x;
        }
        if (a < 0 || c < 0) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        rem_e(a, b);
        rem_e(c, e);
        add_e(a, e);
        add_e(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd64() % 10 == 0)) {
            cur = nw;
        } else {
            rem_e(a, e);
            rem_e(c, b);
            add_e(a, b);
            add_e(c, e);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dg = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();
    clock_t deadline = t0 + (clock_t)(tl * CLOCKS_PER_SEC);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 1 || n > MAXN || m < 0 || Dg < 1 || Dg > MAXD - 4 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < n; v++) deg[v] = 0;
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            deg[u] >= Dg || deg[v] >= Dg || has_edge(u, v)) {
            bad = 1;
            break;
        }
        add_e(u, v);
    }
    if (bad) { printf("0 0\n"); return 0; }

    for (int v = 0; v < n; v++) col[v] = -1;
    static int stack[MAXN];
    for (int s = 0; s < n && !bad; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; stack[sp++] = v; }
                else if (col[v] == col[u]) { bad = 1; break; }
            }
            if (bad) break;
        }
    }
    if (bad) { printf("0 0\n"); return 0; }

    save_state(&bN, bDeg, bCol, bAdj);

    while (clock() < deadline) {
        save_state(&sN, sDeg, sCol, sAdj);
        int changed = 0;
        if (N > DIAM + 3 && rndint(4) == 0) {
            kill_vertex(rndint(N));
            changed = 1;
        }
        if (add_vertex()) changed = 1;
        if (!changed) continue;
        fill();
        if (anneal(ITERS, deadline) == 0) {
            if (N > bN) save_state(&bN, bDeg, bCol, bAdj);
            else if (N < bN - 3) load_state(bN, bDeg, bCol, bAdj);
        } else {
            load_state(sN, sDeg, sCol, sAdj);
        }
    }

    int cnt = 0;
    for (int v = 0; v < bN; v++)
        for (int i = 0; i < bDeg[v]; i++)
            if (v < bAdj[v][i]) cnt++;
    printf("%d %d\n", bN, cnt);
    for (int v = 0; v < bN; v++)
        for (int i = 0; i < bDeg[v]; i++)
            if (v < bAdj[v][i]) printf("%d %d\n", v, bAdj[v][i]);
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
    """A dense structured graph whose degree is at least d, to be thinned into a valid graph."""
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
# Twin duplication: non-adjacent twins keep distances and bipartiteness.
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
# Thinning: reduce a dense structured graph to degree d, delete the worst
# vertices until the diameter holds, then regrow. Deletion keeps validity.
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
# Python-side annealing helpers (used by cross-matching doubling).
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
    if time.monotonic() < deadline:
        if _anneal(B, color2, d, D, rng, 3000, deadline):
            return N, [(u, v) for u in range(N) for v in B[u] if u < v]
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
# Driver. Fractions of time_limit:
#   A  structured base (W(q) or PG(2,q)) grown; twin trials
#   B  cross-matching doubling (only if 2n fits the Moore bound)
#   C  thinning of a dense structured graph
#   D  C engine (annealed add/kill LNS) from the best valid graph, to the end
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base and its growth.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.08 * time_limit, rng)
            consider(n1, e1)

    # Calibration cases already at the Moore bound return at once.
    if best_n >= moore:
        return best_n, list(best_e)

    if D >= 2:
        trial_end = start + 0.12 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: cross-matching doubling, when 2n fits under the Moore bound.
    if D >= 2 and 2 * base_n <= moore:
        dbl_end = start + 0.18 * time_limit
        _try_doubling(base_n, base_e, d, D, dbl_end, rng, consider)

    # Phase C: thinning of a dense structured graph.
    if D >= 2 and best_n < moore and time.monotonic() < start + 0.26 * time_limit:
        thin_end = start + 0.26 * time_limit
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < thin_end:
                r = _deletion_trial(d, D, rn, re, rng, thin_end)
                if r is None:
                    break
                consider(*r)

    # Phase D: C engine from the best valid graph found so far.
    if D >= 2 and best_n < moore:
        c_end = start + 0.88 * time_limit - 2.0
        budget = c_end - time.monotonic() - 1.5
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
