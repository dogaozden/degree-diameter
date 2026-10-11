import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost annealing with add-vertex and kill-and-regrow moves.
#
# The state is a valid bipartite graph with max degree d. Each attempt starts
# from the best valid graph, either adds one vertex or deletes one and adds
# two, then repairs with degree-preserving bipartite double-edge switches.
# The cost is the number of vertex pairs at distance > D, computed by bitset
# ball expansion. A repaired state with cost 0 is a valid graph, and it is kept
# when it is at least as large as the best so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXD 64
#define ITER 1500

static int d, D, N, W;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static uint64_t PA[MAXN * MAXW], PB[MAXN * MAXW];

static int bN;
static int bAdj[MAXN][MAXD];
static int bDeg[MAXN];
static int bCol[MAXN];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset of vertices within distance r of each vertex; sets W for current N. */
static uint64_t *balls(int r) {
    uint64_t *X = PA, *Y = PB, *t;
    int v, w, k, i;
    W = (N + 63) >> 6;
    for (v = 0; v < N; v++) {
        for (w = 0; w < W; w++) X[v * W + w] = 0;
        X[v * W + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (k = 0; k < r; k++) {
        for (v = 0; v < N; v++) {
            for (w = 0; w < W; w++) Y[v * W + w] = X[v * W + w];
            for (i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (w = 0; w < W; w++) Y[v * W + w] |= X[u * W + w];
            }
        }
        t = X; X = Y; Y = t;
    }
    return X;
}

/* Number of unordered pairs at distance > D. */
static long cost(void) {
    uint64_t *X = balls(D);
    long bad = 0;
    int v, w, c;
    for (v = 0; v < N; v++) {
        c = 0;
        for (w = 0; w < W; w++) c += popc(X[v * W + w]);
        bad += N - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void rm_one(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; break; }
    for (i = 0; i < deg[b]; i++) if (adj[b][i] == a) { adj[b][i] = adj[b][--deg[b]]; break; }
}

/* Join deficient opposite-side vertices in random order. */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0, v, i, j, t, a, b;
    for (v = 0; v < N; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    for (i = nl - 1; i > 0; i--) { j = rndint(i + 1); t = L[i]; L[i] = L[j]; L[j] = t; }
    for (i = nr - 1; i > 0; i--) { j = rndint(i + 1); t = R[i]; R[i] = R[j]; R[j] = t; }
    for (i = 0; i < nl; i++) {
        a = L[i];
        for (j = 0; j < nr && deg[a] < d; j++) {
            b = R[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Append a vertex on side 1-c, joined to a greedy near-cover of side c. */
static void add_vertex_repair(int c) {
    static int used[MAXN];
    int chosen[MAXD], nc = 0, k, s, w, v, i, best, g;
    long key, bestkey;
    uint64_t cov[MAXW];
    uint64_t *B2 = balls(D - 1);
    for (w = 0; w < MAXW; w++) cov[w] = 0;
    for (s = 0; s < N; s++) used[s] = 0;
    for (k = 0; k < d; k++) {
        best = -1;
        bestkey = -1;
        for (s = 0; s < N; s++) {
            if (col[s] != 1 - c || used[s]) continue;
            g = 0;
            for (w = 0; w < W; w++) g += popc(B2[s * W + w] & ~cov[w]);
            key = (long)g * 4096 + (long)(rnd() % 4096);
            if (key > bestkey) { bestkey = key; best = s; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (w = 0; w < W; w++) cov[w] |= B2[best * W + w];
    }
    v = N;
    N++;
    W = (N + 63) >> 6;
    deg[v] = 0;
    col[v] = 1 - c;
    for (i = 0; i < nc; i++) {
        s = chosen[i];
        if (deg[s] >= d) {
            int t = adj[s][rndint(deg[s])];
            rm_one(s, t);
        }
        add_edge(s, v);
    }
    fill();
}

/* Remove vertex x; the last vertex takes its label, keeping the graph compact. */
static void delete_vertex(int x) {
    int last = N - 1, t;
    while (deg[x] > 0) rm_one(x, adj[x][0]);
    if (x != last) {
        while (deg[last] > 0) {
            t = adj[last][0];
            rm_one(last, t);
            add_edge(x, t);
        }
        col[x] = col[last];
    }
    deg[last] = 0;
    N--;
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. True if cost reaches 0. */
static int anneal(int iters, long *out) {
    long cur = cost(), nw, delta;
    int it, a, b, c, e;
    for (it = 0; it < iters && cur > 0; it++) {
        a = rndint(N);
        if (col[a] != 0 || deg[a] == 0) continue;
        b = adj[a][rndint(deg[a])];
        c = rndint(N);
        if (c == a || col[c] != 0 || deg[c] == 0) continue;
        e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        rm_one(a, b);
        rm_one(c, e);
        add_edge(a, e);
        add_edge(c, b);
        nw = cost();
        delta = nw - cur;
        if (delta <= 0 || (delta == 1 && rndint(8) == 0) || (delta > 1 && rndint(64) == 0)) {
            cur = nw;
        } else {
            rm_one(a, e);
            rm_one(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    *out = cur;
    return cur == 0;
}

static void save_best(void) {
    int v;
    bN = N;
    for (v = 0; v < N; v++) {
        bDeg[v] = deg[v];
        bCol[v] = col[v];
        memcpy(bAdj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void load_best(void) {
    int v;
    N = bN;
    for (v = 0; v < N; v++) {
        deg[v] = bDeg[v];
        col[v] = bCol[v];
        memcpy(adj[v], bAdj[v], sizeof(int) * (size_t)deg[v]);
    }
}

int main(int argc, char **argv) {
    int n, m, i, u, v, s, h, t;
    int *q = NULL;
    double tl, t_end;
    long cc;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    tl = atof(argv[4]);
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN - 64 || d < 1 || d > MAXD - 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (v = 0; v < N; v++) { deg[v] = 0; col[v] = -1; }
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (deg[u] >= MAXD || deg[v] >= MAXD) continue;
        if (!has_edge(u, v)) add_edge(u, v);
    }
    /* Two-colour the input (it is bipartite). */
    q = (int *)malloc(sizeof(int) * (size_t)(N + 1));
    for (s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        h = 0; t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (i = 0; i < deg[x]; i++) {
                int y = adj[x][i];
                if (col[y] == -1) { col[y] = 1 - col[x]; q[t++] = y; }
            }
        }
    }
    free(q);

    save_best();
    if (cost() != 0) {
        /* Input is not valid for this (d, D): echo it back unchanged. */
        goto output;
    }

    t_end = wall() + tl * 0.95 - 0.3;
    while (wall() < t_end && bN < MAXN - 4) {
        int kill = (rnd() % 3 == 0);
        load_best();
        if (kill && N > 4) delete_vertex(rndint(N));
        add_vertex_repair(rndint(2));
        if (kill) add_vertex_repair(rndint(2));
        if (anneal(ITER, &cc) && N >= bN) save_best();
    }

output:
    {
        int ecount = 0;
        for (v = 0; v < bN; v++)
            for (i = 0; i < bDeg[v]; i++)
                if (bAdj[v][i] > v) ecount++;
        printf("%d %d\n", bN, ecount);
        for (v = 0; v < bN; v++)
            for (i = 0; i < bDeg[v]; i++)
                if (bAdj[v][i] > v) printf("%d %d\n", v, bAdj[v][i]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (structured bases and cheap growth).
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
# Twin duplication: a non-adjacent twin of v (same neighbourhood) keeps all
# distances to other vertices, and the diameter bound, for D >= 2.
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end_all = start + 0.92 * time_limit
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.2 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C annealing engine: add-vertex and kill-and-regrow repair from the best graph.
    if D >= 2 and 2 <= d < 60:
        remaining = end_all - time.monotonic()
        if remaining > 4.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 3.0, 2)],
                                stdin_graph=(best_n, best_e), timeout=remaining - 1.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
