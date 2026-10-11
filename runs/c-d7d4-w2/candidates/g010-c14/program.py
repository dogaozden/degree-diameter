import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Keeps a valid bipartite graph (every pair within distance D) and repeatedly:
#   1. Adds a vertex on one side. Its neighbours are chosen greedily to cover the
#      other side within radius D-1. A saturated neighbour gives up one random edge,
#      so its partner becomes deficient and is refilled with cross-side edges.
#   2. Repairs the diameter with degree-preserving bipartite double-edge switches,
#      minimising the number of bad pairs (annealed acceptance).
#   3. On success, prunes redundant edges (removal keeps diameter <= D), which frees
#      degree for the next insertion. On failure, the snapshot is restored.
#   4. After many failures, returns to the best graph and walks its plateau with
#      valid-only switches.
# Bad pairs are counted exactly with bitset balls, so every stored state is valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 64
#define ANNEAL_IT 2500

static int Dg, DIAM, N, nw;
static int adjv[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static uint64_t *bufA, *bufB, *ballout, *ballr;

static int snapN;
static int snapAdj[MAXN][MAXD];
static int snapDeg[MAXN], snapCol[MAXN];

static int bestN = -1;
static int bestAdj[MAXN][MAXD];
static int bestDeg[MAXN], bestCol[MAXN];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adjv[u][k] == v) return 1;
    return 0;
}

static void del_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adjv[u][k] == v) { adjv[u][k] = adjv[u][--deg[u]]; return; }
    }
}

static void del_edge(int u, int v) { del_one(u, v); del_one(v, u); }

static void add_edge(int u, int v) {
    adjv[u][deg[u]++] = v;
    adjv[v][deg[v]++] = u;
}

/* Bitset balls of radius r: bit w of out[v] set iff dist(v, w) <= r. */
static void balls(int r, uint64_t *out) {
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * nw);
    for (int v = 0; v < N; v++) cur[(size_t)v * nw + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * nw;
            const uint64_t *src = cur + (size_t)v * nw;
            memcpy(dst, src, sizeof(uint64_t) * nw);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s2 = cur + (size_t)adjv[v][k] * nw;
                for (int w = 0; w < nw; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    memcpy(out, cur, sizeof(uint64_t) * (size_t)N * nw);
}

/* Number of unordered pairs at distance more than DIAM (unreachable included). */
static long cost_of(void) {
    balls(DIAM, ballout);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        for (int w = 0; w < nw; w++)
            pc += __builtin_popcountll(ballout[(size_t)v * nw + w]);
        bad += N - pc;
    }
    return bad / 2;
}

static int side0(int *S) {
    int n = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0 && deg[v] > 0) S[n++] = v;
    return n;
}

static int bipartition(void) {
    for (int v = 0; v < N; v++) col[v] = -1;
    int *q = malloc(sizeof(int) * (N > 0 ? N : 1));
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adjv[u][k];
                if (col[v] == -1) { col[v] = 1 - col[u]; q[qt++] = v; }
                else if (col[v] == col[u]) { free(q); return 0; }
            }
        }
    }
    free(q);
    return 1;
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    int *A = malloc(sizeof(int) * (N + 1));
    int *B = malloc(sizeof(int) * (N + 1));
    int na = 0, nb = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < Dg) { if (col[v] == 0) A[na++] = v; else B[nb++] = v; }
    }
    size_t cap = (size_t)na * (size_t)nb;
    int *P = malloc(sizeof(int) * 2 * (cap + 1));
    size_t cnt = 0;
    for (int i = 0; i < na; i++)
        for (int j = 0; j < nb; j++)
            if (!has_edge(A[i], B[j])) { P[2 * cnt] = A[i]; P[2 * cnt + 1] = B[j]; cnt++; }
    for (size_t i = cnt; i > 1; i--) {
        size_t j = (size_t)(rnd() % (uint64_t)i);
        size_t x = i - 1;
        int ta = P[2 * x], tb = P[2 * x + 1];
        P[2 * x] = P[2 * j]; P[2 * x + 1] = P[2 * j + 1];
        P[2 * j] = ta; P[2 * j + 1] = tb;
    }
    for (size_t i = 0; i < cnt; i++) {
        int a = P[2 * i], b = P[2 * i + 1];
        if (deg[a] < Dg && deg[b] < Dg && !has_edge(a, b)) add_edge(a, b);
    }
    free(A); free(B); free(P);
}

/* Vertex insertion with greedy cover of the opposite side (stealing if saturated). */
static void add_vertex(void) {
    int s = rndint(2);
    int v = N++;
    nw = (N + 63) >> 6;
    col[v] = 1 - s;
    deg[v] = 0;
    balls(DIAM - 1, ballr);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(cov));
    for (int pick = 0; pick < Dg; pick++) {
        int best = -1;
        long bs = -1;
        for (int t = 0; t < N - 1; t++) {
            if (col[t] != s || has_edge(t, v)) continue;
            int gain = 0;
            for (int w = 0; w < nw; w++)
                gain += __builtin_popcountll(ballr[(size_t)t * nw + w] & ~cov[w]);
            long sc = (long)gain * 64 + (deg[t] < Dg ? 32 : 0) + rndint(32);
            if (sc > bs) { bs = sc; best = t; }
        }
        if (best < 0) break;
        if (deg[best] >= Dg) {
            int w = adjv[best][rndint(deg[best])];
            del_edge(best, w);
        }
        add_edge(best, v);
        for (int w = 0; w < nw; w++) cov[w] |= ballr[(size_t)best * nw + w];
    }
    fill();
}

/* One double-edge switch a-b, c-e -> a-e, c-b (a, c on side 0). Returns new cost. */
static long try_switch(const int *S0, int n0, long cur, double p1, double p2) {
    int a = S0[rndint(n0)];
    if (deg[a] == 0) return cur;
    int b = adjv[a][rndint(deg[a])];
    int c = S0[rndint(n0)];
    if (c == a || deg[c] == 0) return cur;
    int e = adjv[c][rndint(deg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return cur;
    del_edge(a, b); del_edge(c, e);
    add_edge(a, e); add_edge(c, b);
    long nc = cost_of();
    if (nc <= cur) return nc;
    double diff = (double)(nc - cur);
    double p = (diff == 1.0) ? p1 : (diff == 2.0 ? p2 : 0.0);
    if (rnd01() < p) return nc;
    del_edge(a, e); del_edge(c, b);
    add_edge(a, b); add_edge(c, e);
    return cur;
}

static long anneal(int iters, long cur) {
    int *S0 = malloc(sizeof(int) * (N > 0 ? N : 1));
    int n0 = side0(S0);
    for (int it = 0; it < iters && cur > 0 && n0 >= 2; it++)
        cur = try_switch(S0, n0, cur, 0.1, 0.02);
    free(S0);
    return cur;
}

/* Valid-only plateau walk: switches that keep cost 0. */
static void plateau(int steps) {
    int *S0 = malloc(sizeof(int) * (N > 0 ? N : 1));
    int n0 = side0(S0);
    if (n0 >= 2)
        for (int s = 0; s < steps; s++) try_switch(S0, n0, 0, 0.0, 0.0);
    free(S0);
}

/* Delete random edges while the diameter bound survives. */
static void prune(int tests) {
    int cap = N * Dg + 1;
    int *EU = malloc(sizeof(int) * cap);
    int *EV = malloc(sizeof(int) * cap);
    int m = 0;
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++) {
            int v = adjv[u][k];
            if (u < v && m < cap) { EU[m] = u; EV[m] = v; m++; }
        }
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tu = EU[i], tv = EV[i];
        EU[i] = EU[j]; EV[i] = EV[j];
        EU[j] = tu; EV[j] = tv;
    }
    int t = 0;
    for (int i = 0; i < m && t < tests; i++) {
        int u = EU[i], v = EV[i];
        if (!has_edge(u, v)) continue;
        t++;
        del_edge(u, v);
        if (cost_of() != 0) add_edge(u, v);
    }
    free(EU); free(EV);
}

static void snap(void) {
    snapN = N;
    memcpy(snapAdj, adjv, sizeof(adjv));
    memcpy(snapDeg, deg, sizeof(deg));
    memcpy(snapCol, col, sizeof(col));
}

static void restore_snap(void) {
    N = snapN;
    nw = (N + 63) >> 6;
    memcpy(adjv, snapAdj, sizeof(adjv));
    memcpy(deg, snapDeg, sizeof(deg));
    memcpy(col, snapCol, sizeof(col));
}

static void save_best(void) {
    bestN = N;
    memcpy(bestAdj, adjv, sizeof(adjv));
    memcpy(bestDeg, deg, sizeof(deg));
    memcpy(bestCol, col, sizeof(col));
}

static void load_best(void) {
    N = bestN;
    nw = (N + 63) >> 6;
    memcpy(adjv, bestAdj, sizeof(adjv));
    memcpy(deg, bestDeg, sizeof(deg));
    memcpy(col, bestCol, sizeof(col));
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed time\n"); return 1; }
    Dg = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double tl = atof(argv[4]);
    if (Dg < 1 || Dg > MAXD - 2 || DIAM < 2) { printf("0 0\n"); return 0; }

    bufA = malloc(sizeof(uint64_t) * MAXN * MAXW);
    bufB = malloc(sizeof(uint64_t) * MAXN * MAXW);
    ballout = malloc(sizeof(uint64_t) * MAXN * MAXW);
    ballr = malloc(sizeof(uint64_t) * MAXN * MAXW);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    N = 0;
    if (n0 == 0) {
        N = 2 * Dg;
        for (int i = 0; i < Dg; i++)
            for (int j = 0; j < Dg; j++) add_edge(i, Dg + j);
        for (int i = 0; i < N; i++) col[i] = (i < Dg) ? 0 : 1;
    } else {
        if (n0 > MAXN - 2) { printf("0 0\n"); return 0; }
        N = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
            if (deg[u] >= Dg || deg[v] >= Dg || has_edge(u, v)) continue;
            add_edge(u, v);
        }
        if (!bipartition()) { printf("0 0\n"); return 0; }
    }
    nw = (N + 63) >> 6;

    long cur = cost_of();
    if (cur != 0) cur = anneal(40000, cur);
    if (cur == 0) save_best();

    double t0 = cpu_now();
    if (bestN >= 0) {
        int fails = 0;
        while (cpu_now() - t0 < tl && N < MAXN - 2) {
            snap();
            add_vertex();
            long c = cost_of();
            c = anneal(ANNEAL_IT, c);
            if (c == 0) {
                prune(300);
                if (N > bestN) save_best();
                fails = 0;
            } else {
                restore_snap();
                fails++;
            }
            if (fails > 120) {
                load_best();
                plateau(300);
                fails = 0;
            }
        }
    }

    if (bestN < 0) { printf("0 0\n"); return 0; }
    load_best();
    int m = 0;
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++) if (adjv[u][k] > u) m++;
    printf("%d %d\n", N, m);
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (adjv[u][k] > u) printf("%d %d\n", u, adjv[u][k]);
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared Python helpers (growth by cover vertices, saturation, twins).
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


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    # Short randomized twin-duplication pipelines.
    if D >= 2:
        trial_end = start + 0.25 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Main improver: C insertion / repair / prune search from the best valid graph.
    if D >= 2:
        c_end = start + 0.88 * time_limit
        budget = c_end - time.monotonic()
        if budget > 2.0:
            remaining = start + time_limit - 1.5 - time.monotonic()
            timeout = max(1.0, min(budget + 3.0, remaining))
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget - 1.0:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=timeout)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
