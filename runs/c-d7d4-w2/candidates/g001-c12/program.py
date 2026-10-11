import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: monotone add-and-repair with bipartite double-edge switches.
#
# Each round adds one vertex on alternating sides, joins it to the opposite side
# (stealing a neighbour edge when a partner is full), saturates spare degree, then
# anneals with degree-preserving switches to drive the count of pairs at distance
# > D to zero. A round is kept only if the graph is valid again, so the state is
# always a valid graph. The best graph is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3000
#define MAXD 64
#define MAXW 48
#define SNAPMAX (MAXN * MAXD / 2 + 8)
#define ANN_ITERS 1500

static int Dg, Dist, n;
static int color[MAXN];
static int deg[MAXN];
static int adjl[MAXN][MAXD];
static unsigned char Am[MAXN][MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static double t_budget = 0.0;
static clock_t t0;
static int snapN, snapEc;
static int snapU[SNAPMAX], snapV[SNAPMAX];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC >= t_budget; }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }
static int has(int u, int v) { return Am[u][v]; }

static void remove_nb(int x, int y) {
    for (int i = 0; i < deg[x]; i++) {
        if (adjl[x][i] == y) {
            adjl[x][i] = adjl[x][--deg[x]];
            return;
        }
    }
}

static void add_e(int u, int v) {
    adjl[u][deg[u]++] = v;
    adjl[v][deg[v]++] = u;
    Am[u][v] = 1;
    Am[v][u] = 1;
}

static void del_e(int u, int v) {
    remove_nb(u, v);
    remove_nb(v, u);
    Am[u][v] = 0;
    Am[v][u] = 0;
}

/* Number of unordered pairs at distance > Dist (unreachable counts). */
static int cost(void) {
    int W = (n + 63) / 64;
    uint64_t *A = bufA, *B = bufB;
    memset(A, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) A[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < Dist; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *bv = B + (size_t)v * W;
            memcpy(bv, A + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *bu = A + (size_t)adjl[v][i] * W;
                for (int w = 0; w < W; w++) bv[w] |= bu[w];
            }
        }
        uint64_t *t = A;
        A = B;
        B = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(A[(size_t)v * W + w]);
        total += n - pc;
    }
    return (int)(total / 2);
}

static void shuffle_int(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Join deficient opposite-colour vertices (only shortens distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < Dg) {
            if (color[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        for (int j = 0; j < nr; j++) {
            int a = L[i], b = R[j];
            if (deg[a] < Dg && deg[b] < Dg && !has(a, b)) add_e(a, b);
        }
    }
}

/* Append a vertex of colour col joined to up to Dg vertices of the other colour. */
static int add_vertex(int col) {
    if (n >= MAXN - 1) return -1;
    int v = n, X = 1 - col;
    for (int u = 0; u < n; u++) {
        Am[u][v] = 0;
        Am[v][u] = 0;
    }
    Am[v][v] = 0;
    deg[v] = 0;
    color[v] = col;
    n++;
    int joined = 0;
    for (int tries = 0; joined < Dg && tries < 60 * Dg + 200; tries++) {
        int s = rndi(v);
        if (color[s] != X || has(s, v)) continue;
        if (deg[s] >= Dg) {
            if (deg[s] == 0) continue;
            int t = adjl[s][rndi(deg[s])];
            del_e(s, t);
        }
        add_e(s, v);
        joined++;
    }
    return v;
}

static void take_snapshot(void) {
    snapN = n;
    snapEc = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int w = adjl[u][i];
            if (u < w && snapEc < SNAPMAX) {
                snapU[snapEc] = u;
                snapV[snapEc] = w;
                snapEc++;
            }
        }
    }
}

static void load_snapshot(void) {
    int m = n;
    for (int u = 0; u < m; u++) {
        memset(Am[u], 0, (size_t)m);
        deg[u] = 0;
    }
    n = snapN;
    for (int i = 0; i < snapEc; i++) add_e(snapU[i], snapV[i]);
}

/* Degree-preserving bipartite double-edge switches minimising cost. Returns final cost. */
static int anneal(int iters) {
    static int s0[MAXN];
    int cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && timeup()) break;
        int k = 0;
        for (int v = 0; v < n; v++)
            if (color[v] == 0 && deg[v] > 0) s0[k++] = v;
        if (k < 2) break;
        int a = s0[rndi(k)];
        int c = s0[rndi(k)];
        if (a == c) continue;
        int b = adjl[a][rndi(deg[a])];
        int e = adjl[c][rndi(deg[c])];
        if (has(a, e) || has(c, b)) continue;
        del_e(a, b);
        del_e(c, e);
        add_e(a, e);
        add_e(c, b);
        int nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd01() < 0.05)) {
            cur = nw;
        } else {
            del_e(a, e);
            del_e(c, b);
            add_e(a, b);
            add_e(c, e);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    Dg = atoi(argv[1]);
    Dist = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 88172645463325252ULL;
    t_budget = atof(argv[4]);
    t0 = clock();

    int nin = 0, mi = 0;
    if (scanf("%d %d", &nin, &mi) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (Dg < 2 || Dg > MAXD || Dist < 2 || nin < 2 || nin > MAXN - 200 || mi < 0) {
        printf("0 0\n");
        return 0;
    }
    n = nin;
    int bad = 0;
    for (int i = 0; i < mi; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            bad = 1;
            break;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            deg[u] >= Dg || deg[v] >= Dg || has(u, v)) {
            bad = 1;
            break;
        }
        add_e(u, v);
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    for (int v = 0; v < n; v++) color[v] = -1;
    static int q[MAXN];
    for (int s = 0; s < n && !bad; s++) {
        if (color[s] >= 0) continue;
        color[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int x = q[qh++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adjl[x][i];
                if (color[y] < 0) {
                    color[y] = 1 - color[x];
                    q[qt++] = y;
                } else if (color[y] == color[x]) {
                    bad = 1;
                }
            }
        }
    }
    if (bad || cost() != 0) {
        printf("0 0\n");
        return 0;
    }

    fill();
    int col = 0;
    while (!timeup()) {
        take_snapshot();
        int v = add_vertex(col);
        if (v < 0) break;
        col ^= 1;
        fill();
        if (anneal(ANN_ITERS) != 0) load_snapshot();
    }

    int ec = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (u < adjl[u][i]) ec++;
    printf("%d %d\n", n, ec);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (u < adjl[u][i]) printf("%d %d\n", u, adjl[u][i]);
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices.

    `attempts` bounds the randomized cover retries per growth step.
    """
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
# Random voltage lifts with repair.
#
# Base graph: k vertices on side A and k on side B, joined by d darts forming
# a d-regular bipartite multigraph (d random perfect matchings between the two
# sides). Each dart carries a random voltage in Z_m. The lift has 2*k*m vertices
# and degree <= d, is bipartite by construction, and is the search space for
# order > current best. If the lift has bad pairs, double-edge switches
# (degree-preserving) repair it before growing with cover vertices.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
#
# Delete 1-3 vertices from a valid graph. Their neighbours regain spare degree,
# but distances may grow. Repair the diameter with bipartite double-edge
# switches (degrees preserved), then regrow with cover vertices and saturation.
# Cover growth keeps the diameter bound, so every accepted state stays valid.
# The walk is anchored: if it drifts too far below its best graph, it returns
# to that best graph instead of wandering off the plateau.
# ----------------------------------------------------------------------------

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
        # Accept sideways and slightly downward moves to drift across the plateau.
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            # Drifted too far below the best graph: return to it.
            cur_n, cur_e = best_n, list(best_e)


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

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.2 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Random voltage lifts of small bipartite base multigraphs, repaired and grown.
    if D >= 2:
        lift_end = start + 0.3 * time_limit
        _lift_search(d, D, lift_end, rng, best_n, consider)

    # Kill-repair-regrow search from the best valid graph found so far.
    if D >= 2:
        lns_end = start + 0.4 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # C stage: fast monotone add-and-repair from the best valid graph, using the
    # remaining budget. Any failure or bad output leaves the Python best in place.
    if D >= 2 and d <= 63 and best_n >= 2:
        budget = (start + 0.85 * time_limit) - time.monotonic() - 1.5
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 6.0)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
