import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: grows a valid bipartite graph by adding one vertex at a time
# and repairing the diameter with degree-preserving double-edge switches
# (simulated annealing on the number of pairs farther apart than D).
# A failed repair restores the last valid snapshot, so the output is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define NMAX 1100
#define WMAX 18
#define DMAX 64
#define EMAX (NMAX * DMAX / 2 + 8)

static int n, dd, DD, W;
static int deg[NMAX];
static int nb[NMAX][DMAX];
static unsigned char A[NMAX][NMAX];
static int col[NMAX];
static uint64_t B1[NMAX][WMAX], B2[NMAX][WMAX];
static uint64_t (*cur)[WMAX];

static int snapN, snapM;
static int snapU[EMAX], snapV[EMAX], snapCol[NMAX];

static uint64_t rs = 88172645463325252ULL;
static clock_t T0;
static double TL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC > TL; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    A[u][v] = A[v][u] = 1;
}

static void rem_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; return; }
}

static void del_edge(int u, int v) {
    rem_from(u, v);
    rem_from(v, u);
    A[u][v] = A[v][u] = 0;
}

/* Bitsets of all vertices within distance r; result in cur. */
static void balls(int r) {
    uint64_t (*p)[WMAX] = B1, (*q)[WMAX] = B2, (*t)[WMAX];
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(p[v], 0, sizeof(uint64_t) * W);
        p[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) q[v][w] = p[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) q[v][w] |= p[u][w];
            }
        }
        t = p; p = q; q = t;
    }
    cur = p;
}

/* Number of unordered pairs at distance more than DD. */
static long cost(void) {
    balls(DD);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    static int L[NMAX], R[NMAX];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < dd) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < dd; j++) {
            int b = R[j];
            if (deg[b] < dd && !A[a][b]) add_edge(a, b);
        }
    }
}

/* One degree-preserving bipartite double-edge switch, kept if cost does not grow much. */
static void switch_try(const int *S0, int ns0, long *cc) {
    if (ns0 < 2) return;
    int a = S0[rndint(ns0)];
    if (deg[a] == 0) return;
    int b = nb[a][rndint(deg[a])];
    int c = S0[rndint(ns0)];
    if (c == a || deg[c] == 0) return;
    int e = nb[c][rndint(deg[c])];
    if (A[a][e] || A[c][b]) return;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    long nw = cost();
    if (nw <= *cc || (nw == *cc + 1 && rndu() < 0.08)) {
        *cc = nw;
        return;
    }
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

static int anneal(long *cc, long iters) {
    static int S0[NMAX];
    int ns0 = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) S0[ns0++] = v;
    for (long it = 0; it < iters && *cc > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        switch_try(S0, ns0, cc);
    }
    return *cc == 0;
}

/* Add a vertex joined to a greedy cover of the opposite side; evict edges if needed. */
static int add_vertex(void) {
    if (n + 1 >= NMAX) return 0;
    int nc = rndint(2);
    int side = 1 - nc;
    balls(DD - 1);
    uint64_t U[WMAX];
    memset(U, 0, sizeof U);
    for (int x = 0; x < n; x++) U[x >> 6] |= 1ULL << (x & 63);
    int chosen[DMAX];
    int nch = 0;
    for (int k = 0; k < dd; k++) {
        int best = -1, bg = -1, ties = 0;
        for (int s = 0; s < n; s++) {
            if (col[s] != side) continue;
            int used = 0;
            for (int i = 0; i < nch; i++) if (chosen[i] == s) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(cur[s][w] & U[w]);
            if (g > bg) { bg = g; best = s; ties = 1; }
            else if (g == bg) { ties++; if (rndint(ties) == 0) best = s; }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) U[w] &= ~cur[best][w];
    }
    int v = n;
    n++;
    col[v] = nc;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (deg[s] >= dd) {
            int t = nb[s][rndint(deg[s])];
            del_edge(s, t);
        }
        add_edge(v, s);
    }
    return 1;
}

static void snap_save(void) {
    snapN = n;
    snapM = 0;
    for (int u = 0; u < n; u++) {
        snapCol[u] = col[u];
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (u < v && snapM < EMAX) {
                snapU[snapM] = u;
                snapV[snapM] = v;
                snapM++;
            }
        }
    }
}

static void snap_restore(void) {
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++) A[u][nb[u][i]] = 0;
    for (int u = 0; u < n; u++) deg[u] = 0;
    n = snapN;
    for (int u = 0; u < n; u++) col[u] = snapCol[u];
    for (int i = 0; i < snapM; i++) add_edge(snapU[i], snapV[i]);
}

static int read_graph(void) {
    int m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n >= NMAX - 1) return 0;
    for (int u = 0; u < n; u++) {
        deg[u] = 0;
        memset(A[u], 0, (size_t)n);
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (A[u][v]) continue;
        if (deg[u] >= dd || deg[v] >= dd) continue;
        add_edge(u, v);
    }
    static int stk[NMAX];
    for (int u = 0; u < n; u++) col[u] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= 0x9E3779B97F4A7C15ULL * ((uint64_t)atoll(argv[3]) + 1);
    if (rs == 0) rs = 1;
    TL = atof(argv[4]);
    T0 = clock();
    if (dd < 1 || dd >= DMAX || DD < 2 || !read_graph()) { printf("0 0\n"); return 0; }
    fill();
    long c = cost();
    if (c > 0) anneal(&c, 20000);
    if (c > 0) { printf("0 0\n"); return 0; }
    snap_save();
    while (!timeup()) {
        if (!add_vertex()) break;
        fill();
        long cc = cost();
        if (anneal(&cc, 2500)) snap_save();
        else snap_restore();
    }
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (structured bases and Python-side growth).
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
#
# Delete 1-3 vertices from a valid graph. Their neighbours regain spare degree,
# but distances may grow. Repair the diameter with bipartite double-edge
# switches (degrees preserved), then regrow with cover vertices and saturation.
# Cover growth keeps the diameter bound, so every accepted state stays valid.
# The walk is anchored: if it drifts too far below its best graph, it returns
# to that best graph instead of wandering off the plateau.
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
    """Python pipeline: structured base, twin/cover growth, LNS and repair. Returns (n, edges)."""
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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
        trial_end = start + 0.3 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Kill-repair-regrow search from the best valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.75 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # Bold stage: repeated add-and-repair from the largest valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Stage 1: Python constructions and searches (about half the budget).
    n0, e0 = _python_build(d, D, seed, 0.5 * time_limit)
    if not lib.is_valid(n0, e0, d, D):
        n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, list(e0))

    # Stage 2: C annealing growth from the best graph found so far.
    if D >= 2 and 2 <= d < 60:
        budget = 0.8 * time_limit - (time.monotonic() - start) - 1.0
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=budget + 8.0)
                n1, e1 = lib.parse_graph_text(out)
                if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                    best = (n1, list(e1))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0], list(best[1])
