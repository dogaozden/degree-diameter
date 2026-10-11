import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex insertion followed by annealed double-edge switches.
#
# Starting from a valid bipartite graph, the engine adds one vertex on a random
# side, joins it to d opposite-side vertices (stealing one edge from any full
# vertex), saturates spare degree with cross-side edges, and then runs simulated
# annealing over degree-preserving bipartite double-edge switches. The cost is
# the number of vertex pairs at distance > D, computed with bitset balls. A
# successful anneal keeps the larger graph as the new base. A failed anneal
# restores the base and retries with a longer budget. The best valid graph is
# printed when time runs out.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1024
#define WMAX 16
#define DMAX 16
#define EMAX (NMAX * DMAX)

static int d_, Dist, n;
static int color[NMAX], deg[NMAX], adjv[NMAX][DMAX];
static uint64_t bufA[NMAX][WMAX], bufB[NMAX][WMAX];
static uint64_t (*CUR)[WMAX] = bufA, (*NXT)[WMAX] = bufB;
static int W;
static clock_t T0clk;
static double TL;
static uint64_t rs = 88172645463325252ULL;

static int bestn = 0, bestm = 0;
static int bestE[EMAX][2];

static int S0[NMAX];
static int ns0 = 0;

typedef struct {
    int n;
    int deg[NMAX];
    int adj[NMAX][DMAX];
    int color[NMAX];
} Snap;
static Snap base;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0clk) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static int idx(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return i;
    return -1;
}

static void add_nb(int a, int b) { adjv[a][deg[a]++] = b; }

static void del_nb(int a, int b) {
    int k = idx(a, b);
    if (k < 0) return;
    adjv[a][k] = adjv[a][--deg[a]];
}

static void shuffle_int(int *x, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Number of unordered pairs at distance > Dist. */
static long long cost(void) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) CUR[v][w] = 0;
        CUR[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < Dist; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) NXT[v][w] = CUR[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adjv[v][i];
                for (int w = 0; w < W; w++) NXT[v][w] |= CUR[u][w];
            }
        }
        uint64_t (*t)[WMAX] = CUR;
        CUR = NXT;
        NXT = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(CUR[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Add cross-side edges between deficient vertices. Never increases the cost. */
static void fill(void) {
    static int L[NMAX], R[NMAX];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d_) {
            if (color[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d_; j++) {
            int b = R[j];
            if (deg[b] < d_ && !has(a, b)) {
                add_nb(a, b);
                add_nb(b, a);
            }
        }
    }
}

/* Insert one vertex on a random side; steal one edge from each full chosen neighbour. */
static int add_vertex(void) {
    static int cand[NMAX], chosen[DMAX];
    int side = rndint(2);
    int v = n++;
    color[v] = side;
    deg[v] = 0;
    int nc = 0;
    for (int u = 0; u < v; u++)
        if (color[u] != side) cand[nc++] = u;
    shuffle_int(cand, nc);
    int k = 0;
    for (int i = 0; i < nc && k < d_; i++) {
        int u = cand[i];
        if (deg[u] < d_) chosen[k++] = u;
    }
    for (int i = 0; i < nc && k < d_; i++) {
        int u = cand[i];
        if (deg[u] >= d_) {
            int j = rndint(deg[u]);
            int w = adjv[u][j];
            del_nb(u, w);
            del_nb(w, u);
            chosen[k++] = u;
        }
    }
    for (int i = 0; i < k; i++) {
        add_nb(v, chosen[i]);
        add_nb(chosen[i], v);
    }
    return v;
}

static void take(Snap *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(deg));
    memcpy(s->adj, adjv, sizeof(adjv));
    memcpy(s->color, color, sizeof(color));
}

static void restore(const Snap *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(deg));
    memcpy(adjv, s->adj, sizeof(adjv));
    memcpy(color, s->color, sizeof(color));
}

static void save_best(void) {
    if (n <= bestn) return;
    bestn = n;
    bestm = 0;
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adjv[v][i];
            if (v < u && bestm < EMAX) {
                bestE[bestm][0] = v;
                bestE[bestm][1] = u;
                bestm++;
            }
        }
    }
}

/* Degree-preserving bipartite double-edge switch with Metropolis acceptance. */
static int try_switch(long long *cur, double T) {
    if (ns0 < 2) return 0;
    int a = S0[rndint(ns0)];
    if (deg[a] == 0) return 0;
    int i = rndint(deg[a]);
    int b = adjv[a][i];
    int c = S0[rndint(ns0)];
    if (c == a || deg[c] == 0) return 0;
    int j = rndint(deg[c]);
    int e = adjv[c][j];
    if (has(a, e) || has(c, b)) return 0;
    adjv[a][i] = e;
    adjv[e][idx(e, c)] = a;
    adjv[c][j] = b;
    adjv[b][idx(b, a)] = c;
    long long nc = cost();
    if (nc <= *cur || rnd01() < exp(-(double)(nc - *cur) / T)) {
        *cur = nc;
        return 1;
    }
    adjv[a][i] = b;
    adjv[b][idx(b, c)] = a;
    adjv[c][j] = e;
    adjv[e][idx(e, a)] = c;
    return 0;
}

static int anneal(long long iters, double Ta, double Tb) {
    ns0 = 0;
    for (int v = 0; v < n; v++)
        if (color[v] == 0 && deg[v] > 0) S0[ns0++] = v;
    long long cur = cost();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > TL) break;
        double T = Ta * pow(Tb / Ta, (double)it / (double)iters);
        try_switch(&cur, T);
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    T0clk = clock();
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    Dist = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    TL = atof(argv[4]);
    if (Dist < 1) Dist = 1;
    if (d_ < 1 || d_ > DMAX - 1) {
        printf("0 0\n");
        return 0;
    }
    int nin = 0, mm = 0;
    if (scanf("%d %d", &nin, &mm) != 2 || nin < 1 || nin > NMAX - 64 || mm < 0) {
        printf("0 0\n");
        return 0;
    }
    n = nin;
    memset(deg, 0, sizeof(deg));
    memset(adjv, 0, sizeof(adjv));
    for (int k = 0; k < mm; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || deg[u] >= d_ || deg[v] >= d_ || has(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_nb(u, v);
        add_nb(v, u);
    }
    /* Bipartition by BFS. */
    static int q[NMAX];
    for (int v = 0; v < n; v++) color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (color[s] >= 0) continue;
        color[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjv[u][i];
                if (color[w] < 0) {
                    color[w] = 1 - color[u];
                    q[qt++] = w;
                } else if (color[w] == color[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    fill();
    long long c0 = cost();
    if (c0 != 0) {
        if (anneal(400000, 2.0, 0.08)) save_best();
        else {
            printf("0 0\n");
            return 0;
        }
    } else {
        save_best();
    }
    take(&base);

    long long iters = 20000;
    while (elapsed() < TL && n < NMAX - 2) {
        add_vertex();
        fill();
        if (anneal(iters, 2.0, 0.08)) {
            save_best();
            take(&base);
            iters = 20000;
        } else {
            restore(&base);
            if (iters < 300000) iters = iters + iters / 4;
        }
    }

    printf("%d %d\n", bestn, bestm);
    for (int k = 0; k < bestm; k++) printf("%d %d\n", bestE[k][0], bestE[k][1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Algebraic constructions.
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
# Group-lift search.
#
# A bipartite base with kb vertices per side and degree d is lifted over a
# finite group G = Z_m x| Z_k. Left translation by G is an automorphism of the
# lift, so the diameter test only needs one BFS per base vertex.
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All (m, k, r) with m*k = G giving a semidirect product Z_m x| Z_k."""
    out = []
    for m in range(1, G + 1):
        if G % m:
            continue
        k = G // m
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _lift_cost(kb, G, T, d, D, tgt, lab):
    """Sum over base vertices of unreached lifted vertices within distance D of (u, identity)."""
    n = 2 * kb * G
    nbr = [[] for _ in range(n)]
    for t in range(d):
        tt = tgt[t]
        lt = lab[t]
        for i in range(kb):
            j = kb + tt[i]
            g = lt[i]
            for x in range(G):
                a = i * G + x
                b = j * G + T[x][g]
                nbr[a].append(b)
                nbr[b].append(a)
    total = 0
    for u in range(2 * kb):
        s = u * G
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for w in nbr[v]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _lift_search(kb, G, T, d, D, deadline, rng):
    """Anneal dart labels and slot permutations until the lift has diameter <= D. Returns (n, edges) or None."""
    n = 2 * kb * G
    tgt = []
    lab = []
    for _ in range(d):
        p = list(range(kb))
        rng.shuffle(p)
        tgt.append(p)
        lab.append([rng.randrange(G) for _ in range(kb)])
    cur = _lift_cost(kb, G, T, d, D, tgt, lab)
    temp = 2.0
    while cur > 0 and time.monotonic() < deadline:
        if kb >= 2 and rng.random() < 0.3:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(kb), 2)
            tt = tgt[t]
            tt[i1], tt[i2] = tt[i2], tt[i1]
            c = _lift_cost(kb, G, T, d, D, tgt, lab)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                tt[i1], tt[i2] = tt[i2], tt[i1]
        else:
            t = rng.randrange(d)
            i = rng.randrange(kb)
            old = lab[t][i]
            new = rng.randrange(G)
            if new == old:
                continue
            lab[t][i] = new
            c = _lift_cost(kb, G, T, d, D, tgt, lab)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                lab[t][i] = old
    if cur != 0:
        return None
    edges = set()
    for t in range(d):
        for i in range(kb):
            j = kb + tgt[t][i]
            g = lab[t][i]
            for x in range(G):
                edges.add((i * G + x, j * G + T[x][g]))
    return n, sorted(edges)


def _lift_stage(d, D, rng, deadline, floor_n, limit_n):
    """Ladder over lift sizes above floor_n. Returns the largest valid lift found, or None."""
    cands = []
    for kb in range(1, 7):
        lo = floor_n // (2 * kb) + 1
        hi = limit_n // (2 * kb)
        for G in range(lo, hi + 1):
            n = 2 * kb * G
            if floor_n < n <= limit_n:
                cands.append((n, kb, G))
    cands.sort()
    best = None
    best_n = floor_n
    for n, kb, G in cands:
        if n <= best_n:
            continue
        if time.monotonic() >= deadline:
            break
        groups = _groups_of_order(G)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        slice_end = min(deadline, time.monotonic() + 4.0)
        res = _lift_search(kb, G, T, d, D, slice_end, rng)
        if res is not None:
            cn, ce = res
            if cn > best_n and lib.is_valid(cn, ce, d, D):
                best_n = cn
                best = (cn, ce)
    return best


# ----------------------------------------------------------------------------
# Python pipeline (constructions plus Python search).
# ----------------------------------------------------------------------------

def _parent_build(d, D, seed, time_limit):
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

    if D >= 2:
        trial_end = start + 0.3 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.75 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


def _c_anneal(d, D, seed, graph, budget):
    """Run the C insertion-and-anneal engine from a valid graph. Returns (n, edges) or None."""
    n, e = graph
    if n < 2 or n > 900 or d > 15 or D < 2 or budget < 1.0:
        return None
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(n, e), timeout=budget + 8.0)
    cn, ce = lib.parse_graph_text(out)
    if cn > 0 and lib.is_valid(cn, ce, d, D):
        return cn, ce
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def keep(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Stage 1: parent constructions and search.
    try:
        frac = 0.35 if (D >= 4 and d >= 3 and time_limit >= 10) else 0.6
        n1, e1 = _parent_build(d, D, seed, frac * time_limit)
        keep(n1, e1)
    except Exception:
        pass

    # Stage 2: group lifts above the current best (large cases only).
    if D >= 4 and d >= 3 and time_limit >= 10:
        try:
            rng = random.Random(seed * 7919 + 1)
            limit_n = min(lib.moore_bound(d, D), 900)
            res = _lift_stage(d, D, rng, start + 0.45 * time_limit, best_n, limit_n)
            if res is not None:
                keep(res[0], res[1])
        except Exception:
            pass

    # Stage 3: C insertion-and-anneal from the best valid graph found so far.
    budget = start + 0.85 * time_limit - time.monotonic() - 1.0
    if budget >= 2.0:
        try:
            res = _c_anneal(d, D, seed, (best_n, best_e), budget)
            if res is not None:
                keep(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
