import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex insertion with annealed repair and plateau diffusion.
#
# The state is a valid bipartite graph with max degree d and diameter <= D.
# Each attempt copies the best valid graph, optionally diffuses it across the
# plateau of valid graphs of the same order (only cost-0 moves accepted), adds
# one vertex whose neighbours are chosen greedily by ball coverage, fills spare
# degree, and anneals double-edge switches to minimise bad pairs. Cost 0 means
# a valid graph with one more vertex; it becomes the new best.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 64
#define MAXW (MAXN / 64)
#define ITERS 2000

typedef uint64_t u64;
typedef u64 Row[MAXW];

static int d_, D_;
static int n_;
static int adj_[MAXN][MAXDEG];
static int deg_[MAXN];
static int col_[MAXN];

static int bestn_;
static int bestadj_[MAXN][MAXDEG];
static int bestdeg_[MAXN];
static int bestcol_[MAXN];

static Row bufA_[MAXN];
static Row bufB_[MAXN];

static u64 rng_s = 88172645463325252ULL;
static double t_start;
static double tlim_;

static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static double elapsed(void) { return wall() - t_start; }

static u64 rnd(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}

static int rndint(int k) { return (int)(rnd() % (u64)k); }

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg_[a]; i++)
        if (adj_[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}

static void del_from(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (adj_[a][i] == b) {
            adj_[a][i] = adj_[a][--deg_[a]];
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
}

/* Ball of radius r around every vertex, as bitsets. Result is overwritten by the next call. */
static Row *balls(int r) {
    int n = n_;
    int W = (n + 63) >> 6;
    Row *cur = bufA_, *nxt = bufB_;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg_[v]; i++) {
                const u64 *src = cur[adj_[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        Row *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance more than D_ (unreachable pairs included). */
static int bad_pairs(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    Row *b = balls(D_);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(b[v][w]);
        total += n - c;
    }
    return (int)(total / 2);
}

/* Append a vertex of colour nc, joined to a greedy cover of the other colour. */
static void add_vertex(int nc) {
    int v = n_++;
    col_[v] = nc;
    deg_[v] = 0;
    int want = 1 - nc;
    int W = (n_ + 63) >> 6;
    Row *b = balls(D_ - 1);
    u64 cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXDEG];
    int nch = 0;
    for (int pass = 0; pass < 2 && nch < d_; pass++) {
        while (nch < d_) {
            int bs = -1;
            double bg = -1e18;
            for (int s = 0; s < v; s++) {
                if (col_[s] != want) continue;
                if (pass == 0 && deg_[s] >= d_) continue;
                int used = 0;
                for (int i = 0; i < nch; i++)
                    if (chosen[i] == s) { used = 1; break; }
                if (used) continue;
                int g = 0;
                for (int w = 0; w < W; w++) g += pc64(b[s][w] & ~cov[w]);
                double sc = g + 0.5 * rnd01();
                if (sc > bg) { bg = sc; bs = s; }
            }
            if (bs < 0) break;
            chosen[nch++] = bs;
            for (int w = 0; w < W; w++) cov[w] |= b[bs][w];
        }
    }
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (deg_[s] >= d_) {
            int t = adj_[s][rndint(deg_[s])];
            remove_edge(s, t);
        }
        add_edge(s, v);
    }
}

/* Add cross-colour edges between deficient vertices. Never increases any distance. */
static void fill_edges(void) {
    int n = n_;
    if (n <= 0) return;
    int oa = rndint(n), ob = rndint(n);
    for (int ja = 0; ja < n; ja++) {
        int a = (oa + ja) % n;
        if (col_[a] != 0 || deg_[a] >= d_) continue;
        for (int jb = 0; jb < n && deg_[a] < d_; jb++) {
            int b = (ob + jb) % n;
            if (col_[b] != 1 || deg_[b] >= d_) continue;
            if (has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

/*
 * One random double-edge switch a-b, c-e -> a-e, c-b (a, c colour 0; b, e colour 1).
 * Accepted if the new cost is <= cur, or with Metropolis probability when T > 0.
 * Returns the cost of the resulting state.
 */
static int step(int cur, double T) {
    int a = rndint(n_);
    if (col_[a] != 0 || deg_[a] == 0) return cur;
    int c = rndint(n_);
    if (col_[c] != 0 || deg_[c] == 0 || c == a) return cur;
    int b = adj_[a][rndint(deg_[a])];
    int e = adj_[c][rndint(deg_[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return cur;
    remove_edge(a, b);
    remove_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    int nw = bad_pairs();
    int delta = nw - cur;
    if (delta <= 0 || (T > 0.0 && rnd01() < exp(-(double)delta / T))) return nw;
    remove_edge(a, e);
    remove_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
    return cur;
}

static int anneal(int iters, double T0, double T1) {
    int cur = bad_pairs();
    for (int it = 0; it < iters && cur > 0; it++) {
        if (elapsed() > tlim_) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        cur = step(cur, T);
    }
    return cur;
}

/* Diffuse across the plateau of valid graphs: only cost-0 switches accepted. */
static void plateau_walk(int steps) {
    for (int it = 0; it < steps; it++) step(0, 0.0);
}

static void save_best(void) {
    bestn_ = n_;
    memcpy(bestadj_, adj_, sizeof(adj_));
    memcpy(bestdeg_, deg_, sizeof(deg_));
    memcpy(bestcol_, col_, sizeof(col_));
}

static void restore_best(void) {
    n_ = bestn_;
    memcpy(adj_, bestadj_, sizeof(adj_));
    memcpy(deg_, bestdeg_, sizeof(deg_));
    memcpy(col_, bestcol_, sizeof(col_));
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    t_start = wall();
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    tlim_ = atof(argv[4]);
    rng_s = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rng_s == 0) rng_s = 1;
    for (int i = 0; i < 4; i++) rnd();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > MAXN ||
        d_ < 1 || d_ >= MAXDEG || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    n_ = n0;
    for (int v = 0; v < n0; v++) deg_[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* Two-colour the graph by BFS. */
    for (int v = 0; v < n0; v++) col_[v] = -1;
    static int q[MAXN];
    for (int s = 0; s < n0; s++) {
        if (col_[s] != -1) continue;
        col_[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int i = 0; i < deg_[x]; i++) {
                int y = adj_[x][i];
                if (col_[y] == -1) {
                    col_[y] = 1 - col_[x];
                    q[t++] = y;
                }
            }
        }
    }

    if (bad_pairs() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    int fails = 0;
    while (elapsed() < tlim_) {
        restore_best();
        if (n_ + 1 >= MAXN) break;
        if (fails > 0 && rndint(2) == 0) plateau_walk(10 + rndint(40));
        add_vertex(rndint(2));
        fill_edges();
        int c = anneal(ITERS, 1.5, 0.05);
        if (c == 0) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }

    int bn = bestn_, m = 0;
    for (int v = 0; v < bn; v++)
        for (int i = 0; i < bestdeg_[v]; i++)
            if (bestadj_[v][i] > v) m++;
    printf("%d %d\n", bn, m);
    for (int v = 0; v < bn; v++)
        for (int i = 0; i < bestdeg_[v]; i++)
            if (bestadj_[v][i] > v) printf("%d %d\n", v, bestadj_[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
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
# Twin duplication: non-adjacent twins keep distances, so the diameter holds.
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
# Python fallback (used only if the C engine cannot run): kill-repair-regrow.
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


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
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

    moore = lib.moore_bound(d, D)

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
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    # Calibration cases already at the Moore bound return at once.
    if best_n >= moore:
        return best_n, list(best_e)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.25 * time_limit
        while time.monotonic() < trial_end and best_n < moore:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C engine: vertex insertion with annealed repair and plateau diffusion.
    c_ok = False
    if D >= 2 and best_n < moore and best_n <= 1000:
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            budget = 0.9 * remaining
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=remaining + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
                c_ok = True
            except Exception:
                c_ok = False

    # Python fallback if the C engine could not run.
    if D >= 2 and not c_ok and time.monotonic() < deadline - 1.0 and best_n < moore:
        _lns(best_n, best_e, d, D, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
