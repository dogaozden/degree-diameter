import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# New in this version: C engine "cover-grow + degree-preserving anneal".
#
# The C program starts from the best valid graph found by Python. Each round it
# (1) saves the state, (2) optionally shakes it with random degree-preserving
# bipartite switches, (3) adds one vertex on a random side whose neighbours are
# a greedy cover of the other side's (D-1)-balls, (4) fills spare degree with
# cross edges, and (5) anneals with double-edge switches (degrees fixed) until
# the bad-pair count is zero. Success keeps the bigger graph; failure restores.
# Every stored graph is valid, and the output is checked again in Python.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXDEG 64
#define MAXW 64
#define ANNEAL_CAP 500

static int N = 0, DMAX = 3, DIAM = 2;
static int nadj[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static int dist_[MAXN];
static int que[MAXN];
static int side_buf[MAXN];
static uint64_t ballb[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int sN = 0, bN = 0;
static int snadj[MAXN], bnadj[MAXN], scol[MAXN], dummy_col[MAXN];
static int sadj[MAXN][MAXDEG], badj[MAXN][MAXDEG];

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int has_edge(int u, int v) {
    for (int k = 0; k < nadj[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void rm_arc(int u, int v) {
    for (int k = 0; k < nadj[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--nadj[u]];
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adj[u][nadj[u]++] = v;
    adj[v][nadj[v]++] = u;
}

static void del_edge(int u, int v) {
    rm_arc(u, v);
    rm_arc(v, u);
}

/* BFS from s up to depth R; fills que[0..t) and dist_; returns t. */
static int bfs_limit(int s, int R) {
    for (int i = 0; i < N; i++) dist_[i] = -1;
    int h = 0, t = 0;
    que[t++] = s;
    dist_[s] = 0;
    while (h < t) {
        int u = que[h++];
        if (dist_[u] >= R) continue;
        for (int k = 0; k < nadj[u]; k++) {
            int x = adj[u][k];
            if (dist_[x] < 0) {
                dist_[x] = dist_[u] + 1;
                que[t++] = x;
            }
        }
    }
    return t;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static long long cost(void) {
    long long bad = 0;
    for (int s = 0; s < N; s++) bad += N - bfs_limit(s, DIAM);
    return bad / 2;
}

/* ballb[s] = all vertices within distance DIAM-1 of s. */
static void compute_balls(void) {
    int W = (N + 63) / 64;
    int R = DIAM - 1;
    for (int s = 0; s < N; s++) {
        for (int w = 0; w < W; w++) ballb[s][w] = 0;
        int t = bfs_limit(s, R);
        for (int i = 0; i < t; i++) {
            int x = que[i];
            ballb[s][x >> 6] |= 1ULL << (x & 63);
        }
    }
}

static void save_state(void) {
    sN = N;
    for (int v = 0; v < N; v++) {
        snadj[v] = nadj[v];
        scol[v] = col[v];
        memcpy(sadj[v], adj[v], sizeof(adj[v]));
    }
}

static void restore_state(void) {
    N = sN;
    for (int v = 0; v < N; v++) {
        nadj[v] = snadj[v];
        col[v] = scol[v];
        memcpy(adj[v], sadj[v], sizeof(adj[v]));
    }
}

static void save_best(void) {
    bN = N;
    for (int v = 0; v < N; v++) {
        bnadj[v] = nadj[v];
        memcpy(badj[v], adj[v], sizeof(adj[v]));
    }
}

/* Pick a degree-preserving bipartite switch a-b, c-e -> a-e, c-b (a, c on side 0). */
static int pick_switch(int *pa, int *pb, int *pc, int *pe) {
    int ns = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == 0 && nadj[v] > 0) side_buf[ns++] = v;
    if (ns < 2) return 0;
    int a = side_buf[rndi(ns)];
    int c = side_buf[rndi(ns)];
    if (a == c) return 0;
    int b = adj[a][rndi(nadj[a])];
    int e = adj[c][rndi(nadj[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    *pa = a;
    *pb = b;
    *pc = c;
    *pe = e;
    return 1;
}

static void apply_switch(int a, int b, int c, int e) {
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static void undo_switch(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Anneal with switches until cost 0. Returns 1 on success. */
static int anneal(int cap, double deadline) {
    long long cur = cost();
    for (int it = 0; it < cap && cur > 0; it++) {
        if (now() > deadline) break;
        int a, b, c, e;
        if (!pick_switch(&a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        long long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndi(100) < 5)) {
            cur = nw;
        } else {
            undo_switch(a, b, c, e);
        }
    }
    return cur == 0;
}

/* Random switches with no acceptance test (plateau move). */
static void shake(int k) {
    int done = 0;
    for (int t = 0; t < 40 * k && done < k; t++) {
        int a, b, c, e;
        if (pick_switch(&a, &b, &c, &e)) {
            apply_switch(a, b, c, e);
            done++;
        }
    }
}

/* Add cross-side edges between deficient vertices (never hurts validity). */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (nadj[v] < DMAX) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && nadj[a] < DMAX; j++) {
            int b = R[j];
            if (nadj[b] < DMAX && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add one vertex on the side opposite to `side`, joined to a greedy cover of `side`. */
static int add_vertex_cover(int side) {
    if (N >= MAXN - 2) return 0;
    compute_balls();
    int W = (N + 63) / 64;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(cov));
    static int C[MAXN];
    static char used[MAXN];
    int nc = 0;
    for (int v = 0; v < N; v++) {
        used[v] = 0;
        if (col[v] == side) C[nc++] = v;
    }
    shuffle_int(C, nc);
    int chosen[MAXDEG];
    int nch = 0;
    for (int step = 0; step < DMAX; step++) {
        int best = -1, bestg = 0, ties = 0;
        for (int i = 0; i < nc; i++) {
            int c = C[i];
            if (used[c]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc64(ballb[c][w] & ~cov[w]);
            if (g > bestg) {
                bestg = g;
                best = c;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndi(ties) == 0) best = c;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= ballb[best][w];
    }
    int v = N++;
    nadj[v] = 0;
    col[v] = 1 - side;
    for (int i = 0; i < nch; i++) {
        int x = chosen[i];
        if (nadj[x] >= DMAX) {
            int y = adj[x][rndi(nadj[x])];
            del_edge(x, y);
        }
        add_edge(x, v);
    }
    return 1;
}

static void emit_best(void) {
    long long m = 0;
    for (int v = 0; v < bN; v++) m += bnadj[v];
    m /= 2;
    printf("%d %lld\n", bN, m);
    for (int u = 0; u < bN; u++) {
        for (int k = 0; k < bnadj[u]; k++) {
            int v = badj[u][k];
            if (u < v) printf("%d %d\n", u, v);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 2 || d > MAXDEG - 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    DMAX = d;
    DIAM = D;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 0 || n > MAXN - 200 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) nadj[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (nadj[u] >= DMAX || nadj[v] >= DMAX || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        que[t++] = s;
        while (h < t) {
            int u = que[h++];
            for (int k = 0; k < nadj[u]; k++) {
                int w = adj[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    que[t++] = w;
                }
            }
        }
    }
    (void)dummy_col;

    if (N == 0) {
        printf("0 0\n");
        return 0;
    }

    double deadline = now() + tl;
    if (cost() != 0) {
        if (!anneal(3000, deadline)) {
            printf("0 0\n");
            return 0;
        }
    }
    save_best();

    while (now() < deadline && N < MAXN - 4) {
        save_state();
        if (rndi(3) == 0) {
            shake(24);
            if (!anneal(ANNEAL_CAP, deadline)) {
                restore_state();
                continue;
            }
            save_state();
        }
        int side = rndi(2);
        if (add_vertex_cover(side)) {
            fill_edges();
            if (anneal(ANNEAL_CAP, deadline)) {
                if (N > bN) save_best();
                continue;
            }
        }
        restore_state();
    }
    emit_best();
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


# ----------------------------------------------------------------------------
# Twin duplication.
#
# A vertex v' with N(v') = N(v), v' not adjacent to v, is a "twin" of v. Non-adjacent
# twins are at the same distance from every other vertex and at distance 2 from
# each other, so duplicating a vertex keeps the diameter (for D >= 2), keeps the
# graph bipartite, and needs only spare degree on the neighbours of v.
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
# Python large-neighbourhood search (kill, repair, regrow).
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.08 * T, rng)
            consider(n1, e1)

    # Short randomized twin-duplication pipelines.
    if D >= 2:
        trial_end = start + 0.10 * T
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Python kill-repair-regrow and redundant-edge pruning.
    if D >= 2 and time.monotonic() < start + 0.25 * T:
        _lns(best_n, best_e, d, D, start + 0.18 * T, rng, consider)
        _prune_regrow(best_n, best_e, d, D, start + 0.25 * T, rng, consider)

    # C engine: cover-grow plus degree-preserving anneal from the best graph so far.
    # Skip when the Moore bound is already reached (calibration cases) or d is large.
    if D >= 2 and 2 <= d <= 60 and best_n < lib.moore_bound(d, D):
        elapsed = time.monotonic() - start
        budget = 0.80 * T - elapsed - 3.0  # margin for the one-off C compile
        if budget >= 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, int(seed), round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 20.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass  # keep the Python result

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
