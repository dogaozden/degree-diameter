import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Works on a valid bipartite graph with max degree d and diameter <= D. Each
# step either (a) adds a vertex joined to a greedy cover of the opposite side,
# or (b) kills a random vertex. Both are followed by cross-side filling and a
# simulated-annealing repair. The repair uses degree-preserving bipartite
# double-edge switches, with cost = number of pairs farther than D apart
# (computed with bitset balls). Only zero-cost states are accepted, so the
# output is always valid. Output is the best valid graph found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define MAXD 64
#define ANN_IT 700

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int side[MAXN];
} State;

static int d, D, n, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static uint64_t BX[MAXN][MAXW], BY[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static double t0, limit_s;
static State best_s, snap_s;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC - t0; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void rem_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    rem_arc(a, b);
    rem_arc(b, a);
}

/* Bitset balls of radius r into BX; returns number of unordered pairs at distance > r. */
static long ball_cost(int r) {
    W = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = BX, (*nxt)[MAXW] = BY;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        tot += n - c;
    }
    if (cur != BX)
        for (int v = 0; v < n; v++) memcpy(BX[v], cur[v], sizeof(uint64_t) * W);
    return tot / 2;
}

/* Add a vertex on the opposite side of c, joined to a greedy cover of side c. */
static void add_vertex(int c) {
    int v = n++;
    side[v] = 1 - c;
    deg[v] = 0;
    ball_cost(D - 1);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    for (int step = 0; step < d; step++) {
        int best = -1;
        double bg = -1e18;
        for (int s = 0; s < v; s++) {
            if (side[s] != c || has_edge(s, v)) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(BX[s][w] & ~cov[w]);
            double sc = g + 0.5 * rndu() - (deg[s] >= d ? 3.0 : 0.0);
            if (sc > bg) {
                bg = sc;
                best = s;
            }
        }
        if (best < 0) break;
        if (deg[best] >= d) {
            int t = adj[best][rndi(deg[best])];
            del_edge(best, t);
        }
        add_edge(best, v);
        for (int w = 0; w < W; w++) cov[w] |= BX[best][w];
    }
}

static void shuffle_arr(int *x, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Join deficient opposite-side vertices in random order. */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_arr(L, nl);
    shuffle_arr(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d; j++) {
            int b = R[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. True if cost 0. */
static int anneal(int iters) {
    static int cand[MAXN];
    long cur = ball_cost(D);
    for (int it = 0; it < iters && cur > 0; it++) {
        if (elapsed() > limit_s) break;
        int nc = 0;
        for (int v = 0; v < n; v++)
            if (side[v] == 0 && deg[v] > 0) cand[nc++] = v;
        if (nc < 2) break;
        int a = cand[rndi(nc)];
        int c = cand[rndi(nc)];
        if (a == c) continue;
        int b = adj[a][rndi(deg[a])];
        int e = adj[c][rndi(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        double T = 0.6 * (1.0 - (double)it / iters) + 0.03;
        long nw = ball_cost(D);
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

/* Remove vertex v and relabel the last vertex into its slot. */
static void kill_vertex(int v) {
    while (deg[v] > 0) {
        int u = adj[v][0];
        del_edge(u, v);
    }
    int L = n - 1;
    if (v != L) {
        for (int k = 0; k < deg[L]; k++) {
            int u = adj[L][k];
            for (int j = 0; j < deg[u]; j++)
                if (adj[u][j] == L) {
                    adj[u][j] = v;
                    break;
                }
        }
        deg[v] = deg[L];
        memcpy(adj[v], adj[L], sizeof(int) * deg[L]);
        side[v] = side[L];
    }
    deg[L] = 0;
    n--;
}

static void save_state(State *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * n);
    memcpy(s->adj, adj, sizeof(int) * MAXD * n);
    memcpy(s->side, side, sizeof(int) * n);
}

static void load_state(const State *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * n);
    memcpy(adj, s->adj, sizeof(int) * MAXD * n);
    memcpy(side, s->side, sizeof(int) * n);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    limit_s = atof(argv[4]);
    t0 = (double)clock() / CLOCKS_PER_SEC;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > MAXN - 40 ||
        d < 2 || d >= MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    memset(deg, 0, sizeof deg);
    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            bad = 1;
            break;
        }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || deg[u] >= d ||
            deg[v] >= d || has_edge(u, v)) {
            bad = 1;
            continue;
        }
        add_edge(u, v);
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* Bipartition check. */
    static int col[MAXN], stk[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) side[v] = col[v];

    if (ball_cost(D) != 0) anneal(ANN_IT * 30);
    if (ball_cost(D) != 0) {
        printf("0 0\n");
        return 0;
    }

    save_state(&best_s);
    int bestn = n;
    while (elapsed() < limit_s) {
        save_state(&snap_s);
        int ok = 0;
        if (rndu() < 0.8 && n < MAXN - 2) {
            add_vertex(rndi(2));
            fill();
            ok = anneal(ANN_IT);
        } else if (n > 12) {
            kill_vertex(rndi(n));
            fill();
            ok = anneal(ANN_IT / 2);
        }
        if (ok) {
            if (n > bestn) {
                bestn = n;
                save_state(&best_s);
            }
        } else {
            load_state(&snap_s);
        }
        if (n < bestn - 3) load_state(&best_s);
    }

    int bn = best_s.n;
    int m = 0;
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < best_s.deg[v]; k++)
            if (v < best_s.adj[v][k]) m++;
    printf("%d %d\n", bn, m);
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < best_s.deg[v]; k++)
            if (v < best_s.adj[v][k]) printf("%d %d\n", v, best_s.adj[v][k]);
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
# Twin duplication.
#
# A vertex v' with N(v') = N(v), v' not adjacent to v, is a "twin" of v. Such
# duplication keeps the diameter bound (for D >= 2), keeps bipartiteness, and
# needs only spare degree on the neighbours of v.
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
# Python large-neighbourhood search (fallback when C is unavailable).
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Known-optimal calibration cases return immediately.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.18 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Main stage: C kill / add / anneal engine from the best valid graph so far.
    if D >= 2:
        c_budget = 0.72 * time_limit - (time.monotonic() - start) - 1.5
        if c_budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=(best_n, list(best_e)),
                                timeout=c_budget + 8.0)
                cn, ce = lib.parse_graph_text(out)
                consider(cn, ce)
            except Exception:
                pass

    # Remaining time: Python LNS from the best valid graph.
    lns_end = start + 0.88 * time_limit
    if D >= 2 and time.monotonic() < lns_end - 1.0:
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
