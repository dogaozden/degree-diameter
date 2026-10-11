import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: wall-clock bitset annealing with incremental add-and-repair.
#
# Each round adds one vertex on one side, joins it greedily to a cover of the
# opposite side's (D-1)-balls, saturates spare degree, and anneals with
# degree-preserving bipartite double-edge switches until the diameter bound
# holds again. Failed rounds are rolled back exactly. Every accepted state is
# a valid graph, and the best one is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define NW (MAXN / 64)

static int d_, D_, n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t bufA[MAXN * NW], bufB[MAXN * NW];
static double deadline;
static uint64_t rs = 88172645463325252ULL;

static int sv_n;
static int sv_deg[MAXN];
static int sv_adj[MAXN][MAXD];
static int sv_col[MAXN];

static int best_n = 0, best_m = 0;
static int bu[MAXN * MAXD / 2], bv[MAXN * MAXD / 2];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int pc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
    }
}
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

/* Ball bitsets of radius r for the current graph; returns the buffer holding them. */
static uint64_t *balls(int r) {
    int nw = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * NW);
    for (int v = 0; v < n; v++) cur[v * NW + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *x = nxt + v * NW;
            uint64_t *c = cur + v * NW;
            for (int k = 0; k < nw; k++) x[k] = c[k];
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *cu = cur + adj[v][i] * NW;
                for (int k = 0; k < nw; k++) x[k] |= cu[k];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance more than r (unreachable pairs count). */
static long long cost_of(int r) {
    uint64_t *b = balls(r);
    int nw = (n + 63) >> 6;
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < nw; k++) c += pc(b[v * NW + k]);
        bad += n - c;
    }
    return bad / 2;
}

static long long cur_cost;

/* Degree-preserving bipartite double-edge switches. True if cost reaches 0. */
static int anneal(int iters) {
    static int s0[MAXN];
    int c0 = 0;
    cur_cost = cost_of(D_);
    for (int v = 0; v < n; v++) if (col[v] == 0) s0[c0++] = v;
    if (c0 == 0) return 0;
    for (int it = 0; it < iters && cur_cost > 0; it++) {
        if ((it & 31) == 0 && now() > deadline) break;
        int a = s0[rndi(c0)];
        int c = s0[rndi(c0)];
        if (a == c || deg[a] == 0 || deg[c] == 0) continue;
        int b = adj[a][rndi(deg[a])];
        int e = adj[c][rndi(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long long nc = cost_of(D_);
        if (nc <= cur_cost || (nc == cur_cost + 1 && rnd01() < 0.05)) {
            cur_cost = nc;
        } else {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur_cost == 0;
}

/* Add vertex n-1 on the opposite side of `side`, joined greedily to a cover of side's (D-1)-balls. */
static void add_vertex(int side) {
    int v = n - 1;
    uint64_t *b = balls(D_ - 1);
    int nw = (n + 63) >> 6;
    uint64_t covered[NW];
    int used[MAXN];
    memset(covered, 0, sizeof covered);
    memset(used, 0, sizeof used);
    used[v] = 1;
    int picks = 0;
    while (picks < d_) {
        int best = -1;
        double bestk = -1.0;
        for (int s = 0; s < n; s++) {
            if (col[s] != side || used[s]) continue;
            int g = 0;
            for (int k = 0; k < nw; k++) g += pc(b[s * NW + k] & ~covered[k]);
            double key = g + 0.5 * rnd01();
            if (key > bestk) { bestk = key; best = s; }
        }
        if (best < 0) break;
        used[best] = 1;
        picks++;
        if (deg[best] >= d_) {
            int t = adj[best][rndi(deg[best])];
            del_edge(best, t);
        }
        add_edge(best, v);
        for (int k = 0; k < nw; k++) covered[k] |= b[best * NW + k];
    }
}

static void shuffle_ints(int *x, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = x[i]; x[i] = x[j]; x[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    static int Lv[MAXN], Rv[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= d_) continue;
        if (col[v] == 0) Lv[nl++] = v; else Rv[nr++] = v;
    }
    shuffle_ints(Lv, nl);
    shuffle_ints(Rv, nr);
    for (int i = 0; i < nl; i++) {
        int a = Lv[i];
        for (int j = 0; j < nr && deg[a] < d_; j++) {
            int b = Rv[j];
            if (deg[b] >= d_ || has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

static void snapshot(void) {
    sv_n = n;
    memcpy(sv_deg, deg, sizeof deg);
    memcpy(sv_adj, adj, sizeof adj);
    memcpy(sv_col, col, sizeof col);
}
static void restore(void) {
    n = sv_n;
    memcpy(deg, sv_deg, sizeof deg);
    memcpy(adj, sv_adj, sizeof adj);
    memcpy(col, sv_col, sizeof col);
}

static void record_best(void) {
    best_n = n;
    best_m = 0;
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int w = adj[v][i];
            if (v < w && best_m < MAXN * MAXD / 2) {
                bu[best_m] = v;
                bv[best_m] = w;
                best_m++;
            }
        }
    }
}

static void colorize(void) {
    static int st[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp > 0) {
            int u = st[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) { col[w] = 1 - col[u]; st[sp++] = w; }
            }
        }
    }
}

static int read_input(void) {
    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; return 0; }
    if (n <= 0 || n > MAXN) { n = 0; return 0; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d_ < 1) d_ = 1;
    if (d_ > MAXD) d_ = MAXD;
    if (D_ < 2) D_ = 2;
    rs ^= ((uint64_t)seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    deadline = now() + budget;

    if (read_input()) {
        colorize();
        if (cost_of(D_) == 0) record_best();
        int iters = 3000, fails = 0;
        while (n > 0 && n < MAXN && now() < deadline) {
            snapshot();
            int side = rndi(2);
            col[n] = 1 - side;
            deg[n] = 0;
            n++;
            add_vertex(side);
            fill();
            if (anneal(iters)) {
                record_best();
                fails = 0;
                iters = 3000;
            } else {
                restore();
                if (++fails % 10 == 0 && iters < 64000) iters *= 2;
            }
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
'''


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
# Shared Python helpers.
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
# Twin duplication: non-adjacent twins are at distance 2 from each other and at
# the same distance from everything else, so duplication keeps the diameter.
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
    bound = lib.moore_bound(d, D)

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
            n1, e1 = _grow(n0, e0, d, D, start + 0.1 * time_limit, rng)
            consider(n1, e1)

    # Calibration cases already at the Moore-style bound return immediately.
    if best_n >= bound:
        return best_n, list(best_e)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.2 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C annealer: add-and-repair from the best valid graph found so far.
    if D >= 2 and d <= 60 and best_n < 1000 and time.monotonic() < start + 0.75 * time_limit:
        budget = 0.78 * time_limit - (time.monotonic() - start) - 1.5
        if budget > 2:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 10)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
