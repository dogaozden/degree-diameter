import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cost-driven vertex insertion with degree-preserving switches.
#
# Each attempt copies the current valid graph, adds one vertex whose neighbours
# greedily cover all old vertices within distance D-1, fills spare slots, then
# anneals bipartite double-edge switches (degrees unchanged) to remove the bad
# pairs (pairs at distance > D). Success keeps the larger graph; failure restores
# the snapshot. Occasional random switch kicks diversify the starting point.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXD 24
#define MAXW ((MAXN + 63) / 64)

static int d_, D_, n_, W_;
static int side_[MAXN];
static int deg_[MAXN];
static int adj_[MAXN][MAXD];
static uint64_t ballA_[MAXN * MAXW];
static uint64_t ballB_[MAXN * MAXW];
static uint64_t rs_ = 88172645463325252ULL;
static double budget_ = 1.0;
static clock_t t0_;

static int snap_n_;
static int snap_side_[MAXN];
static int snap_deg_[MAXN];
static int snap_adj_[MAXN][MAXD];
static int queue_[MAXN];

typedef struct { int a, b, c, e; } Sw;

static uint64_t rnext(void) {
    rs_ ^= rs_ >> 12;
    rs_ ^= rs_ << 25;
    rs_ ^= rs_ >> 27;
    return rs_ * 2685821657736338717ULL;
}

static int rndint(int k) { return (int)((rnext() >> 11) % (uint64_t)k); }

static double rnd01(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)(clock() - t0_) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ballA_ = bitmask of vertices within distance radius of each vertex. */
static void balls(int radius) {
    int n = n_;
    int W = (n + 63) / 64;
    W_ = W;
    size_t total = (size_t)n * (size_t)W;
    memset(ballA_, 0, sizeof(uint64_t) * total);
    for (int v = 0; v < n; v++) ballA_[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < radius; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = ballB_ + (size_t)v * W;
            const uint64_t *src = ballA_ + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *s2 = ballA_ + (size_t)adj_[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        memcpy(ballA_, ballB_, sizeof(uint64_t) * total);
    }
}

/* Number of unordered pairs at distance > D_ (unreachable pairs count). */
static long long cost(void) {
    balls(D_);
    int n = n_, W = W_;
    long long s = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *b = ballA_ + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pc64(b[w]);
        s += n - c;
    }
    return s / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg_[a]; k++) if (adj_[a][k] == b) return 1;
    return 0;
}

static void rm_from(int a, int b) {
    for (int k = 0; k < deg_[a]; k++) {
        if (adj_[a][k] == b) {
            adj_[a][k] = adj_[a][--deg_[a]];
            return;
        }
    }
}

static void add_edge(int a, int b) {
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}

static void del_edge(int a, int b) {
    rm_from(a, b);
    rm_from(b, a);
}

static int pick_side(int s) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(n_);
        if (side_[v] == s && deg_[v] > 0) return v;
    }
    return -1;
}

/* Switch a-b, c-e (a, c on side 0) into a-e, c-b. Degrees are preserved. */
static int do_switch(Sw *s) {
    for (int t = 0; t < 50; t++) {
        int a = pick_side(0);
        int c = pick_side(0);
        if (a < 0 || c < 0 || a == c) continue;
        int b = adj_[a][rndint(deg_[a])];
        int e = adj_[c][rndint(deg_[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        s->a = a; s->b = b; s->c = c; s->e = e;
        return 1;
    }
    return 0;
}

static void undo_switch(const Sw *s) {
    del_edge(s->a, s->e);
    del_edge(s->c, s->b);
    add_edge(s->a, s->b);
    add_edge(s->c, s->e);
}

/* Anneal switches until cost 0. Returns 1 if cost reached 0. */
static int anneal(int iters, double T0) {
    long long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if (elapsed() > budget_) break;
        Sw s;
        if (!do_switch(&s)) continue;
        long long nw = cost();
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            undo_switch(&s);
        }
    }
    return cur == 0;
}

/* Join deficient opposite-side non-adjacent pairs. This only shortens distances. */
static void fill(void) {
    int n = n_;
    int off0 = rndint(n), off1 = rndint(n);
    for (int i = 0; i < n; i++) {
        int a = (i + off0) % n;
        if (side_[a] != 0 || deg_[a] >= d_) continue;
        for (int j = 0; j < n; j++) {
            int b = (j + off1) % n;
            if (side_[b] != 1 || deg_[b] >= d_) continue;
            if (has_edge(a, b)) continue;
            add_edge(a, b);
            if (deg_[a] >= d_) break;
        }
    }
}

/* Add a vertex on one side, joined to a randomized greedy cover of the other side. */
static int add_vertex(void) {
    int n = n_;
    if (n + 1 >= MAXN) return 0;
    balls(D_ - 1);
    int W = W_;
    int sv = rndint(2);
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nc = 0;
    while (nc < d_) {
        int best = -1, bestg = 0;
        double bests = -1.0;
        for (int u = 0; u < n; u++) {
            if (side_[u] == sv) continue;
            int used = 0;
            for (int k = 0; k < nc; k++) if (chosen[k] == u) { used = 1; break; }
            if (used) continue;
            int g = 0;
            const uint64_t *b = ballA_ + (size_t)u * W;
            for (int w = 0; w < W; w++) g += pc64(b[w] & ~cov[w]);
            double sc = g + 0.6 * rnd01();
            if (sc > bests) { bests = sc; best = u; bestg = g; }
        }
        if (best < 0 || bestg == 0) break;
        chosen[nc++] = best;
        const uint64_t *b = ballA_ + (size_t)best * W;
        for (int w = 0; w < W; w++) cov[w] |= b[w];
    }
    if (nc == 0) return 0;
    int v = n;
    side_[v] = sv;
    deg_[v] = 0;
    n_ = n + 1;
    for (int k = 0; k < nc; k++) {
        int u = chosen[k];
        if (deg_[u] >= d_) {
            int t = adj_[u][rndint(deg_[u])];
            del_edge(u, t);
        }
        add_edge(v, u);
    }
    return 1;
}

static void save_state(void) {
    snap_n_ = n_;
    memcpy(snap_side_, side_, sizeof(int) * (size_t)n_);
    memcpy(snap_deg_, deg_, sizeof(int) * (size_t)n_);
    memcpy(snap_adj_, adj_, sizeof(int) * (size_t)MAXD * (size_t)n_);
}

static void restore_state(void) {
    n_ = snap_n_;
    memcpy(side_, snap_side_, sizeof(int) * (size_t)n_);
    memcpy(deg_, snap_deg_, sizeof(int) * (size_t)n_);
    memcpy(adj_, snap_adj_, sizeof(int) * (size_t)MAXD * (size_t)n_);
}

/* K_{d,d} fallback, valid for D >= 2. */
static void set_fallback(void) {
    n_ = 2 * d_;
    for (int v = 0; v < n_; v++) {
        deg_[v] = 0;
        side_[v] = v < d_ ? 0 : 1;
    }
    for (int a = 0; a < d_; a++)
        for (int b = 0; b < d_; b++)
            add_edge(a, d_ + b);
}

static int color_graph(void) {
    for (int v = 0; v < n_; v++) side_[v] = -1;
    for (int s = 0; s < n_; s++) {
        if (side_[s] != -1) continue;
        side_[s] = 0;
        int qh = 0, qt = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int k = 0; k < deg_[u]; k++) {
                int w = adj_[u][k];
                if (side_[w] == -1) {
                    side_[w] = 1 - side_[u];
                    queue_[qt++] = w;
                } else if (side_[w] == side_[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int load_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n >= MAXN || m < 0 || m > MAXN * MAXD) return 0;
    n_ = n;
    for (int i = 0; i < n; i++) deg_[i] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (has_edge(u, v)) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_) continue;
        add_edge(u, v);
    }
    return color_graph();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    budget_ = atof(argv[4]);
    t0_ = clock();
    if (d_ < 2 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < 20; i++) rnext();

    if (!load_input()) set_fallback();
    if (cost() != 0) {
        anneal(60000, 0.8);
        if (cost() != 0) set_fallback();
    }

    while (elapsed() < budget_) {
        save_state();
        if (rnd01() < 0.25) {
            Sw s;
            for (int k = 0; k < 6; k++) do_switch(&s);
        }
        if (!add_vertex()) {
            restore_state();
            if (n_ + 1 >= MAXN) break;
            continue;
        }
        fill();
        if (!anneal(3000, 0.6)) restore_state();
    }

    if (cost() != 0) set_fallback();

    int m = 0;
    for (int v = 0; v < n_; v++)
        for (int k = 0; k < deg_[v]; k++)
            if (adj_[v][k] > v) m++;
    printf("%d %d\n", n_, m);
    for (int v = 0; v < n_; v++)
        for (int k = 0; k < deg_[v]; k++)
            if (adj_[v][k] > v) printf("%d %d\n", v, adj_[v][k]);
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
# Shared Python graph helpers.
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


def _spare_matching_base(n0, e0, d, rng, keep_free):
    """Point-line base: add random cross-side edges into spare slots, keeping some free."""
    n = n0
    half = n // 2
    adj = _to_sets(n, e0)
    rounds = d - max(len(a) for a in adj)
    for _ in range(max(0, rounds)):
        order = [p for p in range(half) if len(adj[p]) < d]
        rng.shuffle(order)
        target = max(0, len(order) - keep_free)
        count = 0
        for p in order:
            if count >= target:
                break
            cands = [L for L in range(half, n) if len(adj[L]) < d and L not in adj[p]]
            if not cands:
                continue
            L = rng.choice(cands)
            adj[p].add(L)
            adj[L].add(p)
            count += 1
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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
# Build: structured base and short Python growth, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    prep_end = start + 0.22 * time_limit
    c_end = start + 0.80 * time_limit
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
    base_is_gq = False
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is not None:
            base_is_gq = True
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Short randomized Python phase: twin/cover pipelines and spare-slot matching.
    if D >= 2:
        while time.monotonic() < prep_end:
            if base_is_gq and rng.random() < 0.5:
                keep = rng.choice((0, 2, 4, 8, 12, 20))
                sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
                gn, ge = _grow(sn, se, d, D, prep_end, rng)
            else:
                gn, ge = _trial(base_n, base_e, d, D, rng, prep_end)
            consider(gn, ge)

    # C annealer: grow from the best valid graph found so far.
    if D >= 2 and d >= 2:
        budget = max(1.0, c_end - time.monotonic() - 2.0)
        if budget >= 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                                 stdin_graph=(best_n, best_e),
                                 timeout=budget + 4.0)
                cn, ce = lib.parse_graph_text(text)
                consider(cn, ce)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
