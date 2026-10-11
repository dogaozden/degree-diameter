import itertools
import random
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 32
#define ITERS 3000
#define T0_ 2.0
#define T1_ 0.2

static int d_, D_;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int side[MAXN];
static uint64_t ballbuf[2][MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;

static int snap_adj[MAXN][MAXD];
static int snap_deg[MAXN];
static int snap_side[MAXN];
static int snap_n;

static int g_s0[MAXN];
static int g_ns0;

typedef struct { int a, b, c, e; } Move;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}

static void repl(int a, int old, int nw) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == old) { adj[a][k] = nw; return; }
    }
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) { adj[a][k] = adj[a][--deg[a]]; break; }
    }
    for (int k = 0; k < deg[b]; k++) {
        if (adj[b][k] == a) { adj[b][k] = adj[b][--deg[b]]; break; }
    }
}

// Balls of radius r: bit w of row v is set iff dist(v, w) <= r. Valid until the next call.
static uint64_t *compute_balls(int n, int r) {
    int W = (n + 63) >> 6;
    uint64_t *cur = ballbuf[0], *nxt = ballbuf[1];
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

static long long bad_pairs(int n, const uint64_t *ball) {
    int W = (n + 63) >> 6;
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = ball + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(row[w]);
        tot += n - c;
    }
    return tot / 2;
}

static long long full_cost(int n) { return bad_pairs(n, compute_balls(n, D_)); }

static void build_s0(int n) {
    g_ns0 = 0;
    for (int v = 0; v < n; v++) if (side[v] == 0) g_s0[g_ns0++] = v;
}

// One random bipartite double-edge switch: a-b, c-e become a-e, c-b (degrees kept).
static int random_switch(Move *mv) {
    if (g_ns0 < 2) return 0;
    int a = g_s0[rndint(g_ns0)];
    if (deg[a] == 0) return 0;
    int b = adj[a][rndint(deg[a])];
    int c = g_s0[rndint(g_ns0)];
    if (c == a || deg[c] == 0) return 0;
    int e = adj[c][rndint(deg[c])];
    if (e == b) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    repl(a, b, e);
    repl(b, a, c);
    repl(c, e, b);
    repl(e, c, a);
    mv->a = a; mv->b = b; mv->c = c; mv->e = e;
    return 1;
}

static void undo_switch(const Move *mv) {
    repl(mv->a, mv->e, mv->b);
    repl(mv->e, mv->a, mv->c);
    repl(mv->c, mv->b, mv->e);
    repl(mv->b, mv->c, mv->a);
}

static void shuffle_ints(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

// Add edges between deficient opposite-side vertices (only lowers the cost).
static void fill_edges(int n) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d_) {
            if (side[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    shuffle_ints(L, nl);
    shuffle_ints(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d_; j++) {
            int b = R[j];
            if (deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

// Simulated annealing over switches until the cost (bad pairs) hits 0.
static long long anneal(int n, long long cur, int iters, double deadline) {
    double lr = log(T1_ / T0_);
    double T = T0_;
    build_s0(n);
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0) {
            if (now_s() > deadline) break;
            T = T0_ * exp(lr * (double)it / (double)iters);
        }
        Move mv;
        if (!random_switch(&mv)) continue;
        long long nw = full_cost(n);
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nw;
        } else {
            undo_switch(&mv);
        }
    }
    return cur;
}

// Add one vertex on the opposite side of s, joined to a greedy ball cover of side s.
// Modifies the graph only when it returns 1.
static int try_grow(int *pn, int s) {
    int n = *pn;
    if (n + 1 >= MAXN) return 0;
    int W = (n + 63) >> 6;
    uint64_t *ball = compute_balls(n, D_ - 1);
    uint64_t covered[MAXW], full[MAXW];
    memset(covered, 0, sizeof covered);
    memset(full, 0, sizeof full);
    for (int v = 0; v < n; v++) full[v >> 6] |= 1ULL << (v & 63);
    static char used[MAXN];
    memset(used, 0, sizeof used);
    int chosen[MAXD];
    int nc = 0;
    while (nc < d_) {
        int complete = 1;
        for (int w = 0; w < W; w++) {
            if (covered[w] != full[w]) { complete = 0; break; }
        }
        if (complete) break;
        int best = -1;
        long long bestkey = -1;
        for (int c = 0; c < n; c++) {
            if (side[c] != s || used[c]) continue;
            const uint64_t *row = ball + (size_t)c * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(row[w] & ~covered[w]);
            if (g == 0) continue;
            long long key = (long long)g * 4096 + rndint(4096);
            if (key > bestkey) { bestkey = key; best = c; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        const uint64_t *row = ball + (size_t)best * W;
        for (int w = 0; w < W; w++) covered[w] |= row[w];
    }
    if (nc == 0) return 0;
    int v = n;
    side[v] = 1 - s;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (deg[c] >= d_) {
            int t = adj[c][rndint(deg[c])];
            del_edge(c, t);
        }
        add_edge(c, v);
    }
    *pn = n + 1;
    fill_edges(n + 1);
    return 1;
}

static void save_state(int n) {
    snap_n = n;
    memcpy(snap_adj, adj, sizeof(int) * (size_t)n * MAXD);
    memcpy(snap_deg, deg, sizeof(int) * (size_t)n);
    memcpy(snap_side, side, sizeof(int) * (size_t)n);
}

static int restore_state(void) {
    int n = snap_n;
    memcpy(adj, snap_adj, sizeof(int) * (size_t)n * MAXD);
    memcpy(deg, snap_deg, sizeof(int) * (size_t)n);
    memcpy(side, snap_side, sizeof(int) * (size_t)n);
    return n;
}

static void print_graph(int n) {
    long long m = 0;
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] > u) m++;
    printf("%d %lld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] > u) printf("%d %d\n", u, adj[u][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    double t_end = now_s() + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN || m < 0 ||
        d_ < 2 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) { ok = 0; break; }
        if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) { ok = 0; break; }
        add_edge(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    // Bipartition by BFS; reject non-bipartite input.
    for (int v = 0; v < n; v++) side[v] = -1;
    static int q[MAXN];
    for (int s = 0; s < n && ok; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt && ok) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    q[qt++] = w;
                } else if (side[w] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    long long cur = full_cost(n);
    if (cur > 0) cur = anneal(n, cur, 20000, t_end);
    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }

    // Main loop: grow by one vertex and repair, or perturb on the plateau and repair.
    // The state is always valid because every failed attempt is rolled back.
    while (now_s() < t_end) {
        save_state(n);
        if (rnd01() < 0.6) {
            int nn = n;
            if (!try_grow(&nn, rndint(2))) continue;
            n = nn;
            long long c = anneal(n, full_cost(n), ITERS, t_end);
            if (c != 0) n = restore_state();
        } else {
            build_s0(n);
            int k = 1 + rndint(3);
            Move mv;
            for (int i = 0; i < k; i++) random_switch(&mv);
            long long c = anneal(n, full_cost(n), ITERS, t_end);
            if (c != 0) n = restore_state();
        }
    }

    print_graph(n);
    return 0;
}
'''


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
# C engine: vertex-addition plus switch annealing, run on the best graph found.
# ----------------------------------------------------------------------------

def _engine(d, D, seed, budget, n, edges):
    """Run the C search for `budget` seconds from (n, edges). Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 3.0)
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError, OSError):
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end_all = start + 0.90 * time_limit
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
            grow_end = start + 0.15 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.25 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C engine: the rest of the budget, starting from the best valid graph.
    # Skipped when the graph already meets the Moore bound (nothing can be added).
    if D >= 2 and d >= 2 and best_n <= 4000 and best_n < lib.moore_bound(d, D):
        budget = end_all - time.monotonic() - 1.5
        if budget >= 2.0:
            res = _engine(d, D, seed, budget, best_n, best_e)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
