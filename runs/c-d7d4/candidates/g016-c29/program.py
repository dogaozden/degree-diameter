"""Cover-growth plus C annealing for bipartite graphs with degree d and diameter D.

Python builds a structured base (generalized quadrangle W(q) for D >= 4, projective plane for
D = 3), grows it with cheap cover vertices, and returns instantly when the Moore bound is met.
The C engine then works from the best graph: it keeps a valid graph, adds one vertex whose
neighbourhood covers the old vertices within distance D-1, and repairs bad pairs with
degree-preserving bipartite double-edge switches. It uses exact bitset ball counts and restores
the last valid snapshot when a phase stalls.
"""
import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4200
#define MAXW 66
#define MAXD 40
#define PHASE_LIMIT 6000

static int d, D;
static int n, W;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static int side[2][MAXN];
static int cnt[2];

static int snap_n;
static int snap_adj[MAXN][MAXD];
static int snap_deg[MAXN];
static int snap_col[MAXN];

static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t_begin;
static double budget;

static double elapsed(void) { return (double)(clock() - t_begin) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rebuild_sides(void) {
    int i;
    cnt[0] = cnt[1] = 0;
    for (i = 0; i < n; i++) side[col[i]][cnt[col[i]]++] = i;
}

static int has_edge(int u, int v) {
    int j;
    for (j = 0; j < deg[u]; j++)
        if (adj[u][j] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_arc(int u, int v) {
    int j;
    for (j = 0; j < deg[u]; j++) {
        if (adj[u][j] == v) {
            adj[u][j] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* Bitset balls of radius r: returns a pointer to n rows of W words. */
static uint64_t *compute_balls(int r) {
    uint64_t *cur = bufA, *nxt = bufB;
    int i, j, w, k;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (i = 0; i < n; i++) cur[(size_t)i * W + (size_t)(i >> 6)] |= 1ULL << (i & 63);
    for (k = 0; k < r; k++) {
        for (i = 0; i < n; i++) {
            uint64_t *dst = nxt + (size_t)i * W;
            const uint64_t *src = cur + (size_t)i * W;
            for (w = 0; w < W; w++) dst[w] = src[w];
            for (j = 0; j < deg[i]; j++) {
                const uint64_t *s = cur + (size_t)adj[i][j] * W;
                for (w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        {
            uint64_t *t = cur;
            cur = nxt;
            nxt = t;
        }
    }
    return cur;
}

/* Number of unordered pairs at distance greater than D (unreachable counts). */
static long cost_full(void) {
    uint64_t *b = compute_balls(D);
    long s = 0;
    int i, w;
    for (i = 0; i < n; i++) {
        int c = 0;
        for (w = 0; w < W; w++) c += pc64(b[(size_t)i * W + w]);
        s += n - c;
    }
    return s / 2;
}

/* Add cross-side edges between deficient vertices. Never increases the cost. */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0, k, ii, jj;
    for (k = 0; k < cnt[0]; k++) {
        int v = side[0][k];
        if (deg[v] < d) L[nl++] = v;
    }
    for (k = 0; k < cnt[1]; k++) {
        int v = side[1][k];
        if (deg[v] < d) R[nr++] = v;
    }
    if (nl == 0 || nr == 0) return;
    {
        int oa = rndint(nl), ob = rndint(nr);
        for (ii = 0; ii < nl; ii++) {
            int a = L[(ii + oa) % nl];
            for (jj = 0; jj < nr; jj++) {
                int b = R[(jj + ob) % nr];
                if (deg[a] >= d) break;
                if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
            }
        }
    }
}

/* Add a vertex on a random side, joined to a greedy cover of the other side. */
static int grow_vertex(void) {
    static int used[MAXN];
    uint64_t unc[MAXW];
    int chosen[MAXD];
    int nch = 0, k, w, i, q;
    int c, o, v;
    uint64_t *b;

    if (n + 1 >= MAXN) return 0;
    b = compute_balls(D - 1);
    c = rndint(2);
    o = 1 - c;
    memset(unc, 0, sizeof unc);
    for (i = 0; i < n; i++) unc[i >> 6] |= 1ULL << (i & 63);
    memset(used, 0, sizeof(int) * (size_t)n);

    for (k = 0; k < d; k++) {
        int best = -1, bestg = 0, ties = 0;
        for (q = 0; q < cnt[o]; q++) {
            int s = side[o][q];
            int g = 0;
            if (used[s]) continue;
            for (w = 0; w < W; w++) g += pc64(b[(size_t)s * W + w] & unc[w]);
            if (g > bestg) {
                bestg = g;
                best = s;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndint(ties) == 0) best = s;
            }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        used[best] = 1;
        for (w = 0; w < W; w++) unc[w] &= ~b[(size_t)best * W + w];
    }
    if (nch == 0) return 0;

    v = n;
    n++;
    W = (n + 63) >> 6;
    deg[v] = 0;
    col[v] = c;
    side[c][cnt[c]++] = v;
    for (k = 0; k < nch; k++) {
        int s = chosen[k];
        if (deg[s] >= d) {
            int t = adj[s][rndint(deg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
    return 1;
}

static int mv_a, mv_b, mv_c, mv_e;

/* Degree-preserving bipartite double-edge switch: a-b, c-e become a-e, c-b. */
static int do_switch(void) {
    int a, c, b, e;
    if (cnt[0] < 2) return 0;
    a = side[0][rndint(cnt[0])];
    c = side[0][rndint(cnt[0])];
    if (a == c || deg[a] == 0 || deg[c] == 0) return 0;
    b = adj[a][rndint(deg[a])];
    e = adj[c][rndint(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    mv_a = a;
    mv_b = b;
    mv_c = c;
    mv_e = e;
    return 1;
}

static void undo_switch(void) {
    del_edge(mv_a, mv_e);
    del_edge(mv_c, mv_b);
    add_edge(mv_a, mv_b);
    add_edge(mv_c, mv_e);
}

static void save_snap(void) {
    int i;
    snap_n = n;
    for (i = 0; i < n; i++) {
        memcpy(snap_adj[i], adj[i], sizeof(int) * (size_t)d);
        snap_deg[i] = deg[i];
        snap_col[i] = col[i];
    }
}

static void load_snap(void) {
    int i;
    n = snap_n;
    for (i = 0; i < n; i++) {
        memcpy(adj[i], snap_adj[i], sizeof(int) * (size_t)d);
        deg[i] = snap_deg[i];
        col[i] = snap_col[i];
    }
    W = (n + 63) >> 6;
    rebuild_sides();
}

static int bfs_color(void) {
    static int q[MAXN];
    int i, s, qh, qt, j;
    for (i = 0; i < n; i++) col[i] = -1;
    for (s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        qh = 0;
        qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (j = 0; j < deg[u]; j++) {
                int v = adj[u][j];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[qt++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void set_kdd(void) {
    int i, j;
    memset(deg, 0, sizeof deg);
    n = 2 * d;
    W = (n + 63) >> 6;
    for (i = 0; i < n; i++) col[i] = (i < d) ? 0 : 1;
    for (i = 0; i < d; i++)
        for (j = 0; j < d; j++) add_edge(i, d + j);
    rebuild_sides();
}

int main(int argc, char **argv) {
    int gn = 0, gm = 0, i, ok = 1;
    long cur = 0;
    long moves = 0;
    int stuck = 0;

    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    t_begin = clock();

    if (d < 3 || d > MAXD - 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }

    if (scanf("%d %d", &gn, &gm) != 2) {
        gn = 0;
        gm = 0;
    }
    if (gn <= 0 || gn > MAXN - 200 || gm < 0) {
        ok = 0;
    } else {
        n = gn;
        for (i = 0; i < gm; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
                deg[u] >= d || deg[v] >= d || has_edge(u, v)) {
                ok = 0;
                break;
            }
            add_edge(u, v);
        }
    }
    if (ok) {
        W = (n + 63) >> 6;
        ok = bfs_color();
        if (ok) {
            rebuild_sides();
            if (cost_full() != 0) ok = 0;
        }
    }
    if (!ok) set_kdd();

    /* Saturate the start graph with cross edges (never hurts), then snapshot it. */
    fill_edges();
    cur = cost_full();
    if (cur != 0) {
        set_kdd();
        cur = 0;
    }
    save_snap();

    while (elapsed() < budget) {
        if (cur == 0) {
            if (n > snap_n) save_snap();
            stuck = 0;
            if (!grow_vertex()) break;
            fill_edges();
            cur = cost_full();
            continue;
        }
        {
            double frac = (double)stuck / (double)PHASE_LIMIT;
            double temp;
            if (frac > 1.0) frac = 1.0;
            temp = 1.2 * pow(0.1 / 1.2, frac);
            if (do_switch()) {
                long nc = cost_full();
                long delta = nc - cur;
                if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                    cur = nc;
                } else {
                    undo_switch();
                }
            }
        }
        moves++;
        stuck++;
        if (moves % 400 == 0) {
            fill_edges();
            cur = cost_full();
        }
        if (stuck > PHASE_LIMIT) {
            int k;
            load_snap();
            for (k = 0; k < 3; k++) do_switch();
            cur = cost_full();
            stuck = 0;
        }
    }
    if (cur == 0 && n > snap_n) save_snap();

    {
        int m = 0, j;
        for (i = 0; i < snap_n; i++)
            for (j = 0; j < snap_deg[i]; j++)
                if (snap_adj[i][j] > i) m++;
        printf("%d %d\n", snap_n, m);
        for (i = 0; i < snap_n; i++)
            for (j = 0; j < snap_deg[i]; j++)
                if (snap_adj[i][j] > i) printf("%d %d\n", i, snap_adj[i][j]);
    }
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
# Python-side cover growth (cheap pre-step before the C engine).
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of all vertices."""
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
            for attempt in range(60):
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    for _ in range(4):
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
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, t0 + 0.08 * T, rng)
            consider(n1, e1)

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        # Already optimal (calibration cases): return immediately.
        return best_n, list(best_e)

    # C engine: cover growth + degree-preserving annealing from the best graph.
    if D >= 2 and d >= 3:
        spent = time.monotonic() - t0
        budget = max(1.0, 0.75 * T - spent - 2.0)
        timeout = max(2.0, 0.9 * T - spent)
        if budget > 1.0:
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, int(seed) & 0x7FFFFFFF, f"{budget:.2f}"],
                    stdin_graph=(best_n, best_e),
                    timeout=timeout,
                )
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
