import itertools
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

/* Bitset-exact bipartite diameter search.
 * State: bipartite graph with degree <= DEG, always valid (diameter <= D) once accepted.
 * Move: attach a new vertex by greedy ball-cover (stealing a slot when a target is full),
 * fill spare degree, repair with double-edge switches (degrees and sides preserved)
 * minimising the number of pairs at distance > D, then prune redundant edges.
 * Restarts from the best graph with random switch perturbations when stuck. */

#define MAXN 1400
#define MAXD 32
#define MAXW 22

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} G;

static G g, snap, best;
static int D, DEG;
static int W;
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static int mark[MAXN];
static int stamp = 0;
static double t_limit;
static struct timespec t0;
static int eu[MAXN * MAXD], ev[MAXN * MAXD];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) {
    if (m <= 0) return 0;
    return (int)(rnd() % (uint64_t)m);
}

static double elapsed(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)(t.tv_sec - t0.tv_sec) + 1e-9 * (double)(t.tv_nsec - t0.tv_nsec);
}

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static uint64_t *balls(int r) {
    int n = g.n;
    W = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            for (int k = 0; k < g.deg[v]; k++) {
                const uint64_t *t = cur + (size_t)g.adj[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    return cur;
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long cost(void) {
    uint64_t *b = balls(D);
    int n = g.n;
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc(b[(size_t)v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < g.deg[a]; k++)
        if (g.adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    g.adj[a][g.deg[a]++] = b;
    g.adj[b][g.deg[b]++] = a;
}

static void del_from(int a, int b) {
    for (int k = 0; k < g.deg[a]; k++) {
        if (g.adj[a][k] == b) {
            g.adj[a][k] = g.adj[a][--g.deg[a]];
            return;
        }
    }
}

static void rem_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
}

static int color_graph(void) {
    int n = g.n;
    static int q[MAXN];
    for (int v = 0; v < n; v++) g.col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (g.col[s] != -1) continue;
        g.col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = 0; k < g.deg[u]; k++) {
                int v = g.adj[u][k];
                if (g.col[v] == -1) {
                    g.col[v] = 1 - g.col[u];
                    q[tail++] = v;
                } else if (g.col[v] == g.col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* New vertex on a random side, attached greedily to opposite-side ball covers. */
static void add_vertex(void) {
    int n = g.n;
    if (n + 1 >= MAXN) return;
    int c = rndint(2);
    uint64_t *b = balls(D - 1);
    int ww = W;
    uint64_t cov[MAXW];
    for (int w = 0; w < ww; w++) cov[w] = 0;
    stamp++;
    int v = n;
    g.n = n + 1;
    g.deg[v] = 0;
    g.col[v] = c;
    for (int it = 0; it < DEG; it++) {
        int bu = -1;
        long bs = -1;
        for (int u = 0; u < n; u++) {
            if (g.col[u] != 1 - c || mark[u] == stamp) continue;
            long gain = 0;
            for (int w = 0; w < ww; w++) gain += pc(b[(size_t)u * ww + w] & ~cov[w]);
            if (gain == 0) continue;
            long sc = gain * 8 + rndint(8);
            if (sc > bs) {
                bs = sc;
                bu = u;
            }
        }
        if (bu < 0) break;
        mark[bu] = stamp;
        if (g.deg[bu] >= DEG) {
            int t = g.adj[bu][rndint(g.deg[bu])];
            rem_edge(bu, t);
        }
        add_edge(bu, v);
        for (int w = 0; w < ww; w++) cov[w] |= b[(size_t)bu * ww + w];
    }
}

static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < g.n; v++) {
        if (g.deg[v] < DEG) {
            if (g.col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    if (!nl || !nr) return;
    int tries = 4 * (nl + nr) + 10;
    for (int t = 0; t < tries; t++) {
        int a = L[rndint(nl)], b = R[rndint(nr)];
        if (g.deg[a] < DEG && g.deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
    }
}

static int build_L0(int *L0) {
    int nl = 0;
    for (int v = 0; v < g.n; v++)
        if (g.col[v] == 0) L0[nl++] = v;
    return nl;
}

/* Pick a switch a-b, c-e -> a-e, c-b with a,c on side 0. */
static int find_switch(const int *L0, int nl, int *o) {
    if (nl < 2) return 0;
    for (int t = 0; t < 20; t++) {
        int a = L0[rndint(nl)], c = L0[rndint(nl)];
        if (a == c || g.deg[a] == 0 || g.deg[c] == 0) continue;
        int b = g.adj[a][rndint(g.deg[a])];
        int e = g.adj[c][rndint(g.deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        o[0] = a;
        o[1] = b;
        o[2] = c;
        o[3] = e;
        return 1;
    }
    return 0;
}

static void apply_switch(int a, int b, int c, int e) {
    rem_edge(a, b);
    rem_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static void undo_switch(int a, int b, int c, int e) {
    rem_edge(a, e);
    rem_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

static long anneal(int iters) {
    int L0[MAXN];
    int nl = build_L0(L0);
    long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        int o[4];
        if (!find_switch(L0, nl, o)) continue;
        apply_switch(o[0], o[1], o[2], o[3]);
        long nc = cost();
        if (nc <= cur || (nc == cur + 1 && rndint(10) == 0)) {
            cur = nc;
        } else {
            undo_switch(o[0], o[1], o[2], o[3]);
        }
    }
    return cur;
}

static void perturb(int k) {
    int L0[MAXN];
    int nl = build_L0(L0);
    int done = 0;
    for (int t = 0; t < 50 * k && done < k; t++) {
        int o[4];
        if (!find_switch(L0, nl, o)) continue;
        apply_switch(o[0], o[1], o[2], o[3]);
        done++;
    }
}

/* Delete random redundant edges (diameter stays <= D). */
static void prune(int tests) {
    int m = 0;
    for (int v = 0; v < g.n; v++) {
        for (int k = 0; k < g.deg[v]; k++) {
            int u = g.adj[v][k];
            if (v < u) {
                eu[m] = v;
                ev[m] = u;
                m++;
            }
        }
    }
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tu = eu[i], tv = ev[i];
        eu[i] = eu[j];
        ev[i] = ev[j];
        eu[j] = tu;
        ev[j] = tv;
    }
    int done = 0;
    for (int i = 0; i < m && done < tests; i++) {
        int u = eu[i], v = ev[i];
        if (!has_edge(u, v)) continue;
        done++;
        rem_edge(u, v);
        if (cost() != 0) add_edge(u, v);
    }
}

static void search(void) {
    best = g;
    int fails = 0;
    while (elapsed() < t_limit) {
        if (g.n + 1 >= MAXN) break;
        snap = g;
        add_vertex();
        fill();
        long c = anneal(700);
        if (c == 0) {
            prune(400);
            best = g;
            fails = 0;
        } else {
            g = snap;
            fails++;
        }
        if (fails >= 150) {
            g = best;
            perturb(3 + rndint(5));
            fill();
            if (anneal(3000) != 0) g = best;
            fails = 0;
        }
    }
}

static void output_graph(const G *h) {
    int m = 0;
    for (int v = 0; v < h->n; v++)
        for (int k = 0; k < h->deg[v]; k++)
            if (h->adj[v][k] > v) m++;
    printf("%d %d\n", h->n, m);
    for (int v = 0; v < h->n; v++)
        for (int k = 0; k < h->deg[v]; k++)
            if (h->adj[v][k] > v) printf("%d %d\n", v, h->adj[v][k]);
}

static void fallback_kdd(void) {
    memset(g.deg, 0, sizeof g.deg);
    g.n = 2 * DEG;
    for (int i = 0; i < DEG; i++) {
        g.col[i] = 0;
        g.col[DEG + i] = 1;
    }
    for (int i = 0; i < DEG; i++)
        for (int j = 0; j < DEG; j++)
            add_edge(i, DEG + j);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    DEG = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    t_limit = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (DEG < 2 || DEG > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    static int pu[MAXN * MAXD], pv[MAXN * MAXD];
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    int ok = (n0 >= 1 && n0 < MAXN - 4 && m0 >= 0 && m0 <= MAXN * MAXD);
    for (int i = 0; ok && i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) {
            ok = 0;
            break;
        }
        if (a < 0 || b < 0 || a >= n0 || b >= n0 || a == b) {
            ok = 0;
            break;
        }
        pu[i] = a;
        pv[i] = b;
    }
    if (ok) {
        memset(g.deg, 0, sizeof g.deg);
        g.n = n0;
        for (int i = 0; ok && i < m0; i++) {
            int a = pu[i], b = pv[i];
            if (g.deg[a] >= DEG || g.deg[b] >= DEG || has_edge(a, b)) {
                ok = 0;
            } else {
                add_edge(a, b);
            }
        }
    }
    if (ok) ok = color_graph();
    if (!ok) fallback_kdd();

    search();
    output_graph(&best);
    return 0;
}
"""


def build_kdd_fallback(d):
    return lib.haar_graph(d, range(d))


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
# Spare-slot matching on a point-line base.
# ----------------------------------------------------------------------------

def _spare_matching_base(n0, e0, d, rng, keep_free):
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


# ----------------------------------------------------------------------------
# Redundant-edge pruning, then regrow.
# ----------------------------------------------------------------------------

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
            pe = _prune_redundant(m, e, D, rng, deadline, 200)
            adj = _to_sets(m, pe)
            color = _bipartition(m, adj)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _py_build(d, D, seed, time_limit):
    """Python pipeline: structured base, twin/cover trials, LNS and pruning."""
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

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
            grow_end = start + 0.2 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.10 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if base_is_gq and D >= 4 and time.monotonic() < deadline:
        spare_end = start + 0.20 * time_limit
        while time.monotonic() < spare_end:
            keep = rng.choice((0, 2, 4, 8, 12, 20))
            sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
            gn, ge = _grow(sn, se, d, D, spare_end, rng)
            consider(gn, ge)

    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.55 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        prune_end = start + 0.75 * time_limit
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Stage 1: the Python pipeline gives a valid structured start graph.
    best_n, best_e = _py_build(d, D, seed, 0.35 * time_limit)

    # Stage 2: exact bitset C engine grows from that start graph.
    if D >= 2 and 2 <= d <= 30:
        left = time_limit - (time.monotonic() - start) - 4.0
        budget = min(0.45 * time_limit, left)
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 6.0)
                n, e = lib.parse_graph_text(out)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_e = n, e
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
