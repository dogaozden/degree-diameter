import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost annealing with targeted switches and kill-repair-regrow.
#
# Cost = number of vertex pairs at distance > D, computed with bitset balls.
# Moves are bipartite double-edge switches (degrees and bipartiteness kept).
# Half of the switches are TARGETED: pick a bad pair (x, y) on opposite sides and
# switch so that x-y becomes an edge. This directly repairs the diameter instead
# of waiting for random switches to hit the right pair.
# Growth inserts a vertex joined to a greedy cover of radius D-1 balls, then anneals.
# A valid state is only ever stored as best; every accepted state is valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1536
#define MAXW (MAXN / 64)
#define MAXD 64
#define ITER_G 2000
#define ITER_K 2000

typedef uint64_t Row[MAXW];

typedef struct {
    int n;
    int col[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXD];
} Snap;

static int d_ = 3, D_ = 3;
static int n = 0;
static int col[MAXN], deg[MAXN], nb[MAXN][MAXD];
static Row BA[MAXN], BB[MAXN];
static double t_end = 0.0;
static uint64_t rs = 88172645463325252ULL;
static Snap SNAP_BEST, SNAP_BAK, SNAP_BAK2;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset of vertices within distance r of each vertex. Returns BA or BB. */
static Row *balls(int r) {
    int W = (n + 63) >> 6;
    Row *A = BA, *B = BB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) A[v][w] = 0;
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) B[v][w] = A[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = A[nb[v][i]];
                for (int w = 0; w < W; w++) B[v][w] |= src[w];
            }
        }
        Row *T = A;
        A = B;
        B = T;
    }
    return A;
}

static long long bad_cost(void) {
    Row *R = balls(D_);
    int W = (n + 63) >> 6;
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(R[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (nb[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) {
            nb[a][i] = nb[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Remove a-b and c-e, add a-e and c-b. Degrees preserved. */
static void do_switch(int a, int b, int c, int e) {
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static int pick_vertex(int side) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(n);
        if (col[v] == side && deg[v] > 0) return v;
    }
    return -1;
}

/* A vertex at distance > D from u (uniform among such), or -1. */
static int find_bad_partner(int u, Row *R) {
    int cnt = 0, pick = -1;
    for (int v = 0; v < n; v++) {
        if (v == u) continue;
        if (!((R[u][v >> 6] >> (v & 63)) & 1ULL)) {
            cnt++;
            if (rndint(cnt) == 0) pick = v;
        }
    }
    return pick;
}

/* Join deficient opposite-side vertices. Never increases cost. */
static void fill_edges(void) {
    if (n < 2) return;
    for (int a = 0; a < n; a++) {
        if (col[a] != 0 || deg[a] >= d_) continue;
        int off = rndint(n);
        for (int k = 0; k < n && deg[a] < d_; k++) {
            int b = (k + off) % n;
            if (col[b] != 1 || deg[b] >= d_ || has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

/* Annealing on bad-pair cost. Returns 1 if cost reached 0. */
static int anneal(int iters, double T0, double T1) {
    long long cur = bad_cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && now_s() > t_end) break;
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        int a = -1, b = -1, c = -1, e = -1;
        if (rnd01() < 0.5) {
            Row *R = balls(D_);
            int u = rndint(n);
            int y = find_bad_partner(u, R);
            if (y >= 0 && col[u] != col[y] && deg[u] > 0 && deg[y] > 0) {
                int x = u;
                if (col[x] == 1) {
                    int t = x;
                    x = y;
                    y = t;
                }
                /* x on side 0, y on side 1: switch to make x-y an edge. */
                a = x;
                e = y;
                b = nb[x][rndint(deg[x])];
                c = nb[y][rndint(deg[y])];
            }
        }
        if (a < 0) {
            a = pick_vertex(0);
            if (a < 0) break;
            b = nb[a][rndint(deg[a])];
            c = pick_vertex(0);
            if (c < 0) break;
            e = nb[c][rndint(deg[c])];
        }
        if (c == a || has_edge(a, e) || has_edge(c, b)) continue;
        do_switch(a, b, c, e);
        long long nw = bad_cost();
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            do_switch(a, e, c, b);
        }
    }
    return cur == 0;
}

/* Insert a vertex on side c, joined to a greedy radius-(D-1) cover. */
static void insert_vertex(int c) {
    int old = n;
    Row *R = balls(D_ - 1);
    int W = (old + 63) >> 6;
    uint64_t covered[MAXW];
    static int chosen[MAXN];
    memset(covered, 0, sizeof covered);
    memset(chosen, 0, sizeof(int) * (size_t)old);
    int v = old;
    n = old + 1;
    col[v] = c;
    deg[v] = 0;
    for (int k = 0; k < d_; k++) {
        int best = -1;
        long long bs = -1;
        for (int s = 0; s < old; s++) {
            if (col[s] == c || chosen[s]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(R[s][w] & ~covered[w]);
            long long sc = (long long)g * 4096 + rndint(4096);
            if (sc > bs) {
                bs = sc;
                best = s;
            }
        }
        if (best < 0) break;
        chosen[best] = 1;
        for (int w = 0; w < W; w++) covered[w] |= R[best][w];
        if (deg[best] >= d_) {
            int t = nb[best][rndint(deg[best])];
            del_edge(best, t);
        }
        add_edge(best, v);
    }
}

/* Delete vertex x, moving the last vertex into its slot. */
static void remove_vertex(int x) {
    while (deg[x] > 0) del_edge(x, nb[x][0]);
    int last = n - 1;
    if (x != last) {
        for (int i = 0; i < deg[last]; i++) {
            int t = nb[last][i];
            for (int j = 0; j < deg[t]; j++) {
                if (nb[t][j] == last) {
                    nb[t][j] = x;
                    break;
                }
            }
        }
        memcpy(nb[x], nb[last], sizeof(int) * MAXD);
        deg[x] = deg[last];
        col[x] = col[last];
    }
    deg[last] = 0;
    n--;
}

/* Kill k vertices: one random vertex plus neighbours (cluster) or random vertices. */
static void kill_vertices(int k) {
    int ids[8];
    int m = 0;
    int v = rndint(n);
    ids[m++] = v;
    int cl = (int)(rnd64() & 1ULL);
    for (int tries = 0; m < k && tries < 100; tries++) {
        int u;
        if (cl && deg[v] > 0) u = nb[v][rndint(deg[v])];
        else u = rndint(n);
        int dup = 0;
        for (int i = 0; i < m; i++)
            if (ids[i] == u) dup = 1;
        if (!dup) ids[m++] = u;
    }
    for (int i = 1; i < m; i++) {
        int x = ids[i], j = i - 1;
        while (j >= 0 && ids[j] < x) {
            ids[j + 1] = ids[j];
            j--;
        }
        ids[j + 1] = x;
    }
    for (int i = 0; i < m; i++) remove_vertex(ids[i]);
}

static void save_snap(Snap *s) {
    s->n = n;
    memcpy(s->col, col, sizeof(int) * (size_t)n);
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->nb, nb, sizeof(int) * MAXD * (size_t)n);
}

static void load_snap(const Snap *s) {
    n = s->n;
    memcpy(col, s->col, sizeof(int) * (size_t)n);
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(nb, s->nb, sizeof(int) * MAXD * (size_t)n);
}

static int read_graph(void) {
    int N, M;
    if (scanf("%d %d", &N, &M) != 2) return 0;
    if (N <= 0 || N > MAXN || M < 0) return 0;
    n = N;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < M; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }
    return 1;
}

static int bipartition(void) {
    static int stk[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int top = 0;
        stk[top++] = s;
        while (top > 0) {
            int u = stk[--top];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stk[top++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Fallback: K_{d,d}, valid for D >= 2. */
static void set_complete(void) {
    n = 2 * d_;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = (v < d_) ? 0 : 1;
    }
    for (int a = 0; a < d_; a++)
        for (int b = d_; b < 2 * d_; b++) add_edge(a, b);
}

static int check_current(void) {
    for (int v = 0; v < n; v++) {
        if (deg[v] > d_) return 0;
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            if (u < 0 || u >= n || u == v || col[u] == col[v]) return 0;
            if (!has_edge(u, v)) return 0;
        }
    }
    return bad_cost() == 0;
}

static void print_current(void) {
    long long m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %lld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            if (nb[v][i] > v) printf("%d %d\n", v, nb[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = 88172645463325252ULL ^ (seed * 0x9E3779B97F4A7C15ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    t_end = now_s() + budget;

    if (d_ < 1 || d_ >= MAXD - 1 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    if (!read_graph() || n < 2 || !bipartition()) set_complete();
    if (bad_cost() != 0) anneal(30000, 1.0, 0.1);
    if (!check_current()) set_complete();

    save_snap(&SNAP_BEST);
    int best_n = n;

    while (now_s() < t_end) {
        if (n + 2 >= MAXN) break;
        save_snap(&SNAP_BAK);
        int cur_n = n;
        if (n < 12 || rndint(100) < 70) {
            /* Grow: insert one vertex and repair by annealing. */
            insert_vertex(rndint(2));
            fill_edges();
            if (!anneal(ITER_G, 0.5 + rnd01(), 0.12)) load_snap(&SNAP_BAK);
        } else {
            /* Kill-repair-regrow: remove 1-3 vertices, repair, then try two regrowths. */
            kill_vertices(1 + rndint(3));
            fill_edges();
            int ok = anneal(ITER_K, 0.5 + rnd01(), 0.12);
            if (ok) {
                for (int t = 0; t < 2; t++) {
                    save_snap(&SNAP_BAK2);
                    insert_vertex(rndint(2));
                    fill_edges();
                    if (!anneal(ITER_G, 0.5 + rnd01(), 0.12)) load_snap(&SNAP_BAK2);
                }
            }
            if (!ok || n + 1 < cur_n) load_snap(&SNAP_BAK);
        }
        if (bad_cost() != 0) load_snap(&SNAP_BAK);
        if (n > best_n) {
            best_n = n;
            save_snap(&SNAP_BEST);
        }
        if (n < best_n - 3) load_snap(&SNAP_BEST);
    }

    load_snap(&SNAP_BEST);
    if (!check_current()) set_complete();
    print_current();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, order is 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of a side."""
    if D < 2:
        return n, edges
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
            for attempt in range(100):
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
    """Join deficient opposite-side vertices in random order (only shortens distances)."""
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
    """On a point-line base (points first, lines second), add cross edges, keeping some slots free."""
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
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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
    """One randomized pipeline: twin duplication mixed with cover growth and saturation."""
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit - 1.0
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

    if D < 2 or best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base = None
    base_is_gq = False
    if D >= 4:
        base = _best_gq(d)
        base_is_gq = base is not None
    if base is None and D >= 3:
        base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        consider(*_grow(n0, e0, d, D, t0 + 0.10 * time_limit, rng))

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Randomized twin / growth pipelines (short).
    trial_end = t0 + 0.16 * time_limit
    tries = 0
    while time.monotonic() < trial_end and tries < 300:
        tries += 1
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # Spare-slot matching on the quadrangle base.
    if base_is_gq:
        spare_end = t0 + 0.22 * time_limit
        tries = 0
        while time.monotonic() < spare_end and tries < 200:
            tries += 1
            keep = rng.choice((0, 2, 4, 8, 12, 20))
            sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
            consider(*_grow(sn, se, d, D, spare_end, rng))

    # Main search in C, starting from the best valid graph found so far.
    remaining = hard_end - time.monotonic() - 0.5
    if remaining > 1.0 and best_n < lib.moore_bound(d, D):
        seed_c = int(seed) & 0xFFFFFFFF
        wall = t0 + 0.95 * time_limit - time.monotonic()
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed_c, f"{remaining:.2f}"],
                             stdin_graph=(best_n, best_e),
                             timeout=max(2.0, wall))
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
