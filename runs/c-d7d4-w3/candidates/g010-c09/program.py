"""Structured bases (W(q), PG(2,q)) grown by twin duplication and cover extension,
followed by a C insertion-annealing engine.

New in this version: the C engine (C_SOURCE) grows a bipartite graph one vertex at a
time. Each new vertex is joined to d opposite-side vertices, rewiring existing edges
when those vertices are full. Degree-preserving bipartite switches and
deficiency-transferring rewires then anneal the cost (number of vertex pairs at distance
greater than D) to zero. Failed attempts roll back to the last valid snapshot.
"""
import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 64
#define ITERS 6000
#define TEMP 0.35

typedef uint64_t u64;

static int d_, D_, n;
static int col[MAXN], deg[MAXN], adj[MAXN][MAXD];
static int snap_n, snap_col[MAXN], snap_deg[MAXN], snap_adj[MAXN][MAXD];
static u64 bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static u64 rs = 88172645463325252ULL;
static double tlimit = 10.0;
static clock_t c0;
static time_t w0;
static int undo_type, ua, ub, uc, ue;
static int defs[MAXN];

static u64 rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndint(int k) { return (int)(rnd() % (u64)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pop64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int time_up(void) {
    double cpu = (double)(clock() - c0) / CLOCKS_PER_SEC;
    if (cpu >= tlimit) return 1;
    if (difftime(time(NULL), w0) >= tlimit + 1.0) return 1;
    return 0;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_one(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Number of unordered vertex pairs at distance greater than D_. */
static long long cost_state(void) {
    int W = (n + 63) >> 6;
    u64 (*cur)[MAXW] = bufA;
    u64 (*nxt)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        u64 (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pop64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_snap(void) {
    snap_n = n;
    memcpy(snap_col, col, sizeof(int) * n);
    memcpy(snap_deg, deg, sizeof(int) * n);
    for (int v = 0; v < n; v++)
        memcpy(snap_adj[v], adj[v], sizeof(int) * deg[v]);
}

static void load_snap(void) {
    n = snap_n;
    memcpy(col, snap_col, sizeof(int) * n);
    memcpy(deg, snap_deg, sizeof(int) * n);
    for (int v = 0; v < n; v++)
        memcpy(adj[v], snap_adj[v], sizeof(int) * deg[v]);
}

/* Add edges between deficient opposite-side vertices in random order. */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d_) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d_; j++) {
            int b = R[j];
            if (deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Insert a new vertex on a random side, joined to up to d_ opposite-side vertices.
   Full vertices give up one random edge to their partner, which becomes deficient. */
static int insert_vertex(void) {
    if (n >= MAXN - 1) return 0;
    int c = rndint(2);
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] != c) cand[nc++] = u;
    if (nc == 0) return 0;
    shuffle_int(cand, nc);
    int v = n++;
    col[v] = c;
    deg[v] = 0;
    int k = d_ < nc ? d_ : nc;
    int chosen = 0;
    for (int pass = 0; pass < 2 && chosen < k; pass++) {
        for (int i = 0; i < nc && chosen < k; i++) {
            int u = cand[i];
            int def = deg[u] < d_;
            if ((pass == 0) != def) continue;
            if (!def) {
                int w = adj[u][rndint(deg[u])];
                del_edge(u, w);
            }
            add_edge(v, u);
            chosen++;
        }
    }
    fill_edges();
    return 1;
}

static int pick_vertex_with_deg(void) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(n);
        if (deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving bipartite double-edge switch. */
static int move_switch(void) {
    int a = pick_vertex_with_deg();
    if (a < 0) return 0;
    int b = adj[a][rndint(deg[a])];
    if (col[a] == 1) { int t = a; a = b; b = t; }
    int c = pick_vertex_with_deg();
    if (c < 0) return 0;
    int e = adj[c][rndint(deg[c])];
    if (col[c] == 1) { int t = c; c = e; e = t; }
    if (c == a || e == b) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    undo_type = 1; ua = a; ub = b; uc = c; ue = e;
    return 1;
}

/* Move one edge end from a full vertex to a deficient vertex on the same side. */
static int move_rewire(void) {
    int a = pick_vertex_with_deg();
    if (a < 0) return 0;
    int b = adj[a][rndint(deg[a])];
    if (col[a] == 1) { int t = a; a = b; b = t; }
    int nd = 0;
    for (int x = 0; x < n; x++)
        if (col[x] == col[b] && x != b && deg[x] < d_ && !has_edge(a, x))
            defs[nd++] = x;
    if (nd == 0) return 0;
    int x = defs[rndint(nd)];
    del_edge(a, b);
    add_edge(a, x);
    undo_type = 2; ua = a; ub = b; uc = x;
    return 1;
}

static void undo_move(void) {
    if (undo_type == 1) {
        del_edge(ua, ue);
        del_edge(uc, ub);
        add_edge(ua, ub);
        add_edge(uc, ue);
    } else if (undo_type == 2) {
        del_edge(ua, uc);
        add_edge(ua, ub);
    }
}

/* Simulated annealing on the bad-pair cost. Returns the final cost (0 means valid). */
static long long anneal(int iters, double T) {
    long long cur = cost_state();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && time_up()) break;
        int moved;
        if (rndint(100) < 25) moved = move_rewire();
        else moved = move_switch();
        if (!moved) continue;
        long long nw = cost_state();
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nw;
        else undo_move();
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    tlimit = atof(argv[4]);
    c0 = clock();
    w0 = time(NULL);

    if (d_ < 1 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }

    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n == 0) {
        n = 2 * d_;
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++)
                add_edge(i, d_ + j);
    } else {
        if (n < 0 || n > MAXN - 2) {
            printf("0 0\n");
            return 0;
        }
        for (int i = 0; i < m; i++) {
            int a, b;
            if (scanf("%d %d", &a, &b) != 2) {
                printf("0 0\n");
                return 0;
            }
            if (a < 0 || b < 0 || a >= n || b >= n || a == b ||
                deg[a] >= d_ || deg[b] >= d_ || has_edge(a, b)) {
                printf("0 0\n");
                return 0;
            }
            add_edge(a, b);
        }
    }

    /* Bipartition by BFS; the input must be bipartite. */
    static int queue[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt && ok) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    queue[qt++] = w;
                } else if (col[w] == col[u]) {
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

    if (cost_state() > 0) {
        long long c = anneal(ITERS * 20, TEMP);
        if (c > 0) {
            printf("0 0\n");
            return 0;
        }
    }

    save_snap();
    while (!time_up()) {
        if (!insert_vertex()) break;
        long long c = anneal(ITERS, TEMP);
        if (c == 0) save_snap();
        else load_snap();
    }

    int cnt = 0;
    for (int v = 0; v < snap_n; v++)
        for (int k = 0; k < snap_deg[v]; k++)
            if (snap_adj[v][k] > v) cnt++;
    printf("%d %d\n", snap_n, cnt);
    for (int v = 0; v < snap_n; v++)
        for (int k = 0; k < snap_deg[v]; k++)
            if (snap_adj[v][k] > v)
                printf("%d %d\n", v, snap_adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """Dense structured graph with degree at least d, used as a thinning source."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared helpers.
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


def _cover_search(cands, ball, full, d, rng, iters, deadline):
    """Swap-based local search for a cover of `full` by at most d candidates."""
    if not cands:
        return None
    k = min(d, len(cands))
    cur = rng.sample(cands, k)

    def cov(S):
        c = 0
        for s in S:
            c |= ball[s]
        return c

    cur_cov = cov(cur)
    cur_score = cur_cov.bit_count()
    for it in range(iters):
        if cur_cov == full:
            return cur
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        inn = rng.choice(cands)
        if inn in cur:
            continue
        trial = cur[:]
        trial[i] = inn
        t_cov = cov(trial)
        t_score = t_cov.bit_count()
        if t_score >= cur_score or rng.random() < 0.02:
            cur, cur_cov, cur_score = trial, t_cov, t_score
    return cur if cur_cov == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods cover deficient vertices."""
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
            if not chosen and time.monotonic() < deadline:
                chosen = _cover_search(cands, ball, full, d, rng, 1500, deadline)
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


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
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


def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# C insertion-annealing engine.
# ----------------------------------------------------------------------------

def _c_engine(n, edges, d, D, seed, budget):
    """Run the C engine from a valid start graph. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                        stdin_graph=(n, edges), timeout=budget + 8.0)
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None


# ----------------------------------------------------------------------------
# Driver. Python builds structured starts for the first ~25% of the budget;
# C insertion-annealing uses the rest. Every candidate passes lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(3.0, 0.85 * time_limit - 1.5)
    deadline = start + total

    def at(f):
        return start + f * total

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

    # Phase A: structured base, grown, then twin trials.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense graph for diversity.
    if D >= 2 and time.monotonic() < at(0.25):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.25):
                r = _deletion_trial(d, D, rn, re, rng, at(0.25))
                if r is None:
                    break
                consider(*r)

    # Phase C: C insertion-annealing from the best valid graph.
    if D >= 2:
        budget = deadline - time.monotonic() - 1.0
        if budget > 1.0:
            res = _c_engine(best_n, best_e, d, D, seed, budget)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
