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

#define MAXN 4096
#define DMAX 64
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][DMAX];
} State;

static State best, base;
static int nv, W, d_, D_;
static int adjv[MAXN][DMAX];
static int deg[MAXN];
static int colr[MAXN];
static uint64_t Ba[MAXN * MAXW], Bb[MAXN * MAXW], Bo[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static void shuffle(int *x, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static void setW(void) {
    W = (nv + 63) / 64;
    if (W < 1) W = 1;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Bitset balls of radius r on the live graph, written to Bo. */
static void balls(int r) {
    uint64_t *cu = Ba, *nx = Bb;
    memset(cu, 0, sizeof(uint64_t) * (size_t)nv * W);
    for (int v = 0; v < nv; v++) cu[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *dst = nx + (size_t)v * W;
            memcpy(dst, cu + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cu + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cu;
        cu = nx;
        nx = t;
    }
    memcpy(Bo, cu, sizeof(uint64_t) * (size_t)nv * W);
}

/* Number of unordered pairs at distance > D_ (unreachable counts). */
static long cost(void) {
    balls(D_);
    long bad = 0;
    for (int v = 0; v < nv; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(Bo[(size_t)v * W + w]);
        bad += nv - c;
    }
    return bad / 2;
}

static void save_state(State *s) {
    s->n = nv;
    memcpy(s->deg, deg, sizeof(int) * nv);
    memcpy(s->col, colr, sizeof(int) * nv);
    memcpy(s->adj, adjv, sizeof(int) * DMAX * nv);
}

static void load_state(const State *s) {
    nv = s->n;
    setW();
    memcpy(deg, s->deg, sizeof(int) * nv);
    memcpy(colr, s->col, sizeof(int) * nv);
    memcpy(adjv, s->adj, sizeof(int) * DMAX * nv);
}

static void build_complete(int d) {
    nv = 2 * d;
    setW();
    for (int v = 0; v < nv; v++) {
        deg[v] = 0;
        colr[v] = (v < d) ? 0 : 1;
    }
    for (int a = 0; a < d; a++)
        for (int b = d; b < 2 * d; b++) add_edge(a, b);
}

static int read_input(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 0 || n0 > MAXN / 2 || m0 < 0) return 0;
    nv = n0;
    setW();
    memset(deg, 0, sizeof(int) * nv);
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= nv || v >= nv || u == v) return 0;
        if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    for (int v = 0; v < nv; v++) colr[v] = -1;
    static int queue[MAXN];
    for (int s = 0; s < nv; s++) {
        if (colr[s] != -1) continue;
        colr[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adjv[x][i];
                if (colr[y] == -1) {
                    colr[y] = 1 - colr[x];
                    queue[qt++] = y;
                } else if (colr[y] == colr[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Random bipartite double-edge switch a-b, c-e -> a-e, c-b (a, c on side 0). */
static int pick_switch(const int *s0, int ns, int *pa, int *pb, int *pc, int *pe) {
    if (ns < 2) return 0;
    int a = s0[rndi(ns)], c = s0[rndi(ns)];
    if (a == c || deg[a] == 0 || deg[c] == 0) return 0;
    int b = adjv[a][rndi(deg[a])];
    int e = adjv[c][rndi(deg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
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

/* Anneal bipartite switches to drive the bad-pair count to zero. */
static int anneal(int iters, double T0, double dl) {
    static int s0[MAXN];
    int ns = 0;
    for (int v = 0; v < nv; v++)
        if (colr[v] == 0) s0[ns++] = v;
    long cu = cost();
    for (int it = 0; it < iters && cu > 0; it++) {
        if ((it & 127) == 0 && now_sec() > dl) break;
        double T = T0 * (1.0 - (double)it / iters) + 0.02;
        int a, b, c, e;
        if (!pick_switch(s0, ns, &a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        long nw = cost();
        long delta = nw - cu;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cu = nw;
        } else {
            undo_switch(a, b, c, e);
        }
    }
    return cu == 0;
}

/* Neutral walk: switches accepted only if the graph stays valid. */
static void plateau(int iters, double dl) {
    static int s0[MAXN];
    int ns = 0;
    for (int v = 0; v < nv; v++)
        if (colr[v] == 0) s0[ns++] = v;
    for (int it = 0; it < iters; it++) {
        if ((it & 63) == 0 && now_sec() > dl) break;
        int a, b, c, e;
        if (!pick_switch(s0, ns, &a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        if (cost() != 0) undo_switch(a, b, c, e);
    }
}

/* Add a vertex on `side` joined greedily to a cover of the other side's balls. */
static int add_vertex(int side) {
    if (nv + 1 >= MAXN) return 0;
    balls(D_ - 1);
    static uint64_t cov[MAXW];
    static char used[MAXN];
    memset(cov, 0, sizeof(uint64_t) * W);
    memset(used, 0, sizeof(char) * nv);
    int chosen[DMAX];
    int nc = 0;
    for (int k = 0; k < d_; k++) {
        int bu = -1;
        double bs = -1.0;
        for (int u = 0; u < nv; u++) {
            if (colr[u] != 1 - side || used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++)
                g += __builtin_popcountll(Bo[(size_t)u * W + w] & ~cov[w]);
            double sc = g + 1.5 * rndu();
            if (sc > bs) {
                bs = sc;
                bu = u;
            }
        }
        if (bu < 0) break;
        used[bu] = 1;
        chosen[nc++] = bu;
        for (int w = 0; w < W; w++) cov[w] |= Bo[(size_t)bu * W + w];
    }
    for (int i = 0; i < nc; i++) {
        int u = chosen[i];
        if (deg[u] >= d_) {
            int t = adjv[u][rndi(deg[u])];
            del_edge(u, t);
        }
    }
    int v = nv;
    nv++;
    setW();
    colr[v] = side;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) add_edge(chosen[i], v);
    return 1;
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < nv; v++) {
        if (deg[v] < d_) {
            if (colr[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        if (deg[a] >= d_) continue;
        for (int j = 0; j < nr && deg[a] < d_; j++) {
            int b = R[j];
            if (deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    rs ^= 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    if (d_ < 1) d_ = 1;
    if (d_ > DMAX) d_ = DMAX;
    if (D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    double dl = now_sec() + tl;

    if (!read_input()) build_complete(d_);
    setW();
    if (cost() != 0) {
        build_complete(d_);
        setW();
    }
    save_state(&best);

    while (now_sec() < dl) {
        save_state(&base);
        if (rndu() < 0.5) plateau(200, dl);
        if (!add_vertex(rndi(2))) break;
        fill();
        if (anneal(1500, 0.6, dl)) {
            if (nv > best.n) save_state(&best);
        } else {
            load_state(&base);
        }
    }

    load_state(&best);
    long m = 0;
    for (int v = 0; v < nv; v++) m += deg[v];
    m /= 2;
    printf("%d %ld\n", nv, m);
    for (int v = 0; v < nv; v++)
        for (int i = 0; i < deg[v]; i++)
            if (v < adjv[v][i]) printf("%d %d\n", v, adjv[v][i]);
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
    """Generalized quadrangle incidence graph W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
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
# Random voltage lifts of small d-regular bipartite base multigraphs.
# ----------------------------------------------------------------------------

def _random_lift(k, m, d, rng):
    """Random Z_m lift of a d-regular bipartite multigraph on k + k base vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append((i, k + perm[i], rng.randrange(m)))
    return lib.voltage_lift(2 * k, darts, m)


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _lift_search(d, D, deadline, rng, best_n, consider):
    """Search random voltage lifts slightly above best_n, repair them, then grow."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        if best_n >= moore:
            return
        k = rng.choice((1, 1, 2, 3))
        target = min(moore, best_n + rng.randint(1, 12))
        m = -(-target // (2 * k))
        if 2 * k * m > moore:
            m = moore // (2 * k)
        if m < 2 or 2 * k * m <= best_n:
            continue
        n, e = _random_lift(k, m, d, rng)
        adj = _to_sets(n, e)
        color = [0 if v < k * m else 1 for v in range(n)]
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(n) for v in adj[u] if u < v]
        consider(n, e3)
        n4, e4 = _grow(n, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n = n4


def _c_stage(d, D, n, edges, seed, budget, consider):
    """Run the C annealing engine from a valid start graph; keep its output if it is larger and valid."""
    text = lib.run_c(C_SOURCE, [d, D, int(seed), f"{budget:.2f}"],
                     stdin_graph=(n, list(edges)), timeout=budget + 4.0)
    cn, ce = lib.parse_graph_text(text)
    consider(cn, ce)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    try:
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
                grow_end = start + 0.08 * time_limit
                n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
                consider(n1, e1)

        # Randomized twin-duplication pipelines from the structured base.
        if D >= 2:
            trial_end = start + 0.15 * time_limit
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)

        # Random voltage lifts of small bipartite base multigraphs.
        if D >= 2:
            lift_end = start + 0.2 * time_limit
            _lift_search(d, D, lift_end, rng, best_n, consider)

        # C annealing stage: vertex insertion, plateau walks and repair from the best graph.
        if D >= 2 and best_n < moore:
            budget = 0.88 * time_limit - (time.monotonic() - start) - 3.0
            if budget >= 3.0:
                _c_stage(d, D, best_n, best_e, seed, budget, consider)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
