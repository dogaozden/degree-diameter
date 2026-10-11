import itertools
import math
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

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)
#define ATT_ITERS 1200

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN * MAXD];
} Graph;

static Graph G, CUR, WORK, BEST;
static int DD, DIAM;
static int have_best = 0;
static clock_t DEADLINE;
static uint64_t rs = 88172645463325252ULL;
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static int candA[MAXN], candB[MAXN], stk[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const Graph *g, int a, int b) {
    const int *p = g->adj + a * DD;
    for (int k = 0; k < g->deg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void add_arc(Graph *g, int a, int b) {
    g->adj[a * DD + g->deg[a]] = b;
    g->deg[a]++;
}

static void rem_arc(Graph *g, int a, int b) {
    int *p = g->adj + a * DD;
    for (int k = 0; k < g->deg[a]; k++) {
        if (p[k] == b) {
            p[k] = p[g->deg[a] - 1];
            g->deg[a]--;
            return;
        }
    }
}

static void add_edge(Graph *g, int a, int b) {
    add_arc(g, a, b);
    add_arc(g, b, a);
}

static void del_edge(Graph *g, int a, int b) {
    rem_arc(g, a, b);
    rem_arc(g, b, a);
}

static long long bad_pairs(const Graph *g) {
    int n = g->n;
    int W = (n + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        cur[v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + v * W;
            memcpy(o, cur + v * W, sizeof(uint64_t) * (size_t)W);
            const int *p = g->adj + v * DD;
            for (int k = 0; k < g->deg[v]; k++) {
                const uint64_t *s = cur + p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static int color_ok(Graph *g) {
    int n = g->n;
    for (int v = 0; v < n; v++) g->col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (g->col[s] != -1) continue;
        g->col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < g->deg[u]; k++) {
                int w = g->adj[u * DD + k];
                if (g->col[w] == -1) {
                    g->col[w] = 1 - g->col[u];
                    stk[sp++] = w;
                } else if (g->col[w] == g->col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int pick0(const Graph *g) {
    for (long t = 0; t < 10000000L; t++) {
        int v = rndint(g->n);
        if (g->col[v] == 0 && g->deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving bipartite double-edge switch: a-b, c-e -> a-e, c-b. */
static int switch_move(Graph *g, int *o) {
    int a = pick0(g), c = pick0(g);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = g->adj[a * DD + rndint(g->deg[a])];
    int e = g->adj[c * DD + rndint(g->deg[c])];
    if (b == e) return 0;
    if (has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    del_edge(g, a, b);
    del_edge(g, c, e);
    add_edge(g, a, e);
    add_edge(g, c, b);
    o[0] = a; o[1] = b; o[2] = c; o[3] = e;
    return 1;
}

static void undo_switch(Graph *g, const int *o) {
    int a = o[0], b = o[1], c = o[2], e = o[3];
    del_edge(g, a, e);
    del_edge(g, c, b);
    add_edge(g, a, b);
    add_edge(g, c, e);
}

static void shuffle_arr(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add a vertex on the side opposite to a random side c, joined to up to DD
   vertices of side c. Full vertices give up one random edge to make room. */
static int insert_vertex(Graph *g) {
    if (g->n >= MAXN - 1) return 0;
    int c = rndint(2);
    int nd = 0, nf = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->col[v] != c) continue;
        if (g->deg[v] < DD) candA[nd++] = v;
        else candB[nf++] = v;
    }
    shuffle_arr(candA, nd);
    shuffle_arr(candB, nf);
    int v = g->n++;
    g->col[v] = 1 - c;
    g->deg[v] = 0;
    int chosen = 0;
    for (int i = 0; i < nd && chosen < DD; i++) {
        add_edge(g, v, candA[i]);
        chosen++;
    }
    for (int i = 0; i < nf && chosen < DD; i++) {
        int w = candB[i];
        int x = g->adj[w * DD + rndint(g->deg[w])];
        del_edge(g, w, x);
        add_edge(g, v, w);
        chosen++;
    }
    return 1;
}

static long long anneal(Graph *g, long iters, double T, long long cur, clock_t stop) {
    int o[4];
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && clock() > stop) break;
        if (!switch_move(g, o)) continue;
        long long nw = bad_pairs(g);
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nw;
        else undo_switch(g, o);
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x12345ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    if (DD < 1 || DD > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n >= MAXN - 1 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    memset(&G, 0, sizeof(G));
    G.n = n;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; continue; }
        if (has_edge(&G, u, v)) continue;
        if (G.deg[u] >= DD || G.deg[v] >= DD) { ok = 0; continue; }
        add_edge(&G, u, v);
    }
    if (!ok || !color_ok(&G)) {
        printf("0 0\n");
        return 0;
    }

    DEADLINE = clock() + (clock_t)(tl * CLOCKS_PER_SEC);
    long long cc = bad_pairs(&G);
    if (cc > 0) {
        clock_t stop = clock() + (clock_t)(tl * 0.25 * CLOCKS_PER_SEC);
        cc = anneal(&G, 1000000000L, 0.4, cc, stop);
    }
    if (cc == 0) {
        CUR = G;
        BEST = G;
        have_best = 1;
    }

    if (have_best) {
        while (clock() < DEADLINE) {
            WORK = CUR;
            if (rndint(10) < 8) {
                insert_vertex(&WORK);
            } else {
                int o[4];
                for (int k = 0; k < 20; k++) switch_move(&WORK, o);
            }
            long long c = bad_pairs(&WORK);
            double T = 0.25 + 0.5 * rnd01();
            c = anneal(&WORK, ATT_ITERS, T, c, DEADLINE);
            if (c == 0) {
                CUR = WORK;
                if (CUR.n > BEST.n) BEST = CUR;
            }
            if (CUR.n + 4 < BEST.n) CUR = BEST;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    long long total = 0;
    for (int v = 0; v < BEST.n; v++) total += BEST.deg[v];
    printf("%d %lld\n", BEST.n, total / 2);
    for (int v = 0; v < BEST.n; v++) {
        for (int k = 0; k < BEST.deg[v]; k++) {
            int u = BEST.adj[v * DD + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
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
    """Dense structured graph with degree at least d, to be thinned into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _greedy_cover(cands, ball, full, d, rng, randomize):
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 steps."""
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
# Thinning a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

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
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Voltage lifts over small (possibly non-abelian) groups, annealed to diameter D.
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples: cyclic plus Z_M x|_r Z_k with M*k = G."""
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        M = G // k
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline):
    darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    temp = 0.6
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        old = list(darts)
        k = len(darts)
        if k >= 2 and rng.random() < 0.5:
            p = rng.randrange(k)
            q = rng.randrange(k)
            if p == q:
                continue
            ip, jp, gp = darts[p]
            iq, jq, gq = darts[q]
            darts[p] = (ip, jq, gp)
            darts[q] = (iq, jp, gq)
        else:
            p = rng.randrange(k)
            i, j, _ = darts[p]
            darts[p] = (i, j, rng.randrange(G))
        n2, e2 = lib.group_lift(2 * s, darts, G, mul)
        new = _cost(_to_sets(n2, e2), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            n, e = n2, e2
        else:
            darts = old
        temp = max(0.05, temp * 0.999)
    return n, e


def _lift_phase(d, D, get_best, deadline, rng, consider):
    while time.monotonic() < deadline:
        best_n = get_best()
        s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
        G_min = best_n // (2 * s) + 1
        G = G_min + rng.randrange(4)
        opts = _group_options(G)
        if not opts:
            continue
        M, k, r = rng.choice(opts)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res = _lift_search(d, D, s, G, mul, rng, slice_end)
        if res is not None:
            n, e = res
            consider(n, e)
            n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
            consider(n2, e2)


# ----------------------------------------------------------------------------
# C annealing polish: degree-preserving switches plus vertex insertion.
# ----------------------------------------------------------------------------

def _c_polish(d, D, n, edges, seed, budget):
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                     stdin_graph=(n, edges), timeout=budget + 5.0)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Driver. Fractions of span = 0.88 * time_limit:
#   A  structured base grown, twin/grow trials          (to 0.15)
#   L  voltage lifts over small groups                  (to 0.25)
#   B  thinned dense graph                              (to 0.33)
#   C  C annealing from the best valid graph            (to 1.00)
# Every kept graph passes lib.is_valid. K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    span = 0.88 * time_limit

    def at(f):
        return t0 + f * span

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
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A: structured base, grown, then trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.05), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts.
    if D >= 2 and time.monotonic() < at(0.25):
        _lift_phase(d, D, lambda: best_n, at(0.25), rng, consider)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.33):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.33):
                r = _deletion_trial(d, D, rn, re, rng, at(0.33))
                if r is None:
                    break
                consider(*r)

    # Phase C: C annealing from the best valid graph, leaving a margin.
    if D >= 2 and d <= 32 and best_n > 0:
        budget = at(1.0) - time.monotonic() - 1.5
        if budget > 1.0:
            try:
                n, e = _c_polish(d, D, best_n, best_e, seed, budget)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
