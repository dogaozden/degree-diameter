import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over bipartite graphs with degree <= d.
# State: any graph with degrees <= d. Cost = number of vertex pairs at distance
# > D. Moves: bipartite double-edge switches, greedy edge adds between deficient
# opposite-side vertices, and vertex growth (new vertex joined to d opposite
# vertices, stealing one edge from any saturated endpoint). Best valid graph is
# kept as a snapshot and restored after failed attempts.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64

static int dmax, DIAM, CAP, WMAX, n;
static unsigned char *A;
static int *nb, *deg, *side;
static uint64_t *bs1, *bs2;
static uint64_t rs;
static int bn, bm;
static int *bside, *beu, *bev;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long cost_bad(void) {
    int W = (n + 63) >> 6;
    uint64_t *cur = bs1, *nxt = bs2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *su = cur + (size_t)nb[(size_t)v * dmax + i] * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *x = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(x[w]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_e(int a, int b) { return A[(size_t)a * CAP + b]; }

static void add_edge(int a, int b) {
    nb[(size_t)a * dmax + deg[a]++] = b;
    nb[(size_t)b * dmax + deg[b]++] = a;
    A[(size_t)a * CAP + b] = 1;
    A[(size_t)b * CAP + a] = 1;
}

static void del_nb(int v, int u) {
    for (int i = 0; i < deg[v]; i++) {
        if (nb[(size_t)v * dmax + i] == u) {
            nb[(size_t)v * dmax + i] = nb[(size_t)v * dmax + deg[v] - 1];
            deg[v]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_nb(a, b);
    del_nb(b, a);
    A[(size_t)a * CAP + b] = 0;
    A[(size_t)b * CAP + a] = 0;
}

static void rep(int v, int old, int nw) {
    for (int i = 0; i < deg[v]; i++) {
        if (nb[(size_t)v * dmax + i] == old) {
            nb[(size_t)v * dmax + i] = nw;
            return;
        }
    }
}

/* Replace edges (a,b),(c,e) by (a,e),(c,b). a,c on side 0; b,e on side 1. */
static void swap_edges(int a, int b, int c, int e) {
    rep(a, b, e);
    rep(b, a, c);
    rep(c, e, b);
    rep(e, c, a);
    A[(size_t)a * CAP + b] = 0; A[(size_t)b * CAP + a] = 0;
    A[(size_t)c * CAP + e] = 0; A[(size_t)e * CAP + c] = 0;
    A[(size_t)a * CAP + e] = 1; A[(size_t)e * CAP + a] = 1;
    A[(size_t)c * CAP + b] = 1; A[(size_t)b * CAP + c] = 1;
}

static int pick_switch(int *pa, int *pb, int *pc, int *pe) {
    int a = -1, c = -1;
    for (int t = 0; t < 400 && a < 0; t++) {
        int x = rndint(n);
        if (side[x] == 0 && deg[x] > 0) a = x;
    }
    if (a < 0) return 0;
    for (int t = 0; t < 400 && c < 0; t++) {
        int x = rndint(n);
        if (side[x] == 0 && deg[x] > 0 && x != a) c = x;
    }
    if (c < 0) return 0;
    int b = nb[(size_t)a * dmax + rndint(deg[a])];
    int e = nb[(size_t)c * dmax + rndint(deg[c])];
    if (has_e(a, e) || has_e(c, b)) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}

static int try_add(void) {
    int a = -1, b = -1;
    for (int t = 0; t < 300 && a < 0; t++) {
        int x = rndint(n);
        if (side[x] == 0 && deg[x] < dmax) a = x;
    }
    if (a < 0) return 0;
    for (int t = 0; t < 300 && b < 0; t++) {
        int y = rndint(n);
        if (side[y] == 1 && deg[y] < dmax && !has_e(a, y)) b = y;
    }
    if (b < 0) return 0;
    add_edge(a, b);
    return 1;
}

static long anneal(int iters, double T) {
    long cur = cost_bad();
    for (int it = 0; it < iters && cur > 0; it++) {
        if (rndint(100) < 30) {
            if (try_add()) cur = cost_bad();
        } else {
            int a, b, c, e;
            if (!pick_switch(&a, &b, &c, &e)) continue;
            swap_edges(a, b, c, e);
            long nw = cost_bad();
            if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                swap_edges(a, e, c, b);
            }
        }
    }
    return cur;
}

static int grow_vertex(void) {
    if (n + 1 >= CAP || n < 2) return 0;
    int s = rndint(2);
    int v = n;
    int picked[MAXD];
    int cnt = 0;
    for (int tries = 0; cnt < dmax && tries < 2000; tries++) {
        int t = rndint(n);
        if (side[t] == s) continue;
        int dup = 0;
        for (int i = 0; i < cnt; i++) if (picked[i] == t) { dup = 1; break; }
        if (!dup) picked[cnt++] = t;
    }
    if (cnt == 0) return 0;
    n++;
    side[v] = s;
    deg[v] = 0;
    for (int i = 0; i < cnt; i++) {
        int t = picked[i];
        if (deg[t] >= dmax) {
            int x = nb[(size_t)t * dmax + rndint(deg[t])];
            remove_edge(t, x);
        }
        add_edge(v, t);
    }
    return 1;
}

static void snapshot(void) {
    bn = n;
    bm = 0;
    for (int v = 0; v < n; v++) bside[v] = side[v];
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[(size_t)v * dmax + i];
            if (u > v) { beu[bm] = v; bev[bm] = u; bm++; }
        }
    }
}

static void restore(void) {
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++)
            A[(size_t)v * CAP + nb[(size_t)v * dmax + i]] = 0;
        deg[v] = 0;
    }
    n = bn;
    for (int v = 0; v < n; v++) side[v] = bside[v];
    for (int i = 0; i < bm; i++) add_edge(beu[i], bev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 88172645463325252ULL;
    double limit = atof(argv[4]);
    for (int i = 0; i < 20; i++) rnd64();

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2 || n_in <= 0 || m_in < 0 ||
        dmax < 1 || dmax > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *dg = calloc((size_t)n_in, sizeof(int));
    for (int i = 0; i < m_in; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
        if (eu[i] < 0 || ev[i] < 0 || eu[i] >= n_in || ev[i] >= n_in || eu[i] == ev[i]) {
            printf("0 0\n");
            return 0;
        }
        dg[eu[i]]++;
        dg[ev[i]]++;
    }
    for (int v = 0; v < n_in; v++) {
        if (dg[v] > dmax) { printf("0 0\n"); return 0; }
    }

    n = n_in;
    CAP = n_in + n_in / 2 + 128;
    WMAX = (CAP + 63) / 64;
    A = calloc((size_t)CAP * CAP, 1);
    nb = calloc((size_t)CAP * dmax, sizeof(int));
    deg = calloc((size_t)CAP, sizeof(int));
    side = calloc((size_t)CAP, sizeof(int));
    bside = calloc((size_t)CAP, sizeof(int));
    bs1 = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    bs2 = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    beu = calloc((size_t)CAP * dmax + 1, sizeof(int));
    bev = calloc((size_t)CAP * dmax + 1, sizeof(int));

    for (int i = 0; i < m_in; i++) {
        if (!has_e(eu[i], ev[i])) add_edge(eu[i], ev[i]);
    }

    int *qu = malloc(sizeof(int) * (size_t)CAP);
    for (int v = 0; v < n; v++) side[v] = -1;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail && ok) {
            int u = qu[head++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[(size_t)u * dmax + i];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    qu[tail++] = w;
                } else if (side[w] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    snapshot();

    clock_t t0 = clock();
    const int iters = 1500;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < limit) {
        restore();
        int grow = rndint(10) < 7;
        int good = 0;
        if (grow) {
            good = grow_vertex();
        } else {
            int k = 2 + rndint(6);
            for (int i = 0; i < k; i++) {
                int a, b, c, e;
                if (pick_switch(&a, &b, &c, &e)) swap_edges(a, b, c, e);
            }
            good = 1;
        }
        if (!good) continue;
        long res = anneal(iters, 0.35);
        if (res == 0) {
            if (n > bn || (!grow && n == bn)) snapshot();
        }
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", beu[i], bev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """Dense structured graph with degree at least d, later thinned into a valid graph."""
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


def _cover_search(cands, ball, full, d, rng, iters, deadline):
    """Local search for a cover of `full` by at most d candidates (swap moves with light annealing)."""
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
            for attempt in range(120):
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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
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
# Thin a dense structured graph into a valid one.
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
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
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
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
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


# ----------------------------------------------------------------------------
# Driver. Python phases use fractions of time_limit up to 0.42; the C annealer
# then starts from the best valid graph and runs until about 0.90 of time_limit.
# Every candidate passes lib.is_valid before it is kept; haar_graph(d, d) is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    TL = float(time_limit)

    def at(f):
        return start + f * TL

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured small base, grown by cover vertices.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.06), rng)
            consider(n1, e1)

    if best_n >= target:
        return best_n, list(best_e)

    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
        _lns(best_n, best_e, d, D, at(0.18), rng, consider)

    # Phase B: thinned dense graph, repeated.
    if D >= 2 and time.monotonic() < at(0.26) and best_n < target:
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.26):
                r = _deletion_trial(d, D, rn, re, rng, at(0.26))
                if r is None:
                    break
                consider(*r)

    # Phase C: LNS from the best valid graph.
    if D >= 2 and time.monotonic() < at(0.34) and best_n < target:
        _lns(best_n, best_e, d, D, at(0.34), rng, consider)

    # Phase D: prune redundant edges and regrow.
    if D >= 2 and time.monotonic() < at(0.42) and best_n < target:
        _prune_regrow(best_n, best_e, d, D, at(0.42), rng, consider)

    # Phase E: C annealing from the best graph found so far.
    if D >= 2 and best_n < target:
        budget = 0.90 * TL - (time.monotonic() - start) - 2.5
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 3.0)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
