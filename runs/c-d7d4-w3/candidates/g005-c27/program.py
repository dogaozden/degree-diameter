import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: degree-preserving bipartite switch annealing with vertex
# growth. It starts from a valid graph, adds one vertex (both sides alternate
# by random colour), repairs the diameter by annealing double-edge switches,
# and keeps the result only when the bad-pair cost reaches 0.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64

static int d_, D_;
static int n_, cap_, best_n_;
static int *deg_, *nb_, *col_, *bcol_;
static unsigned char *mat_;
static uint64_t *bufA_, *bufB_;
static int *bu_, *bv_, bm_;
static int *L0_;
static uint64_t rs_ = 88172645463325252ULL;
static double deadline_;
static clock_t t0_;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double elapsed(void) {
    return (double)(clock() - t0_) / CLOCKS_PER_SEC;
}

static void nb_add(int v, int u) {
    nb_[v * MAXD + deg_[v]] = u;
    deg_[v]++;
}

static void nb_del(int v, int u) {
    int *a = &nb_[v * MAXD];
    for (int k = 0; k < deg_[v]; k++) {
        if (a[k] == u) {
            a[k] = a[deg_[v] - 1];
            deg_[v]--;
            return;
        }
    }
}

static void add_edge(int x, int y) {
    nb_add(x, y);
    nb_add(y, x);
    mat_[(size_t)x * cap_ + y] = 1;
    mat_[(size_t)y * cap_ + x] = 1;
}

static void del_edge(int x, int y) {
    nb_del(x, y);
    nb_del(y, x);
    mat_[(size_t)x * cap_ + y] = 0;
    mat_[(size_t)y * cap_ + x] = 0;
}

/* remove (x,y),(z,w); add (x,w),(z,y). Degrees are unchanged. */
static void sw(int x, int y, int z, int w) {
    del_edge(x, y);
    del_edge(z, w);
    add_edge(x, w);
    add_edge(z, y);
}

/* Number of unordered pairs at distance > D_ (unreachable pairs count). */
static long long cost(void) {
    int n = n_;
    size_t W = (size_t)((n + 63) >> 6);
    uint64_t *cur = bufA_, *nxt = bufB_;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + ((size_t)v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < D_; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *o = cur + (size_t)nb_[v * MAXD + k] * W;
                for (size_t w = 0; w < W; w++) dst[w] |= o[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *src = cur + (size_t)v * W;
        int c = 0;
        for (size_t w = 0; w < W; w++) c += popc64(src[w]);
        bad += n - c;
    }
    return bad / 2;
}

static void snapshot(void) {
    best_n_ = n_;
    bm_ = 0;
    for (int v = 0; v < n_; v++) {
        bcol_[v] = col_[v];
        for (int k = 0; k < deg_[v]; k++) {
            int u = nb_[v * MAXD + k];
            if (v < u) {
                bu_[bm_] = v;
                bv_[bm_] = u;
                bm_++;
            }
        }
    }
}

static void restore(void) {
    n_ = best_n_;
    memset(deg_, 0, sizeof(int) * (size_t)cap_);
    memset(mat_, 0, (size_t)cap_ * cap_);
    for (int v = 0; v < n_; v++) col_[v] = bcol_[v];
    for (int i = 0; i < bm_; i++) add_edge(bu_[i], bv_[i]);
}

/* Add vertex v = n_ on colour 1-c, joined to d_ vertices of colour c.
   A full neighbour gives up one edge to a vertex of colour 1-c. */
static int grow_vertex(void) {
    if (n_ >= cap_) return 0;
    int c = rndint(2);
    int *cand = malloc(sizeof(int) * (size_t)(n_ + 1));
    int *ord = malloc(sizeof(int) * (size_t)(n_ + 1));
    int nc = 0;
    for (int u = 0; u < n_; u++)
        if (col_[u] == c) cand[nc++] = u;
    if (nc < d_) {
        free(cand);
        free(ord);
        return 0;
    }
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int no = 0;
    for (int i = 0; i < nc; i++)
        if (deg_[cand[i]] < d_) ord[no++] = cand[i];
    for (int i = 0; i < nc; i++)
        if (deg_[cand[i]] >= d_) ord[no++] = cand[i];
    int v = n_++;
    col_[v] = 1 - c;
    deg_[v] = 0;
    for (int i = 0; i < d_; i++) {
        int u = ord[i];
        if (deg_[u] >= d_) {
            int w = nb_[u * MAXD + rndint(deg_[u])];
            del_edge(u, w);
        }
        add_edge(u, v);
    }
    free(cand);
    free(ord);
    return 1;
}

/* Add cross-colour edges between spare vertices (never increases the cost). */
static void fill(void) {
    int *s0 = malloc(sizeof(int) * (size_t)(n_ + 1));
    int *s1 = malloc(sizeof(int) * (size_t)(n_ + 1));
    int n0 = 0, n1 = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] >= d_) continue;
        if (col_[v] == 0) s0[n0++] = v;
        else s1[n1++] = v;
    }
    for (int i = n0 - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = s0[i]; s0[i] = s0[j]; s0[j] = t;
    }
    for (int i = n1 - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = s1[i]; s1[i] = s1[j]; s1[j] = t;
    }
    for (int i = 0; i < n0; i++) {
        int a = s0[i];
        for (int j = 0; j < n1 && deg_[a] < d_; j++) {
            int b = s1[j];
            if (deg_[b] < d_ && !mat_[(size_t)a * cap_ + b]) add_edge(a, b);
        }
    }
    free(s0);
    free(s1);
}

/* Anneal switches until cost 0. Returns 1 on success. */
static int anneal(long long iters, double T0) {
    long long cur = cost();
    if (cur == 0) return 1;
    int nl0 = 0;
    for (int v = 0; v < n_; v++)
        if (col_[v] == 0 && deg_[v] > 0) L0_[nl0++] = v;
    if (nl0 < 2) return 0;
    for (long long it = 0; it < iters; it++) {
        if ((it & 63) == 0 && elapsed() > deadline_) return 0;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.03;
        int a = L0_[rndint(nl0)];
        int c = L0_[rndint(nl0)];
        if (a == c) continue;
        int b = nb_[a * MAXD + rndint(deg_[a])];
        int e = nb_[c * MAXD + rndint(deg_[c])];
        if (b == e) continue;
        if (mat_[(size_t)a * cap_ + e] || mat_[(size_t)c * cap_ + b]) continue;
        sw(a, b, c, e);
        long long nw = cost();
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            sw(a, e, c, b);
        }
    }
    return cur == 0;
}

static void print_best(void) {
    printf("%d %d\n", best_n_, bm_);
    for (int i = 0; i < bm_; i++) printf("%d %d\n", bu_[i], bv_[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x12345ULL;
    if (rs_ == 0) rs_ = 1;
    double tl = atof(argv[4]);
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0) {
        printf("1 0\n");
        return 0;
    }
    if (d_ < 1 || d_ >= MAXD || D_ < 1) {
        printf("1 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int mm = 0;
    for (int i = 0; i < m; i++) {
        int x, y;
        if (scanf("%d %d", &x, &y) != 2) break;
        eu[mm] = x;
        ev[mm] = y;
        mm++;
    }

    cap_ = n + 600;
    size_t Wc = (size_t)((cap_ + 63) >> 6);
    deg_ = calloc((size_t)cap_, sizeof(int));
    nb_ = calloc((size_t)cap_ * MAXD, sizeof(int));
    col_ = calloc((size_t)cap_, sizeof(int));
    bcol_ = calloc((size_t)cap_, sizeof(int));
    mat_ = calloc((size_t)cap_ * cap_, 1);
    bufA_ = calloc((size_t)cap_ * Wc, sizeof(uint64_t));
    bufB_ = calloc((size_t)cap_ * Wc, sizeof(uint64_t));
    bu_ = calloc((size_t)cap_ * MAXD, sizeof(int));
    bv_ = calloc((size_t)cap_ * MAXD, sizeof(int));
    L0_ = calloc((size_t)cap_, sizeof(int));
    int *q = calloc((size_t)cap_, sizeof(int));

    n_ = n;
    for (int i = 0; i < mm; i++) {
        int x = eu[i], y = ev[i];
        if (x < 0 || y < 0 || x >= n || y >= n || x == y) continue;
        if (mat_[(size_t)x * cap_ + y]) continue;
        if (deg_[x] >= d_ || deg_[y] >= d_) continue;
        add_edge(x, y);
    }
    for (int v = 0; v < n; v++) col_[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col_[s] >= 0) continue;
        col_[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < deg_[u]; k++) {
                int w = nb_[u * MAXD + k];
                if (col_[w] < 0) {
                    col_[w] = 1 - col_[u];
                    q[qt++] = w;
                }
            }
        }
    }

    t0_ = clock();
    deadline_ = tl * 0.9 - 0.3;
    snapshot();
    const long long ITERS = 30000;
    while (elapsed() < deadline_ && n_ < cap_) {
        restore();
        if (!grow_vertex()) break;
        fill();
        if (anneal(ITERS, 1.5)) snapshot();
    }
    print_best();
    return 0;
}
'''


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
    """Dense structured graph (degree >= d) to be thinned into a valid graph."""
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


# ----------------------------------------------------------------------------
# Twin duplication keeps distances and bipartiteness.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
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
# Bipartite voltage lifts over small groups (resumable annealing).
# ----------------------------------------------------------------------------

def _group_options(G):
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


def _lift_search(d, D, s, G, mul, rng, deadline, darts=None, temp=0.6):
    if darts is None:
        darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    while cur > 0:
        if time.monotonic() > deadline:
            return None, darts, temp
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
    return (n, e), darts, temp


def _lift_phase(d, D, get_best, deadline, rng, consider):
    states = {}
    while time.monotonic() < deadline:
        best_n = get_best()
        states = {key: v for key, v in states.items() if 2 * key[0] * key[1] > best_n}
        if states and rng.random() < 0.7:
            key = rng.choice(list(states))
            darts, temp = states.pop(key)
            s, G, M, k, r = key
        else:
            darts, temp = None, 0.6
            s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
            G_min = best_n // (2 * s) + 1
            G = G_min + rng.randrange(4)
            opts = _group_options(G)
            if not opts:
                continue
            M, k, r = rng.choice(opts)
            key = (s, G, M, k, r)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res, darts, temp = _lift_search(d, D, s, G, mul, rng, slice_end, darts, temp)
        if res is None:
            states[key] = (darts, temp)
            if len(states) > 40:
                states.pop(next(iter(states)))
            continue
        n, e = res
        consider(n, e)
        n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
        consider(n2, e2)


# ----------------------------------------------------------------------------
# Redundant-edge pruning and regrowth.
# ----------------------------------------------------------------------------

def _prune_redundant(n, edges, D, rng, deadline, max_tests):
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
# Run the C engine. Any failure (compile, runtime, parse) returns None so the
# Python result stays in place.
# ----------------------------------------------------------------------------

def _c_engine(d, D, seed, n, edges, budget):
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 5.0)
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.85 * time_limit:
#   A  structured base (W(q) or PG(2,q)), grown, then twin trials
#   L  voltage lifts over small groups
#   B  thinned dense graph (degree reduction and vertex deletion)
#   C  C annealing engine grows the best valid graph
#   D  Python redundant-edge pruning and regrowth
# Every kept graph passes lib.is_valid. The Haar graph is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

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

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A: structured base, grown, then twin trials.
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
        n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
        consider(n1, e1)
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts.
    if D >= 2 and time.monotonic() < at(0.30):
        _lift_phase(d, D, lambda: best_n, at(0.30), rng, consider)
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.35):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.35):
                r = _deletion_trial(d, D, rn, re, rng, at(0.35))
                if r is None:
                    break
                consider(*r)

    # Phase C: C annealing engine from the best valid graph.
    if D >= 2 and time.monotonic() < at(0.88):
        budget = at(0.88) - time.monotonic()
        if budget > 1.0:
            res = _c_engine(d, D, seed, best_n, best_e, budget)
            if res is not None:
                consider(*res)

    # Phase D: prune redundant edges and regrow.
    if D >= 2 and time.monotonic() < at(0.97):
        _prune_regrow(best_n, best_e, d, D, at(0.97), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
