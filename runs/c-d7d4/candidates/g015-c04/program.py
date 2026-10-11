import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-anneal.
#
# Starting from a valid graph on n vertices, add one vertex on the lighter side
# (stealing edges when the other side is saturated), then anneal over bipartite
# moves that keep every degree <= d and every edge across the bipartition.
# Moves: double-edge switches (degrees unchanged) and single-edge rewires onto
# deficient vertices. The cost is the number of vertex pairs at distance > D,
# computed with bitset ball expansion. Whenever the cost reaches 0, the graph
# is saved and a vertex is added again. Stalls restore the best graph and retry
# with a fresh random attachment.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAP_LIMIT 3000
#define CYC 30000
#define STALL_LIMIT 120000

typedef struct { int type, a, b, c, e; } Move;

static int d_, D_;
static int n_;
static int maxn_, alloc_n_, S_;
static int *side_, *deg_, *adj_;
static uint64_t *bufA_, *bufB_;
static int *tmpA_, *tmpB_;
static int bestn_ = 0;
static int *bside_, *bdeg_, *badj_;
static unsigned char pc16_[65536];
static uint64_t rs_ = 1;

static uint64_t rnd(void) {
    rs_ ^= rs_ >> 12;
    rs_ ^= rs_ << 25;
    rs_ ^= rs_ >> 27;
    return rs_ * 2685821657736338717ULL;
}

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    return pc16_[x & 0xFFFFu] + pc16_[(x >> 16) & 0xFFFFu]
         + pc16_[(x >> 32) & 0xFFFFu] + pc16_[(x >> 48) & 0xFFFFu];
}

static int has_edge(int a, int b) {
    const int *p = adj_ + (size_t)a * d_;
    for (int k = 0; k < deg_[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void list_remove(int v, int u) {
    int *p = adj_ + (size_t)v * d_;
    for (int k = 0; k < deg_[v]; k++) {
        if (p[k] == u) {
            p[k] = p[deg_[v] - 1];
            deg_[v]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    adj_[(size_t)a * d_ + deg_[a]] = b;
    deg_[a]++;
    adj_[(size_t)b * d_ + deg_[b]] = a;
    deg_[b]++;
}

static void del_edge(int a, int b) {
    list_remove(a, b);
    list_remove(b, a);
}

/* Number of unordered vertex pairs at distance > D_ (unreachable pairs included). */
static long long cost_full(void) {
    int n = n_;
    int W = (n + 63) / 64;
    uint64_t *X = bufA_, *Y = bufB_;
    for (int v = 0; v < n; v++) {
        uint64_t *x = X + (size_t)v * S_;
        for (int w = 0; w < W; w++) x[w] = 0;
        x[v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *y = Y + (size_t)v * S_;
            const uint64_t *x = X + (size_t)v * S_;
            for (int w = 0; w < W; w++) y[w] = x[w];
            const int *p = adj_ + (size_t)v * d_;
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *z = X + (size_t)p[k] * S_;
                for (int w = 0; w < W; w++) y[w] |= z[w];
            }
        }
        uint64_t *t = X;
        X = Y;
        Y = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *x = X + (size_t)v * S_;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(x[w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_best(void) {
    bestn_ = n_;
    memcpy(bside_, side_, sizeof(int) * (size_t)n_);
    memcpy(bdeg_, deg_, sizeof(int) * (size_t)n_);
    memcpy(badj_, adj_, sizeof(int) * (size_t)n_ * d_);
}

static void load_best(void) {
    n_ = bestn_;
    memcpy(side_, bside_, sizeof(int) * (size_t)n_);
    memcpy(deg_, bdeg_, sizeof(int) * (size_t)n_);
    memcpy(adj_, badj_, sizeof(int) * (size_t)n_ * d_);
}

static void shuffle_i(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Two-colour the graph; returns 0 if it is not bipartite. */
static int color_sides(void) {
    int n = n_;
    for (int v = 0; v < n; v++) side_[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side_[s] >= 0) continue;
        side_[s] = 0;
        int qh = 0, qt = 0;
        tmpA_[qt++] = s;
        while (qh < qt) {
            int u = tmpA_[qh++];
            for (int k = 0; k < deg_[u]; k++) {
                int v = adj_[(size_t)u * d_ + k];
                if (side_[v] < 0) {
                    side_[v] = 1 - side_[u];
                    tmpA_[qt++] = v;
                } else if (side_[v] == side_[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Append a new vertex on the lighter side, attached to d opposite-side vertices. */
static void add_vertex(void) {
    int v = n_;
    int c0 = 0, c1 = 0;
    for (int u = 0; u < n_; u++) {
        if (side_[u]) c1++;
        else c0++;
    }
    int s;
    if (c0 < c1) s = 0;
    else if (c1 < c0) s = 1;
    else s = rint_(2);
    side_[v] = s;
    deg_[v] = 0;
    n_++;
    int t = 1 - s;
    int tries = 0, max_tries = 60 * d_ + 400;
    while (deg_[v] < d_ && tries < max_tries) {
        tries++;
        int x = rint_(v);
        if (side_[x] != t || has_edge(v, x)) continue;
        if (deg_[x] < d_) {
            add_edge(v, x);
        } else {
            int y = adj_[(size_t)x * d_ + rint_(deg_[x])];
            del_edge(x, y);
            add_edge(v, x);
        }
    }
}

/* Add edges between deficient opposite-side vertices (never hurts the cost). */
static int fill_deficient(void) {
    int na = 0, nb = 0, added = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] < d_) {
            if (side_[v] == 0) tmpA_[na++] = v;
            else tmpB_[nb++] = v;
        }
    }
    if (na == 0 || nb == 0) return 0;
    shuffle_i(tmpA_, na);
    shuffle_i(tmpB_, nb);
    for (int i = 0; i < na; i++) {
        int a = tmpA_[i];
        for (int j = 0; j < nb && deg_[a] < d_; j++) {
            int b = tmpB_[j];
            if (deg_[b] < d_ && !has_edge(a, b)) {
                add_edge(a, b);
                added++;
            }
        }
    }
    return added;
}

static int propose(Move *mv) {
    int n = n_;
    int a = rint_(n);
    if (deg_[a] == 0) return 0;
    int b = adj_[(size_t)a * d_ + rint_(deg_[a])];
    if (rint_(10) < 7) {
        int c = rint_(n);
        if (c == a || side_[c] != side_[a] || deg_[c] == 0) return 0;
        int e = adj_[(size_t)c * d_ + rint_(deg_[c])];
        if (has_edge(a, e) || has_edge(c, b)) return 0;
        mv->type = 0; mv->a = a; mv->b = b; mv->c = c; mv->e = e;
        return 1;
    }
    int e = rint_(n);
    if (e == b || side_[e] == side_[a] || deg_[e] >= d_) return 0;
    if (has_edge(a, e)) return 0;
    mv->type = 1; mv->a = a; mv->b = b; mv->c = -1; mv->e = e;
    return 1;
}

static void apply_move(const Move *mv) {
    if (mv->type == 0) {
        del_edge(mv->a, mv->b);
        del_edge(mv->c, mv->e);
        add_edge(mv->a, mv->e);
        add_edge(mv->c, mv->b);
    } else {
        del_edge(mv->a, mv->b);
        add_edge(mv->a, mv->e);
    }
}

static void unapply_move(const Move *mv) {
    if (mv->type == 0) {
        del_edge(mv->a, mv->e);
        del_edge(mv->c, mv->b);
        add_edge(mv->a, mv->b);
        add_edge(mv->c, mv->e);
    } else {
        del_edge(mv->a, mv->e);
        add_edge(mv->a, mv->b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    clock_t t0 = clock();

    for (int i = 1; i < 65536; i++) pc16_[i] = (unsigned char)(pc16_[i >> 1] + (i & 1));
    rs_ = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs_ == 0) rs_ = 1;

    if (d_ < 1 || D_ < 2) { printf("0 0\n"); return 0; }

    /* Moore bound (capped) as the growth ceiling. */
    double mb = 1.0, p = 1.0;
    for (int i = 1; i < D_ && mb <= CAP_LIMIT; i++) {
        p *= (double)(d_ - 1);
        mb += p;
    }
    long long moore = (long long)(2.0 * mb);
    if (moore > CAP_LIMIT) moore = CAP_LIMIT;

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) { printf("0 0\n"); return 0; }
    if (n_in < 0 || n_in > CAP_LIMIT || m_in < 0 || m_in > 2000000) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m_in + 1));
    if (!eu || !ev) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m_in; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    maxn_ = (int)moore;
    if (maxn_ < n_in) maxn_ = n_in;
    if (maxn_ < 2) maxn_ = 2;
    alloc_n_ = maxn_ + 2;
    S_ = (alloc_n_ + 63) / 64;
    side_ = calloc(alloc_n_, sizeof(int));
    deg_ = calloc(alloc_n_, sizeof(int));
    adj_ = calloc((size_t)alloc_n_ * d_, sizeof(int));
    bside_ = calloc(alloc_n_, sizeof(int));
    bdeg_ = calloc(alloc_n_, sizeof(int));
    badj_ = calloc((size_t)alloc_n_ * d_, sizeof(int));
    bufA_ = calloc((size_t)alloc_n_ * S_, sizeof(uint64_t));
    bufB_ = calloc((size_t)alloc_n_ * S_, sizeof(uint64_t));
    tmpA_ = calloc(alloc_n_, sizeof(int));
    tmpB_ = calloc(alloc_n_, sizeof(int));
    if (!side_ || !deg_ || !adj_ || !bside_ || !bdeg_ || !badj_ ||
        !bufA_ || !bufB_ || !tmpA_ || !tmpB_) {
        printf("0 0\n");
        return 0;
    }

    n_ = n_in < 2 ? 2 : n_in;
    for (int i = 0; i < m_in; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n_ || v >= n_ || u == v) { printf("0 0\n"); return 0; }
        if (has_edge(u, v)) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_) { printf("0 0\n"); return 0; }
        add_edge(u, v);
    }
    if (!color_sides()) { printf("0 0\n"); return 0; }

    long long cur = cost_full();
    if (cur == 0) save_best();

    long long stall = 0;
    while (1) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > limit) break;

        if (cur == 0) {
            if (n_ > bestn_) save_best();
            if (n_ >= maxn_) break;
            add_vertex();
            fill_deficient();
            cur = cost_full();
            stall = 0;
            continue;
        }

        if (stall >= STALL_LIMIT) {
            if (bestn_ > 0) {
                load_best();
                add_vertex();
                fill_deficient();
            }
            cur = cost_full();
            stall = 0;
            continue;
        }

        double ph = (double)(stall % CYC) / (double)CYC;
        double T = 1.2 * pow(0.08 / 1.2, ph);
        stall++;

        Move mv;
        if (!propose(&mv)) continue;
        apply_move(&mv);
        long long nc = cost_full();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (fill_deficient() > 0) cur = cost_full();
        } else {
            unapply_move(&mv);
        }
    }

    if (bestn_ <= 0) { printf("0 0\n"); return 0; }
    long long m = 0;
    for (int v = 0; v < bestn_; v++) m += bdeg_[v];
    m /= 2;
    printf("%d %lld\n", bestn_, m);
    for (int v = 0; v < bestn_; v++) {
        for (int k = 0; k < bdeg_[v]; k++) {
            int u = badj_[(size_t)v * d_ + k];
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
    """A dense structured graph whose degree is at least d."""
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
# Bipartite voltage lifts over small groups (cyclic or semidirect).
# ----------------------------------------------------------------------------

def _pick_group(order, rng):
    """Return (order, mul) for a cyclic or a semidirect group of the given order."""
    if order >= 4 and rng.random() < 0.5:
        ks = [k for k in range(2, 13) if order % k == 0 and order // k >= 2]
        rng.shuffle(ks)
        for k in ks:
            m = order // k
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                r = rng.choice(rs)
                try:
                    o, mul, _ = lib.semidirect_group(m, k, r)
                    return o, mul
                except ValueError:
                    continue
    o, mul, _ = lib.cyclic_group(order)
    return o, mul


def _init_darts(s, d, order, rng):
    """Darts (u, v, g): A vertex u, B vertex v (local indices), voltage g. Each A and B vertex gets d darts."""
    slots = [v for v in range(s) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    seen = set()
    for u in range(s):
        for j in range(d):
            v = slots[u * d + j]
            for _ in range(60):
                g = rng.randrange(order)
                if (u, v, g) not in seen:
                    break
            else:
                return None
            seen.add((u, v, g))
            darts.append((u, v, g))
    return darts


def _lift(s, darts, order, mul):
    """Lift the base graph: A side is 0..s-1, B side is s..2s-1 in the base."""
    return lib.group_lift(2 * s, [(u, s + v, g) for u, v, g in darts], order, mul)


def _lift_search(d, D, best_n, rng, deadline, consider):
    """Hill-climb voltages of random bipartite base lifts until a diameter-D lift appears."""
    base_pick = (1, 1, 2, 2, 3)
    while time.monotonic() < deadline:
        s = rng.choice(base_pick)
        base_n = 2 * s
        lo = best_n // base_n
        order = lo + 1 + rng.randrange(0, max(2, lo // 8 + 1))
        order, mul = _pick_group(order, rng)
        darts = _init_darts(s, d, order, rng)
        if darts is None:
            continue
        n, e = _lift(s, darts, order, mul)
        cost = lib.bad_pairs(n, e, D)
        steps = 0
        while cost > 0 and steps < 250 and time.monotonic() < deadline:
            steps += 1
            i = rng.randrange(len(darts))
            u, v, old = darts[i]
            g2 = rng.randrange(order)
            if g2 == old or (u, v, g2) in set(darts):
                continue
            darts[i] = (u, v, g2)
            n2, e2 = _lift(s, darts, order, mul)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= cost or rng.random() < 0.02:
                cost, n, e = c2, n2, e2
            else:
                darts[i] = (u, v, old)
        if cost == 0 and time.monotonic() < deadline:
            if n > best_n and lib.is_valid(n, e, d, D):
                consider(n, e)
                best_n = max(best_n, n)
            n3, e3 = _grow(n, e, d, D, deadline, rng)
            consider(n3, e3)
            best_n = max(best_n, n3)


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
# Python large-neighbourhood search (fallback when the C engine is unavailable).
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
# C engine glue.
# ----------------------------------------------------------------------------

def _c_anneal(d, D, seed, budget, n, edges):
    """Run the C grow-and-anneal engine from (n, edges). Returns (n, edges) as printed by C."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=budget + 3.0)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Driver. Fractions of the usable budget T = 0.85 * time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, twin trials, short LNS
#   L  bipartite voltage lifts over cyclic / semidirect groups
#   C  NEW: grow-and-anneal in C from the best valid graph (most of the time)
#   (fallback if C is unavailable) B, LNS and pruning in Python
# Every candidate passes lib.is_valid before it is kept. The fallback is
# haar_graph(d, range(d)), which is valid for every d >= 1 and D >= 2.
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

    mb = lib.moore_bound(d, D)

    # Phase A: structured small base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.03), rng)
            consider(n1, e1)
    if best_n >= mb:
        return best_n, list(best_e)
    if D >= 2:
        trial_end = at(0.04)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
        _lns(best_n, best_e, d, D, at(0.06), rng, consider)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.12) and best_n < mb:
        _lift_search(d, D, best_n, rng, at(0.12), consider)
    if best_n >= mb:
        return best_n, list(best_e)

    # Phase C: grow-and-anneal in C from the best valid graph found so far.
    c_done = False
    if D >= 2 and best_n < mb:
        c_end = start + 0.85 * time_limit - 1.0
        budget = c_end - time.monotonic() - 1.5
        if budget >= 1.0:
            try:
                n2, e2 = _c_anneal(d, D, seed, budget, best_n, best_e)
                consider(n2, e2)
                c_done = True
            except (RuntimeError, ValueError, OSError):
                c_done = False

    # Fallback phases in Python, used only when the C engine could not run.
    if not c_done and D >= 2:
        if time.monotonic() < at(0.60):
            raw = _raw_big(d, D)
            if raw is not None:
                rn, re = raw
                while time.monotonic() < at(0.60):
                    r = _deletion_trial(d, D, rn, re, rng, at(0.60))
                    if r is None:
                        break
                    consider(*r)
        if time.monotonic() < at(0.72):
            _lns(best_n, best_e, d, D, at(0.72), rng, consider)
        if time.monotonic() < at(1.0):
            _prune_regrow(best_n, best_e, d, D, at(1.0), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
