import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bit-parallel bad-pair annealing with greedy-cover vertex insertion,
# vertex kill-and-regrow, and bipartite double-edge switches.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define NMAX 2048
#define WMAX ((NMAX + 63) / 64)
#define DMAX 64

typedef struct {
    int n;
    int deg[NMAX];
    int col[NMAX];
    int adj[NMAX * DMAX];
} State;

static int d_ = 0, D_ = 0, n_ = 0;
static int deg_[NMAX];
static int col_[NMAX];
static int adjl[NMAX * DMAX];
static uint64_t ballA[NMAX * WMAX];
static uint64_t ballB[NMAX * WMAX];
static uint64_t rs = 88172645463325252ULL;
static int Lbuf[NMAX], Rbuf[NMAX], S0[NMAX], stk_[NMAX];
static char used_[NMAX];
static State cur_s, best_s;
static long long moore_ = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int m) { return (int)(rnd64() % (uint64_t)m); }

static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double elapsed_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static long long moore_bound(int d, int D) {
    if (d == 2) return 2LL * D;
    double s = 0.0, p = 1.0;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (double)(d - 1);
    }
    return (long long)(2.0 * s + 0.5);
}

static int has_edge(int u, int v) {
    const int *a = adjl + (size_t)u * d_;
    for (int k = 0; k < deg_[u]; k++)
        if (a[k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adjl[u * d_ + deg_[u]++] = v;
    adjl[v * d_ + deg_[v]++] = u;
}

static void del_from(int u, int v) {
    int *a = adjl + (size_t)u * d_;
    for (int k = 0; k < deg_[u]; k++) {
        if (a[k] == v) {
            a[k] = a[deg_[u] - 1];
            deg_[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_from(u, v);
    del_from(v, u);
}

/* Remove vertex x by moving the last vertex into its slot. */
static void remove_vertex(int x) {
    while (deg_[x] > 0) del_edge(x, adjl[x * d_ + deg_[x] - 1]);
    int last = n_ - 1;
    if (x != last) {
        for (int k = 0; k < deg_[last]; k++) {
            int w = adjl[last * d_ + k];
            int *aw = adjl + (size_t)w * d_;
            for (int j = 0; j < deg_[w]; j++) {
                if (aw[j] == last) {
                    aw[j] = x;
                    break;
                }
            }
        }
        for (int k = 0; k < deg_[last]; k++) adjl[x * d_ + k] = adjl[last * d_ + k];
        deg_[x] = deg_[last];
        col_[x] = col_[last];
    }
    deg_[last] = 0;
    n_--;
}

/* Bitmask balls of radius r for all n vertices. Returns the buffer holding the result. */
static uint64_t *compute_ball(int n, int r) {
    int W = (n + 63) >> 6;
    uint64_t *a = ballA, *b = ballB;
    memset(a, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) a[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = b + (size_t)v * W;
            const uint64_t *src = a + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *nb = a + (size_t)adjl[v * d_ + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= nb[w];
            }
        }
        uint64_t *t = a;
        a = b;
        b = t;
    }
    return a;
}

/* Number of unordered vertex pairs at distance > D_ (unreachable counts). */
static long long cost_of(int n) {
    uint64_t *b = compute_ball(n, D_);
    int W = (n + 63) >> 6;
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(b[(size_t)v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Join deficient cross-side non-adjacent pairs in random order (only shortens distances). */
static void fill_graph(int n) {
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg_[v] >= d_) continue;
        if (col_[v] == 0) Lbuf[nl++] = v;
        else Rbuf[nr++] = v;
    }
    shuffle_int(Lbuf, nl);
    shuffle_int(Rbuf, nr);
    for (int i = 0; i < nl; i++) {
        int a = Lbuf[i];
        if (deg_[a] >= d_) continue;
        for (int j = 0; j < nr && deg_[a] < d_; j++) {
            int b = Rbuf[j];
            if (deg_[b] >= d_) continue;
            if (has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

/* Append a vertex of colour newcol joined to a greedy cover of the opposite side. */
static void add_vertex(int n, int newcol) {
    int W = (n + 63) >> 6;
    uint64_t *b = compute_ball(n, D_ - 1);
    uint64_t covered[WMAX];
    memset(covered, 0, sizeof(covered));
    memset(used_, 0, (size_t)n);
    int chosen[DMAX];
    int nch = 0;
    for (int pick = 0; pick < d_; pick++) {
        int best = -1, bestg = 0, ties = 0;
        for (int s = 0; s < n; s++) {
            if (col_[s] != 1 - newcol || used_[s]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(b[(size_t)s * W + w] & ~covered[w]);
            if (g > bestg) {
                bestg = g;
                best = s;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndi(ties) == 0) best = s;
            }
        }
        if (best < 0) break;
        used_[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) covered[w] |= b[(size_t)best * W + w];
    }
    int v = n;
    n_ = n + 1;
    col_[v] = newcol;
    deg_[v] = 0;
    for (int k = 0; k < nch; k++) {
        int s = chosen[k];
        if (deg_[s] >= d_) {
            int t = adjl[s * d_ + rndi(deg_[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
}

/* Bipartite double-edge switches minimising bad pairs. Returns 1 if cost reaches 0. */
static int anneal(int n, int iters) {
    int ns0 = 0;
    for (int v = 0; v < n; v++)
        if (col_[v] == 0 && deg_[v] > 0) S0[ns0++] = v;
    if (ns0 < 2) return 0;
    long long cur = cost_of(n);
    for (int it = 0; it < iters && cur > 0; it++) {
        int a = S0[rndi(ns0)];
        int c = S0[rndi(ns0)];
        if (c == a) continue;
        if (deg_[a] == 0 || deg_[c] == 0) continue;
        int b = adjl[a * d_ + rndi(deg_[a])];
        int e = adjl[c * d_ + rndi(deg_[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long long nw = cost_of(n);
        if (nw <= cur || (nw == cur + 1 && rndu() < 0.05)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static void save_state(State *s) {
    s->n = n_;
    memcpy(s->deg, deg_, sizeof(int) * (size_t)n_);
    memcpy(s->col, col_, sizeof(int) * (size_t)n_);
    memcpy(s->adj, adjl, sizeof(int) * (size_t)n_ * (size_t)d_);
}

static void load_state(const State *s) {
    n_ = s->n;
    memcpy(deg_, s->deg, sizeof(int) * (size_t)n_);
    memcpy(col_, s->col, sizeof(int) * (size_t)n_);
    memcpy(adjl, s->adj, sizeof(int) * (size_t)n_ * (size_t)d_);
}

static void init_kdd(void) {
    n_ = 2 * d_;
    for (int v = 0; v < n_; v++) {
        deg_[v] = 0;
        col_[v] = (v < d_) ? 0 : 1;
    }
    for (int i = 0; i < d_; i++)
        for (int j = 0; j < d_; j++) add_edge(i, d_ + j);
}

static int color_check(int n) {
    for (int v = 0; v < n; v++) col_[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col_[s] != -1) continue;
        col_[s] = 0;
        int sp = 0;
        stk_[sp++] = s;
        while (sp > 0) {
            int u = stk_[--sp];
            for (int k = 0; k < deg_[u]; k++) {
                int v = adjl[u * d_ + k];
                if (col_[v] == -1) {
                    col_[v] = 1 - col_[u];
                    stk_[sp++] = v;
                }
            }
        }
    }
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg_[u]; k++)
            if (col_[u] == col_[adjl[u * d_ + k]]) return 0;
    return 1;
}

static void print_state(const State *s) {
    int n = s->n;
    long m = 0;
    for (int u = 0; u < n; u++)
        for (int k = 0; k < s->deg[u]; k++)
            if (u < s->adj[u * d_ + k]) m++;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int k = 0; k < s->deg[u]; k++) {
            int v = s->adj[u * d_ + k];
            if (u < v) printf("%d %d\n", u, v);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d_ < 2 || d_ > DMAX || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    moore_ = moore_bound(d_, D_);

    int n0 = 0, m0 = 0;
    int ok_in = 1;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 > 0 && n0 <= NMAX - 2 && m0 >= 0) {
        n_ = n0;
        for (int v = 0; v < n_; v++) deg_[v] = 0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok_in = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n_ || v >= n_ || u == v ||
                deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) {
                ok_in = 0;
                break;
            }
            add_edge(u, v);
        }
        if (ok_in && !color_check(n_)) ok_in = 0;
    } else {
        ok_in = 0;
    }
    if (!ok_in) init_kdd();

    if (cost_of(n_) != 0) {
        if (!anneal(n_, 4000) || cost_of(n_) != 0) init_kdd();
    }
    save_state(&best_s);
    save_state(&cur_s);

    while (elapsed_s() < budget) {
        load_state(&cur_s);
        if (n_ > d_ + 2 && rndi(100) < 35) remove_vertex(rndi(n_));
        fill_graph(n_);
        if ((long long)n_ + 1 <= moore_ && n_ + 1 < NMAX) {
            add_vertex(n_, rndi(2));
            fill_graph(n_);
        }
        int ok = anneal(n_, 1500);
        if (ok) {
            if (n_ > best_s.n) save_state(&best_s);
            if (n_ >= cur_s.n - 1) save_state(&cur_s);
        }
        if (cur_s.n < best_s.n - 3) cur_s = best_s;
    }
    print_state(&best_s);
    return 0;
}
'''


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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list.

    Cross-side edges keep the graph bipartite and degrees <= d, and can only
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


# ----------------------------------------------------------------------------
# Python large-neighbourhood search (kill, repair, regrow), anchored to its best graph.
# ----------------------------------------------------------------------------

def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
                n1, e1 = _grow(n0, e0, d, D, start + 0.06 * time_limit, rng)
                consider(n1, e1)

        # Randomized twin-duplication pipelines from the structured base.
        if D >= 2:
            trial_end = start + 0.10 * time_limit
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)

        # Random voltage lifts of small bipartite base multigraphs.
        if D >= 2:
            _lift_search(d, D, start + 0.14 * time_limit, rng, best_n, consider)

        # Python kill-repair-regrow from the best valid graph so far.
        if D >= 2:
            _lns(best_n, best_e, d, D, start + 0.18 * time_limit, rng, consider)
    except Exception:
        pass

    # Main stage: C annealing engine (kill, regrow, switch-based repair) from the best graph.
    if D >= 2 and 2 <= d <= 64 and best_n < lib.moore_bound(d, D):
        budget = 0.86 * time_limit - (time.monotonic() - start) - 3.0
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 20.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
