import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite local search that grows a valid graph by vertex pairs.
#
# Moves keep every vertex degree <= d and the graph bipartite:
#   * 2-switch: (x,p),(y,q) -> (x,q),(y,p) with x,y on side A. Degrees unchanged.
#   * edge add: joins a deficient A vertex and a deficient B vertex (never hurts).
#   * pair grow: adds w_A, w_B and the edge w_A-w_B, then takes d-1 disjoint edges
#     (a_j,b_j) and rewires them to w_B-a_j and w_A-b_j. Degrees stay <= d.
# Cost = number of ordered vertex pairs at distance > D (bitset BFS, exact).
# Simulated annealing on the cost. Whenever cost hits 0 the graph is recorded and
# grown again. Stagnation restores the best valid graph. Only valid graphs are
# printed, and the best one is printed at the end (or the input if none).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GROW_CAP 4096
#define PATIENCE 1500
#define TEMP 1.5

static int d_, D_, n_, NMAX_, W_;
static int *adj_, *deg_, *col_;
static uint64_t *R_, *R2_;
static int *bAdj_, *bDeg_, *bCol_;
static int bn_ = 0, have_best_ = 0;
static uint64_t rs_ = 88172645463325252ULL;
static clock_t c0_;

static uint64_t rnd(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - c0_) / CLOCKS_PER_SEC; }

static int has_edge(int a, int b) {
    const int *p = adj_ + (size_t)a * d_;
    for (int i = 0; i < deg_[a]; i++) if (p[i] == b) return 1;
    return 0;
}
static void rm_half(int a, int b) {
    int *p = adj_ + (size_t)a * d_;
    for (int i = 0; i < deg_[a]; i++) {
        if (p[i] == b) { p[i] = p[deg_[a] - 1]; deg_[a]--; return; }
    }
}
static void add_half(int a, int b) { adj_[(size_t)a * d_ + deg_[a]++] = b; }
static void add_edge(int a, int b) { add_half(a, b); add_half(b, a); }
static void del_edge(int a, int b) { rm_half(a, b); rm_half(b, a); }

/* Number of ordered pairs (u != v) at distance > D_. Zero iff the graph is valid. */
static long long eval_cost(void) {
    int nw = (n_ + 63) / 64;
    for (int v = 0; v < n_; v++) {
        uint64_t *r = R_ + (size_t)v * W_;
        memset(r, 0, sizeof(uint64_t) * (size_t)nw);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < D_; s++) {
        for (int v = 0; v < n_; v++) {
            uint64_t *out = R2_ + (size_t)v * W_;
            memcpy(out, R_ + (size_t)v * W_, sizeof(uint64_t) * (size_t)nw);
            const int *p = adj_ + (size_t)v * d_;
            for (int i = 0; i < deg_[v]; i++) {
                const uint64_t *src = R_ + (size_t)p[i] * W_;
                for (int w = 0; w < nw; w++) out[w] |= src[w];
            }
        }
        uint64_t *t = R_; R_ = R2_; R2_ = t;
    }
    long long tot = 0;
    for (int v = 0; v < n_; v++) {
        const uint64_t *r = R_ + (size_t)v * W_;
        for (int w = 0; w < nw; w++) tot += __builtin_popcountll(r[w]);
    }
    return (long long)n_ * n_ - tot;
}

static void save_best(void) {
    memcpy(bAdj_, adj_, sizeof(int) * (size_t)NMAX_ * d_);
    memcpy(bDeg_, deg_, sizeof(int) * (size_t)NMAX_);
    memcpy(bCol_, col_, sizeof(int) * (size_t)NMAX_);
    bn_ = n_;
    have_best_ = 1;
}
static void load_best(void) {
    memcpy(adj_, bAdj_, sizeof(int) * (size_t)NMAX_ * d_);
    memcpy(deg_, bDeg_, sizeof(int) * (size_t)NMAX_);
    memcpy(col_, bCol_, sizeof(int) * (size_t)NMAX_);
    n_ = bn_;
}

/* Random 2-switch candidate: x,y on side A; p,q on side B; x-p, y-q edges. */
static int pick_switch(int *a1, int *b1, int *a2, int *b2) {
    for (int t = 0; t < 200; t++) {
        int x = rint_(n_), y = rint_(n_);
        if (x == y || col_[x] != 0 || col_[y] != 0 || deg_[x] == 0 || deg_[y] == 0) continue;
        int p = adj_[(size_t)x * d_ + rint_(deg_[x])];
        int q = adj_[(size_t)y * d_ + rint_(deg_[y])];
        if (p == q) continue;
        if (has_edge(x, q) || has_edge(y, p)) continue;
        *a1 = x; *b1 = p; *a2 = y; *b2 = q;
        return 1;
    }
    return 0;
}

/* Join a deficient A vertex to a deficient B vertex. Cost never increases. */
static int edge_add_move(void) {
    for (int t = 0; t < 300; t++) {
        int a = rint_(n_), b = rint_(n_);
        if (col_[a] != 0 || col_[b] != 1) continue;
        if (deg_[a] >= d_ || deg_[b] >= d_) continue;
        if (has_edge(a, b)) continue;
        add_edge(a, b);
        return 1;
    }
    return 0;
}

/* Pair grow: add w_A (side 0) and w_B (side 1) joined to each other, with
   d-1 disjoint edges (a_j,b_j) rewired to w_B-a_j and w_A-b_j. Degrees preserved. */
static int grow_move(void) {
    int k = d_ - 1;
    if (k < 1 || k > 256) return 0;
    static int ua[256], ub[256];
    int np = 0;
    for (int t = 0; t < 4000 && np < k; t++) {
        int a = rint_(n_);
        if (col_[a] != 0 || deg_[a] == 0) continue;
        int b = adj_[(size_t)a * d_ + rint_(deg_[a])];
        int bad = 0;
        for (int j = 0; j < np; j++) if (ua[j] == a || ub[j] == b) { bad = 1; break; }
        if (bad) continue;
        ua[np] = a; ub[np] = b; np++;
    }
    if (np < k) return 0;
    int wa = n_, wb = n_ + 1;
    col_[wa] = 0; col_[wb] = 1;
    deg_[wa] = 0; deg_[wb] = 0;
    n_ += 2;
    for (int j = 0; j < k; j++) {
        del_edge(ua[j], ub[j]);
        add_edge(wa, ub[j]);
        add_edge(wb, ua[j]);
    }
    add_edge(wa, wb);
    return 1;
}

static int color_graph(int *queue) {
    for (int v = 0; v < n_; v++) col_[v] = -1;
    for (int s = 0; s < n_; s++) {
        if (col_[s] != -1) continue;
        col_[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int u = queue[head++];
            const int *p = adj_ + (size_t)u * d_;
            for (int i = 0; i < deg_[u]; i++) {
                int v = p[i];
                if (col_[v] == -1) { col_[v] = 1 - col_[u]; queue[tail++] = v; }
                else if (col_[v] == col_[u]) return 0;
            }
        }
    }
    return 1;
}

static void print_input(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    double budget = atof(argv[4]);
    c0_ = clock();

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (nin < 0 || min_ < 0 || nin > 2000000 || min_ > 20000000) return 0;
    int *eu = malloc(sizeof(int) * (size_t)(min_ + 2));
    int *ev = malloc(sizeof(int) * (size_t)(min_ + 2));
    if (!eu || !ev) return 0;
    int ne = 0;
    for (int i = 0; i < min_; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        eu[ne] = u; ev[ne] = v; ne++;
    }
    if (nin == 0) { nin = 2; eu[0] = 0; ev[0] = 1; ne = 1; }
    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }

    NMAX_ = nin + GROW_CAP + 8;
    W_ = (NMAX_ + 63) / 64;
    adj_ = calloc((size_t)NMAX_ * d_, sizeof(int));
    deg_ = calloc((size_t)NMAX_, sizeof(int));
    col_ = malloc(sizeof(int) * (size_t)NMAX_);
    bAdj_ = calloc((size_t)NMAX_ * d_, sizeof(int));
    bDeg_ = calloc((size_t)NMAX_, sizeof(int));
    bCol_ = malloc(sizeof(int) * (size_t)NMAX_);
    R_ = calloc((size_t)NMAX_ * W_, sizeof(uint64_t));
    R2_ = calloc((size_t)NMAX_ * W_, sizeof(uint64_t));
    int *queue = malloc(sizeof(int) * (size_t)NMAX_);
    if (!adj_ || !deg_ || !col_ || !bAdj_ || !bDeg_ || !bCol_ || !R_ || !R2_ || !queue) return 0;
    for (int v = 0; v < NMAX_; v++) col_[v] = -1;

    /* Load the start graph; fall back to echoing the input if it is unusable. */
    n_ = nin;
    int ok = 1;
    for (int i = 0; i < ne; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n_ || v >= n_ || u == v) { ok = 0; break; }
        if (has_edge(u, v)) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_) { ok = 0; break; }
        add_edge(u, v);
    }
    if (ok) ok = color_graph(queue);
    if (!ok) { print_input(nin, ne, eu, ev); return 0; }

    long long cur = eval_cost();
    if (cur == 0) save_best();
    long long rbest = cur;
    long stag = 0;
    unsigned long it = 0;

    while (1) {
        if ((it & 31) == 0 && elapsed() >= budget) break;
        it++;

        if (cur == 0) {
            if (!have_best_ || n_ > bn_) save_best();
            if (n_ + 2 > NMAX_ - 2) break;
            if (!grow_move()) continue;
            cur = eval_cost();
            rbest = cur;
            stag = 0;
            continue;
        }

        if (rint_(100) < 4 && edge_add_move()) {
            cur = eval_cost();
        } else {
            int a1, b1, a2, b2;
            if (pick_switch(&a1, &b1, &a2, &b2)) {
                del_edge(a1, b1); del_edge(a2, b2);
                add_edge(a1, b2); add_edge(a2, b1);
                long long nc = eval_cost();
                long long delta = nc - cur;
                if (delta <= 0 || rdbl() < exp(-(double)delta / TEMP)) {
                    cur = nc;
                } else {
                    del_edge(a1, b2); del_edge(a2, b1);
                    add_edge(a1, b1); add_edge(a2, b2);
                }
            }
        }

        if (cur < rbest) {
            rbest = cur;
            stag = 0;
        } else if (++stag > PATIENCE) {
            if (have_best_) { load_best(); cur = eval_cost(); }
            rbest = cur;
            stag = 0;
        }
    }

    if (!have_best_) { print_input(nin, ne, eu, ev); return 0; }
    long m = 0;
    for (int v = 0; v < bn_; v++)
        for (int i = 0; i < bDeg_[v]; i++)
            if (bAdj_[(size_t)v * d_ + i] > v) m++;
    printf("%d %ld\n", bn_, m);
    for (int v = 0; v < bn_; v++)
        for (int i = 0; i < bDeg_[v]; i++) {
            int u = bAdj_[(size_t)v * d_ + i];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (Python search).
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d exactly.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Driver. Time split: Python bi-Cayley search, then the C grow-and-anneal engine
# on the best graph, then greedy slack extension. Every candidate is checked
# with lib.is_valid, and the best valid graph is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    py_deadline = start + 0.40 * total
    c_end = start + 0.90 * total
    final_deadline = start + max(1.0, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < py_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < py_deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, py_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # C grow-and-anneal engine on the best graph found so far.
    if d >= 2 and D >= 2:
        c_budget = c_end - time.monotonic() - 0.5
        if c_budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=best, timeout=c_budget + 10.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
