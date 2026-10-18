import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair annealing.
#
# State: a graph with max degree d, bipartite (side 0 / side 1), and every
# vertex counted by cost = number of ordered vertex pairs at distance > D.
# Moves keep degrees <= d and bipartiteness:
#   - double edge swap (keeps all degrees)
#   - endpoint rewire toward a deficient vertex
#   - fill: join a deficient A-vertex to a deficient B-vertex
# Growth adds one A and one B vertex with degree 0, then anneals to cost 0.
# A successful anneal is saved as the new best; a failed one restores the best
# and perturbs it. Output is always the best saved graph, which has cost 0.
# UNTESTED: written without running it; the Python side falls back on any failure.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAX_GROW 600
#define SA_ITERS 1500

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnext() % (uint64_t)k); }
static double r01(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static int dd, DD;
static int n, cap;
static int *col, *deg, *nb;
static uint64_t *R1, *R2;
static int *dA, *dB, nA, nB;
static int *bnb, *bdeg, *bcol, bn;
static clock_t t_end;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost_eval(void) {
    int W = (n + 63) >> 6;
    size_t words = (size_t)n * W;
    memset(R1, 0, sizeof(uint64_t) * words);
    for (int v = 0; v < n; v++) R1[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < DD; s++) {
        memcpy(R2, R1, sizeof(uint64_t) * words);
        for (int v = 0; v < n; v++) {
            uint64_t *dst = R2 + (size_t)v * W;
            const int *p = nb + (size_t)v * dd;
            for (int j = 0; j < deg[v]; j++) {
                const uint64_t *src = R1 + (size_t)p[j] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = R1;
        R1 = R2;
        R2 = t;
    }
    long long reached = 0;
    for (size_t i = 0; i < words; i++) reached += popc64(R1[i]);
    return (long long)n * n - reached;
}

static int adjacent(int a, int b) {
    const int *p = nb + (size_t)a * dd;
    for (int j = 0; j < deg[a]; j++)
        if (p[j] == b) return 1;
    return 0;
}

static void push_nb(int a, int b) {
    nb[(size_t)a * dd + deg[a]] = b;
    deg[a]++;
}

static void add_edge(int a, int b) {
    push_nb(a, b);
    push_nb(b, a);
}

static void del_one(int a, int b) {
    int *p = nb + (size_t)a * dd;
    for (int j = 0; j < deg[a]; j++) {
        if (p[j] == b) {
            p[j] = p[deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
}

static int random_edge(int *pa, int *pb) {
    for (int t = 0; t < 100; t++) {
        int v = rint_(n);
        if (deg[v] == 0) continue;
        int u = nb[(size_t)v * dd + rint_(deg[v])];
        if (col[v] == 0) {
            *pa = v;
            *pb = u;
        } else {
            *pa = u;
            *pb = v;
        }
        return 1;
    }
    return 0;
}

static void build_def(void) {
    nA = 0;
    nB = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < dd) {
            if (col[v] == 0) dA[nA++] = v;
            else dB[nB++] = v;
        }
    }
}

typedef struct {
    int nr, na;
    int ra[2], rb[2], aa[2], ab[2];
} Change;

static int make_move(Change *c) {
    int a, b, x, e, t;
    c->nr = 0;
    c->na = 0;
    t = rint_(100);
    if (t < 35) {
        int cc;
        if (!random_edge(&a, &b) || !random_edge(&cc, &e)) return 0;
        if (a == cc || b == e) return 0;
        if (adjacent(a, e) || adjacent(cc, b)) return 0;
        c->nr = 2;
        c->ra[0] = a; c->rb[0] = b;
        c->ra[1] = cc; c->rb[1] = e;
        c->na = 2;
        c->aa[0] = a; c->ab[0] = e;
        c->aa[1] = cc; c->ab[1] = b;
        return 1;
    }
    build_def();
    if (t < 60) {
        if (nB == 0 || !random_edge(&a, &b)) return 0;
        e = dB[rint_(nB)];
        if (e == b || adjacent(a, e)) return 0;
        c->nr = 1;
        c->ra[0] = a; c->rb[0] = b;
        c->na = 1;
        c->aa[0] = a; c->ab[0] = e;
        return 1;
    }
    if (t < 85) {
        if (nA == 0 || !random_edge(&a, &b)) return 0;
        x = dA[rint_(nA)];
        if (x == a || adjacent(x, b)) return 0;
        c->nr = 1;
        c->ra[0] = a; c->rb[0] = b;
        c->na = 1;
        c->aa[0] = x; c->ab[0] = b;
        return 1;
    }
    if (nA == 0 || nB == 0) return 0;
    a = dA[rint_(nA)];
    b = dB[rint_(nB)];
    if (adjacent(a, b)) return 0;
    c->na = 1;
    c->aa[0] = a; c->ab[0] = b;
    return 1;
}

static void apply_change(const Change *c) {
    for (int i = 0; i < c->nr; i++) remove_edge(c->ra[i], c->rb[i]);
    for (int i = 0; i < c->na; i++) add_edge(c->aa[i], c->ab[i]);
}

static void undo_change(const Change *c) {
    for (int i = 0; i < c->na; i++) remove_edge(c->aa[i], c->ab[i]);
    for (int i = 0; i < c->nr; i++) add_edge(c->ra[i], c->rb[i]);
}

static long long sa_run(long iters, double T0) {
    long long cur = cost_eval();
    Change c;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && clock() > t_end) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
        if (!make_move(&c)) continue;
        apply_change(&c);
        long long c2 = cost_eval();
        if (c2 <= cur || r01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            undo_change(&c);
        }
    }
    return cur;
}

static void save_best(void) {
    bn = n;
    memcpy(bnb, nb, sizeof(int) * (size_t)n * dd);
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(bcol, col, sizeof(int) * (size_t)n);
}

static void restore_best(void) {
    n = bn;
    memcpy(nb, bnb, sizeof(int) * (size_t)n * dd);
    memcpy(deg, bdeg, sizeof(int) * (size_t)n);
    memcpy(col, bcol, sizeof(int) * (size_t)n);
}

static void diversify(int k) {
    Change c;
    for (int i = 0; i < k; i++)
        if (make_move(&c)) apply_change(&c);
}

static int bipartite_color(int n0, int *qbuf) {
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t) {
            int u = qbuf[h++];
            const int *p = nb + (size_t)u * dd;
            for (int j = 0; j < deg[u]; j++) {
                int v = p[j];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    qbuf[t++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_edges_input(int n0, int m0, const int *eu, const int *ev) {
    printf("%d %d\n", n0, m0);
    for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || dd < 1) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }

    cap = n0 + 2 * MAX_GROW;
    size_t wcap = ((size_t)cap + 63) / 64;
    col = malloc(sizeof(int) * (size_t)cap);
    deg = calloc((size_t)cap, sizeof(int));
    nb = malloc(sizeof(int) * (size_t)cap * dd);
    R1 = malloc(sizeof(uint64_t) * (size_t)cap * wcap);
    R2 = malloc(sizeof(uint64_t) * (size_t)cap * wcap);
    dA = malloc(sizeof(int) * (size_t)cap);
    dB = malloc(sizeof(int) * (size_t)cap);
    bnb = malloc(sizeof(int) * (size_t)cap * dd);
    bdeg = malloc(sizeof(int) * (size_t)cap);
    bcol = malloc(sizeof(int) * (size_t)cap);
    int *qbuf = malloc(sizeof(int) * (size_t)cap);
    if (!col || !deg || !nb || !R1 || !R2 || !dA || !dB || !bnb || !bdeg || !bcol || !qbuf) {
        printf("0 0\n");
        return 0;
    }

    n = n0;
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) ok = 0;
        else if (deg[u] >= dd || deg[v] >= dd) ok = 0;
        else if (adjacent(u, v)) ok = 0;
        else add_edge(u, v);
    }
    if (ok) ok = bipartite_color(n0, qbuf);
    if (ok) ok = (cost_eval() == 0);
    if (!ok) {
        print_edges_input(n0, m0, eu, ev);
        return 0;
    }

    t_end = clock() + (clock_t)(tl * 0.92 * (double)CLOCKS_PER_SEC);
    save_best();
    while (clock() < t_end) {
        if (n + 2 > cap) break;
        col[n] = 0;
        deg[n] = 0;
        col[n + 1] = 1;
        deg[n + 1] = 0;
        n += 2;
        if (sa_run(SA_ITERS, 3.0) == 0) {
            save_best();
        } else {
            restore_best();
            diversify(30);
        }
    }
    restore_best();

    long long m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %lld\n", n, m);
    for (int v = 0; v < n; v++) {
        const int *p = nb + (size_t)v * dd;
        for (int j = 0; j < deg[v]; j++)
            if (v < p[j]) printf("%d %d\n", v, p[j]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions.
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
# Python bi-Cayley voltage search (kept as the seed-producing phase).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_GREEDY_PROB = 0.04
_GREEDY_SAMPLE = 96


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
                r = None
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
    """Simulated annealing with stagnation restarts and greedy voltage scans. Returns (n, edges) or None."""
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

        if rng.random() < _GREEDY_PROB:
            l = rng.randrange(d)
            i = rng.randrange(k)
            old = S[l][i]
            best_v, best_c, best_r = old, cost, reach
            for v in rng.sample(range(G), min(G, _GREEDY_SAMPLE)):
                if v == old:
                    continue
                if time.monotonic() > deadline:
                    break
                S[l][i] = v
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], v)
                r2 = _reach(k, G, D, nbr, d)
                c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
                if c2 < best_c:
                    best_v, best_c, best_r = v, c2, r2
            S[l][i] = best_v
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], best_v)
            cost, reach = best_c, best_r
            if cost < best_cost:
                best_cost, last_improve = cost, t
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
# Build: exact constructions, then a short Python voltage search for a seed,
# then the C grow-and-repair engine started from the best valid graph.
# Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    if D >= 4 and time.monotonic() - start < budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: short Python bi-Cayley search for a seed graph.
    py_deadline = start + 0.35 * budget
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

    # Phase 2: C grow-and-repair from the best valid graph.
    c_budget = start + budget - time.monotonic()
    if c_budget >= 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget - 1.5, 2)],
                             stdin_graph=(best_n, best[1]), timeout=c_budget + 2.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
