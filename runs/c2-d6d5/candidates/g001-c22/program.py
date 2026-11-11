import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: regular bipartite graph growth + 2-switch annealing.
#
# Input: a d-regular bipartite graph with diameter <= D (from Python).
# Growth step: pick d disjoint edges (a_i, b_i). Redirect each to (a_i, wB)
# and add (wA, b_i). This adds two vertices and keeps every degree equal to d
# and the graph bipartite. Repair: 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)
# that minimise the number of pairs at distance > D (exact bitset BFS).
# Only states with zero bad pairs are kept as snapshots, so output is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2000
#define WMAX ((MAXN + 63) / 64)
#define ITERS 3000
#define MAXFAIL 60

static int d_, D_, maxn_;
static int n_, m_, cap_;
static int *eu, *ev, *seu, *sev, *nb, *side, *mark, *sel, *dc, *qbuf;
static unsigned char *adj;
static uint64_t *cur, *nxt;
static unsigned char pc16[65536];
static int snap_n = -1, snap_m = 0;
static int stamp = 0;
static uint64_t rs = 1;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    return pc16[x & 0xffff] + pc16[(x >> 16) & 0xffff] +
           pc16[(x >> 32) & 0xffff] + pc16[(x >> 48) & 0xffff];
}

static void nb_replace(int v, int oldu, int newu) {
    int *p = nb + (size_t)v * d_;
    for (int k = 0; k < d_; k++)
        if (p[k] == oldu) { p[k] = newu; return; }
}

/* Number of unordered pairs at distance > D_. */
static long eval_bad(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    uint64_t *a = cur, *b = nxt;
    memset(a, 0, sizeof(uint64_t) * (size_t)n * WMAX);
    for (int v = 0; v < n; v++) a[(size_t)v * WMAX + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D_; r++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *bv = b + (size_t)v * WMAX;
            const uint64_t *av = a + (size_t)v * WMAX;
            for (int w = 0; w < W; w++) bv[w] = av[w];
            const int *p = nb + (size_t)v * d_;
            for (int k = 0; k < d_; k++) {
                const uint64_t *au = a + (size_t)p[k] * WMAX;
                for (int w = 0; w < W; w++) bv[w] |= au[w];
            }
            for (int w = 0; w < W; w++)
                if (bv[w] != av[w]) changed = 1;
        }
        uint64_t *t = a; a = b; b = t;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *av = a + (size_t)v * WMAX;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(av[w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Swap endpoints of edges i=(x1,y1), j=(x2,y2) to (x1,y2), (x2,y1).
   Applying it twice to the same (i,j) restores the original graph. */
static int do_swap(int i, int j) {
    int x1 = eu[i], y1 = ev[i], x2 = eu[j], y2 = ev[j];
    if (x1 == x2 || y1 == y2) return 0;
    if (adj[(size_t)x1 * MAXN + y2] || adj[(size_t)x2 * MAXN + y1]) return 0;
    adj[(size_t)x1 * MAXN + y1] = adj[(size_t)y1 * MAXN + x1] = 0;
    adj[(size_t)x2 * MAXN + y2] = adj[(size_t)y2 * MAXN + x2] = 0;
    adj[(size_t)x1 * MAXN + y2] = adj[(size_t)y2 * MAXN + x1] = 1;
    adj[(size_t)x2 * MAXN + y1] = adj[(size_t)y1 * MAXN + x2] = 1;
    nb_replace(x1, y1, y2);
    nb_replace(y1, x1, x2);
    nb_replace(x2, y2, y1);
    nb_replace(y2, x2, x1);
    ev[i] = y2;
    ev[j] = y1;
    return 1;
}

static void take_snapshot(void) {
    snap_n = n_;
    snap_m = m_;
    memcpy(seu, eu, sizeof(int) * (size_t)m_);
    memcpy(sev, ev, sizeof(int) * (size_t)m_);
}

/* Restore the graph given by edge arrays U, V (n vertices, m edges). */
static void rebuild(int n, int m, const int *U, const int *V) {
    for (int v = 0; v < n_; v++) memset(adj + (size_t)v * MAXN, 0, MAXN);
    n_ = n;
    m_ = m;
    for (int v = 0; v < n; v++) dc[v] = 0;
    for (int i = 0; i < m; i++) {
        int a = U[i], b = V[i];
        eu[i] = a;
        ev[i] = b;
        adj[(size_t)a * MAXN + b] = 1;
        adj[(size_t)b * MAXN + a] = 1;
        nb[(size_t)a * d_ + dc[a]++] = b;
        nb[(size_t)b * d_ + dc[b]++] = a;
    }
}

/* Add two vertices (wA on side 0, wB on side 1), keeping d-regularity. */
static int grow(void) {
    int n = n_, m = m_, d = d_;
    if (n + 2 > maxn_) return 0;
    stamp++;
    int cnt = 0;
    for (long tries = 0; cnt < d && tries < 100000; tries++) {
        int e = rndint(m);
        int a = eu[e], b = ev[e];
        if (mark[a] == stamp || mark[b] == stamp) continue;
        mark[a] = stamp;
        mark[b] = stamp;
        sel[cnt++] = e;
    }
    if (cnt < d) return 0;
    int wA = n, wB = n + 1;
    side[wA] = 0;
    side[wB] = 1;
    for (int k = 0; k < d; k++) {
        int i = sel[k];
        int a = eu[i], b = ev[i];
        /* edge i: (a, b) becomes (a, wB) */
        ev[i] = wB;
        adj[(size_t)a * MAXN + b] = 0;
        adj[(size_t)b * MAXN + a] = 0;
        adj[(size_t)a * MAXN + wB] = 1;
        adj[(size_t)wB * MAXN + a] = 1;
        nb_replace(a, b, wB);
        nb[(size_t)wB * d + k] = a;
        /* new edge m+k: (wA, b) */
        eu[m + k] = wA;
        ev[m + k] = b;
        adj[(size_t)wA * MAXN + b] = 1;
        adj[(size_t)b * MAXN + wA] = 1;
        nb_replace(b, a, wA);
        nb[(size_t)wA * d + k] = b;
    }
    n_ = n + 2;
    m_ = m + d;
    return 1;
}

/* Simulated annealing over 2-switches; returns the final bad-pair count. */
static long sa_phase(long iters, double t0, double t1, clock_t dl) {
    long cur_bad = eval_bad();
    if (cur_bad == 0) return 0;
    for (long it = 0; it < iters; it++) {
        if ((it & 31) == 0 && clock() >= dl) break;
        int i = rndint(m_), j = rndint(m_);
        if (i == j) continue;
        if (!do_swap(i, j)) continue;
        long nbad = eval_bad();
        long delta = nbad - cur_bad;
        double T = t0 + (t1 - t0) * (double)it / (double)iters;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur_bad = nbad;
            if (cur_bad == 0) break;
        } else {
            do_swap(i, j);
        }
    }
    return cur_bad;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    maxn_ = atoi(argv[5]);
    if (maxn_ > MAXN) maxn_ = MAXN;
    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }

    pc16[0] = 0;
    for (int i = 1; i < 65536; i++) pc16[i] = (unsigned char)(pc16[i >> 1] + (i & 1));

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > MAXN - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    if (n0 > maxn_) maxn_ = n0;
    cap_ = maxn_ * d_ + 2 * d_ + 8;

    int *tu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *tv = malloc(sizeof(int) * (size_t)(m0 + 1));
    adj = calloc((size_t)MAXN * MAXN, 1);
    int *deg = calloc((size_t)maxn_ + 2, sizeof(int));
    if (!tu || !tv || !adj || !deg) { printf("0 0\n"); return 0; }

    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        if (adj[(size_t)u * MAXN + v]) { ok = 0; break; }
        adj[(size_t)u * MAXN + v] = 1;
        adj[(size_t)v * MAXN + u] = 1;
        tu[i] = u;
        tv[i] = v;
        deg[u]++;
        deg[v]++;
    }
    for (int v = 0; v < n0 && ok; v++)
        if (deg[v] != d_) ok = 0;
    if (!ok) { printf("0 0\n"); return 0; }

    eu = malloc(sizeof(int) * (size_t)cap_);
    ev = malloc(sizeof(int) * (size_t)cap_);
    seu = malloc(sizeof(int) * (size_t)cap_);
    sev = malloc(sizeof(int) * (size_t)cap_);
    nb = malloc(sizeof(int) * (size_t)(maxn_ + 4) * d_);
    side = malloc(sizeof(int) * (size_t)(maxn_ + 4));
    mark = calloc((size_t)maxn_ + 4, sizeof(int));
    sel = malloc(sizeof(int) * (size_t)d_);
    dc = calloc((size_t)maxn_ + 4, sizeof(int));
    qbuf = malloc(sizeof(int) * (size_t)(maxn_ + 4));
    cur = calloc((size_t)MAXN * WMAX, sizeof(uint64_t));
    nxt = calloc((size_t)MAXN * WMAX, sizeof(uint64_t));

    for (int v = 0; v < n0; v++) dc[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u = tu[i], v = tv[i];
        nb[(size_t)u * d_ + dc[u]++] = v;
        nb[(size_t)v * d_ + dc[v]++] = u;
    }

    /* 2-colour the input; reject if not bipartite. */
    for (int v = 0; v < n0; v++) side[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int k = 0; k < d_; k++) {
                int w = nb[(size_t)u * d_ + k];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    qbuf[qt++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < m0; i++) {
        if (side[tu[i]] == 0) { eu[i] = tu[i]; ev[i] = tv[i]; }
        else                  { eu[i] = tv[i]; ev[i] = tu[i]; }
    }
    n_ = n0;
    m_ = m0;

    long bad = eval_bad();
    clock_t dl = clock() + (clock_t)(budget * (double)CLOCKS_PER_SEC);
    if (bad == 0) take_snapshot();
    int fails = 0;
    while (clock() < dl) {
        if (bad == 0) {
            take_snapshot();
            fails = 0;
            if (!grow()) break;
            bad = eval_bad();
            continue;
        }
        if (snap_n < 0) break;
        bad = sa_phase(ITERS, 1.5, 0.15, dl);
        if (bad == 0) continue;
        if (clock() >= dl) break;
        if (++fails > MAXFAIL) break;
        rebuild(snap_n, snap_m, seu, sev);
        if (!grow()) break;
        bad = eval_bad();
    }

    if (snap_n < 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++) printf("%d %d\n", seu[i], sev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent).
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent's search).
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


def _lift_search(d, D, start_n, rng, deadline):
    """Bandit over base sizes k; returns the largest (n, edges) found, or None."""
    best = None
    bn = start_n
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = bn // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= bn:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            if res[0] > bn:
                bn, best = res[0], res
    return best


def _is_regular(graph, d):
    """True if every vertex of graph has degree exactly d."""
    n, edges = graph
    if n <= 0:
        return False
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver: lift search for the first half of the budget, then C growth/repair.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(2.0, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: voltage-lift search for a regular starting graph.
    lift_end = start + 0.5 * (end - start)
    if time.monotonic() < lift_end:
        res = _lift_search(d, D, best[0], rng, lift_end)
        if res is not None:
            consider(*res)

    # Phase 2: C growth + 2-switch repair from the best regular graph.
    remaining = end - time.monotonic()
    if remaining > 4.0 and _is_regular(best, d):
        n0 = best[0]
        maxn = min(1990, n0 + max(100, n0 // 4))
        budget_c = remaining - 2.0
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget_c:.2f}", maxn],
                             stdin_graph=best, timeout=remaining + 4.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
