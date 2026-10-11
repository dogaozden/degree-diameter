import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltages of a bi-lift over an ARBITRARY
# finite group given by its multiplication table (read from stdin).
#
# Group G (order G, identity index 0) is supplied as a table: stdin is
# "G G*G" followed by pairs "x*G+y  x*y". Base graph: K vertices per side,
# DEG layers, each layer a permutation dJ of 0..K-1, dart e = l*K + i joins
# A_i to B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j, g*s} for all g.
# Left multiplication by G is an automorphism, so BFS from the 2K
# representatives (A_i,1) and (B_j,1) decides the diameter exactly.
# K = 1 gives bipartite Cayley graphs of G, which are not restricted to
# metacyclic groups (e.g. SL(2,q), PSL(2,q)).
#
# Cost = unreached (representative, vertex) pairs + duplicate penalty.
#
# Usage: prog d D K seed slice_seconds      (group table on stdin)
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)

static int DEG, DIAM, K, G, N, NE;
static int *tab, *invt;
static int *dI, *dJ, *dS, *adj, *cnt, *fr, *nx, *vis;
static int *bestJ, *bestS, *p;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int bfs_unreached(int src) {
    if (stamp >= 0x7ffffff0) {
        memset(vis, 0, sizeof(int) * (size_t)N);
        stamp = 0;
    }
    stamp++;
    int *cur = fr, *nxt = nx;
    int fn = 1, reached = 1;
    cur[0] = src;
    vis[src] = stamp;
    for (int lv = 0; lv < DIAM && fn > 0; lv++) {
        int nn = 0;
        for (int q = 0; q < fn; q++) {
            const int *au = adj + (size_t)cur[q] * DEG;
            for (int t = 0; t < DEG; t++) {
                int v = au[t];
                if (vis[v] != stamp) {
                    vis[v] = stamp;
                    nxt[nn++] = v;
                }
            }
        }
        reached += nn;
        int *tmp = cur; cur = nxt; nxt = tmp;
        fn = nn;
    }
    return N - reached;
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int a0 = dI[e] * G, b0 = (K + dJ[e]) * G, s = dS[e];
        for (int g = 0; g < G; g++) {
            int a = a0 + g;
            int b = b0 + tab[(size_t)g * G + s];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int src = 0; src < 2 * K; src++) {
        total += bfs_unreached(src * G);
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D K seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || (long long)m != (long long)n * n) {
        printf("0 0\n");
        return 0;
    }
    if (DEG < 1 || DIAM < 1 || K < 1 || DEG > n) {
        printf("0 0\n");
        return 0;
    }
    G = n;
    tab = malloc(sizeof(int) * (size_t)n * n);
    if (!tab) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= n * n || v < 0 || v >= n) { printf("0 0\n"); return 0; }
        tab[u] = v;
    }
    /* Check identity index 0 and build inverses. */
    invt = malloc(sizeof(int) * (size_t)n);
    for (int x = 0; x < n; x++) {
        if (tab[x] != x || tab[(size_t)x * n] != x) { printf("0 0\n"); return 0; }
    }
    for (int x = 0; x < n; x++) {
        invt[x] = -1;
        for (int y = 0; y < n; y++) {
            if (tab[(size_t)x * n + y] == 0) { invt[x] = y; break; }
        }
        if (invt[x] < 0) { printf("0 0\n"); return 0; }
    }

    N = 2 * K * G;
    NE = DEG * K;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(int));
    p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestJ || !bestS || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x51ED27ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 40000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) dS[e] = rndint(G);
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n",
                       bestJ[e] * 0 + dI[e] * G + g,
                       (K + bestJ[e]) * G + tab[(size_t)g * G + bestS[e]]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions (kept from the parent).
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
# Finite groups as multiplication tables (identity = index 0).
# ----------------------------------------------------------------------------

def _matrix_table(q, quotient):
    """Table of SL(2,q), or PSL(2,q) = SL/{+-I} when quotient is True (q odd)."""
    F = lib.GF(q)
    addt = F.add_table.tolist()
    mult = F.mul_table.tolist()
    neg = [F.neg(x) for x in range(q)]

    def canon(t):
        if not quotient:
            return t
        nt = (neg[t[0]], neg[t[1]], neg[t[2]], neg[t[3]])
        return t if t <= nt else nt

    found = set()
    for a, b, c, dd in itertools.product(range(q), repeat=4):
        if addt[mult[a][dd]][neg[mult[b][c]]] == 1:
            found.add(canon((a, b, c, dd)))
    ident = canon((1, 0, 0, 1))
    elems = [ident] + sorted(found - {ident})
    idx = {e: i for i, e in enumerate(elems)}

    def mul(x, y):
        a1, b1, c1, d1 = x
        a2, b2, c2, d2 = y
        return canon((addt[mult[a1][a2]][mult[b1][c2]],
                      addt[mult[a1][b2]][mult[b1][d2]],
                      addt[mult[c1][a2]][mult[d1][c2]],
                      addt[mult[c1][b2]][mult[d1][d2]]))

    tab = [[idx[mul(x, y)] for y in elems] for x in elems]
    return len(elems), tab


def _times_cyclic(n, tab, t):
    """Direct product of a table with Z_t; element x*t + z."""
    out = []
    for i in range(n * t):
        x, z = divmod(i, t)
        row = tab[x]
        out.append([row[y] * t + (z + w) % t for y in range(n) for w in range(t)])
    return n * t, out


_GROUP_CACHE = {}


def _make_group(spec):
    """Return (order, table) for a spec, caching a few recent tables."""
    if spec in _GROUP_CACHE:
        return _GROUP_CACHE[spec]
    if spec[0] == "mat":
        _, q, quot, t = spec
        n, tab = _matrix_table(q, quot)
        if t > 1:
            n, tab = _times_cyclic(n, tab, t)
    else:
        _, m, k, r = spec
        order, mul, _ = lib.semidirect_group(m, k, r)
        n = order
        tab = [[mul(x, y) for y in range(n)] for x in range(n)]
    if len(_GROUP_CACHE) >= 4:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[spec] = (n, tab)
    return n, tab


def _specs(lo, hi):
    """List of (order, spec) for groups with lo <= order <= hi."""
    out = []
    for q in (2, 3, 4, 5, 7, 8, 9, 11, 13):
        base = [(q * (q * q - 1), False)]
        if q % 2 == 1:
            base.append((q * (q * q - 1) // 2, True))
        for order, quot in base:
            for t in range(1, 13):
                o = order * t
                if lo <= o <= hi:
                    out.append((o, ("mat", q, quot, t)))
    for k in (2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24):
        for m in range(max(2, lo // k), hi // k + 2):
            o = m * k
            if not (lo <= o <= hi):
                continue
            rs_ = [1]  # r = 1 is the direct product, always valid
            for r in range(2, m):
                if len(rs_) >= 4:
                    break
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    rs_.append(r)
            for r in rs_:
                out.append((o, ("semi", m, k, r)))
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bi-lifts over non-cyclic groups given by multiplication tables.
    # Each run targets a total order above the current best. The floor comes
    # from a fraction of the Moore bound, so the search aims high from the start.
    moore = lib.moore_bound(d, D)
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        K = rng.choice([1, 1, 2, 2, 3])
        lo = max(best[0] // (2 * K) + 1, moore // (10 * K), d)
        hi = min(800, int(lo * (1.0 + 1.6 * rng.random())) + 4)
        specs = _specs(lo, hi)
        if not specs:
            specs = _specs(max(d, 2), 800)
        if not specs:
            break
        order, spec = rng.choice(specs)
        if order < d:
            continue
        try:
            n_g, tab = _make_group(spec)
        except ValueError:
            continue
        edges = [(x * n_g + y, row[y]) for x, row in enumerate(tab) for y in range(n_g)]

        remaining = deadline - time.monotonic()
        slice_s = min(remaining - 1.0, 12.0)
        if slice_s < 1.0:
            break
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(n_g, edges),
                timeout=slice_s + 8.0,
            )
        except RuntimeError:
            break
        try:
            nn, ee = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(nn, ee)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
