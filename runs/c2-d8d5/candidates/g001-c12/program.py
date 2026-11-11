"""Bi-Cayley voltage search seeds a C engine. The C engine grows a regular bipartite
graph by vertex-pair insertion (two new vertices, degree preserved) and then repairs
diameter defects with 2-switch simulated annealing, restarting from the last valid snapshot."""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6000
#define MAXD 16
#define MAXW ((MAXN + 63) / 64)
#define EPOCH_MAX 3000
#define PATIENCE 1200

typedef uint64_t u64;

static int N = 0, DEG = 0, DIAM = 0;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int side[MAXN];

static int snapN = 0;
static int snapAdj[MAXN][MAXD];
static int snapDeg[MAXN];
static int snapSide[MAXN];

static int bestN = -1;
static int bestAdj[MAXN][MAXD];
static int bestDeg[MAXN];

static u64 BUFA[MAXN * MAXW];
static u64 BUFB[MAXN * MAXW];

static u64 rs = 88172645463325252ULL;
static clock_t T0;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (u64)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_idx(int v, int u) {
    for (int i = 0; i < deg[v]; i++)
        if (adj[v][i] == u) return i;
    return -1;
}

static void repl(int v, int old, int nw) {
    int i = find_idx(v, old);
    if (i >= 0) adj[v][i] = nw;
}

/* Number of unordered pairs at distance > DIAM. Zero means valid diameter. */
static long long eval_cost(void) {
    int n = N;
    int W = (n + 63) >> 6;
    u64 *cur = BUFA, *nxt = BUFB;
    for (int v = 0; v < n; v++) {
        u64 *r = cur + (size_t)v * MAXW;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DIAM; it++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            u64 *o = nxt + (size_t)v * MAXW;
            u64 *c = cur + (size_t)v * MAXW;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v][i] * MAXW;
                for (int w = 0; w < W; w++) o[w] |= q[w];
            }
            for (int w = 0; w < W; w++)
                if (o[w] != c[w]) { changed = 1; break; }
        }
        u64 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long unreached = 0;
    for (int v = 0; v < n; v++) {
        u64 *c = cur + (size_t)v * MAXW;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(c[w]);
        unreached += n - pc;
    }
    return unreached / 2;
}

/* Add edges between deficient opposite-side vertices (never breaks validity). */
static void greedy_fill(void) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int a = 0; a < N; a++) {
            if (side[a] != 0 || deg[a] >= DEG) continue;
            for (int b = 0; b < N && deg[a] < DEG; b++) {
                if (side[b] != 1 || deg[b] >= DEG) continue;
                if (find_idx(a, b) >= 0) continue;
                adj[a][deg[a]++] = b;
                adj[b][deg[b]++] = a;
                changed = 1;
            }
        }
    }
}

/* Regular-graph growth: new A-vertex w joined to b_1..b_d (B side), new B-vertex z joined
   to x_1..x_d (A side), where each edge (b_i, x_i) is removed. Degrees stay d, graph stays
   simple and bipartite, and the order rises by 2. */
static int try_grow(void) {
    if (N + 2 > MAXN || N < 4) return 0;
    for (int v = 0; v < N; v++)
        if (deg[v] != DEG) return 0;
    int bs[MAXD], xs[MAXD], nb = 0;
    for (int tries = 0; nb < DEG && tries < 4000; tries++) {
        int b = rndint(N);
        if (side[b] != 1) continue;
        int bad = 0;
        for (int j = 0; j < nb; j++)
            if (bs[j] == b) bad = 1;
        if (bad) continue;
        int x = adj[b][rndint(deg[b])];
        for (int j = 0; j < nb; j++)
            if (xs[j] == x) bad = 1;
        if (bad) continue;
        bs[nb] = b;
        xs[nb] = x;
        nb++;
    }
    if (nb < DEG) return 0;
    int w = N, z = N + 1;
    side[w] = 0;
    side[z] = 1;
    deg[w] = DEG;
    deg[z] = DEG;
    for (int i = 0; i < DEG; i++) {
        int b = bs[i], x = xs[i];
        repl(b, x, w);
        repl(x, b, z);
        adj[w][i] = b;
        adj[z][i] = x;
    }
    N += 2;
    return 1;
}

static int pick_side(int s) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* 2-switch on A-B edges: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees are preserved. */
static int propose(int *a1, int *b1, int *a2, int *b2) {
    int x = pick_side(0), y = pick_side(0);
    if (x < 0 || y < 0 || x == y) return 0;
    *a1 = x;
    *a2 = y;
    *b1 = adj[x][rndint(deg[x])];
    *b2 = adj[y][rndint(deg[y])];
    if (*b1 == *b2) return 0;
    if (find_idx(x, *b2) >= 0 || find_idx(y, *b1) >= 0) return 0;
    return 1;
}

static void apply_sw(int a1, int b1, int a2, int b2) {
    repl(a1, b1, b2);
    repl(b2, a2, a1);
    repl(a2, b2, b1);
    repl(b1, a1, a2);
}

static void undo_sw(int a1, int b1, int a2, int b2) {
    repl(a1, b2, b1);
    repl(b1, a2, a1);
    repl(a2, b1, b2);
    repl(b2, a1, a2);
}

static void snap_save(void) {
    snapN = N;
    memcpy(snapAdj, adj, sizeof(int) * MAXD * (size_t)N);
    memcpy(snapDeg, deg, sizeof(int) * (size_t)N);
    memcpy(snapSide, side, sizeof(int) * (size_t)N);
}

static void snap_load(void) {
    N = snapN;
    memcpy(adj, snapAdj, sizeof(int) * MAXD * (size_t)N);
    memcpy(deg, snapDeg, sizeof(int) * (size_t)N);
    memcpy(side, snapSide, sizeof(int) * (size_t)N);
}

static void best_save(void) {
    bestN = N;
    memcpy(bestAdj, adj, sizeof(int) * MAXD * (size_t)N);
    memcpy(bestDeg, deg, sizeof(int) * (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 5) return 0;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    T0 = clock();

    if (DEG < 1 || DEG > MAXD || DIAM < 1) { printf("0 0\n"); return 0; }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    memset(deg, 0, sizeof(deg));
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (find_idx(u, v) >= 0) continue;
        if (deg[u] >= DEG || deg[v] >= DEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    /* Bipartition by BFS; abort on odd cycle. */
    static int qbuf[MAXN];
    for (int i = 0; i < n; i++) side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    qbuf[qt++] = v;
                } else if (side[v] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    greedy_fill();
    long long cost = eval_cost();
    long long epStart = cost, epBest = cost;
    int epIt = 0, lastImp = 0;

    while (elapsed() < tl) {
        if (cost == 0) {
            if (N > bestN) best_save();
            snap_save();
            if (try_grow()) {
                cost = eval_cost();
                epStart = cost;
                epBest = cost;
                epIt = 0;
                lastImp = 0;
            } else {
                int a1, b1, a2, b2;
                if (propose(&a1, &b1, &a2, &b2)) {
                    apply_sw(a1, b1, a2, b2);
                    if (eval_cost() != 0) undo_sw(a1, b1, a2, b2);
                }
            }
            continue;
        }

        epIt++;
        int a1, b1, a2, b2;
        if (!propose(&a1, &b1, &a2, &b2)) {
            if (epIt >= EPOCH_MAX) { snap_load(); cost = 0; }
            continue;
        }
        apply_sw(a1, b1, a2, b2);
        long long c2 = eval_cost();
        double frac = (double)epIt / EPOCH_MAX;
        if (frac > 1.0) frac = 1.0;
        double T = 0.2 + (0.005 * (double)epStart + 0.5) * (1.0 - frac);
        int acc = (c2 <= cost);
        if (!acc) acc = rnd01() < exp(-(double)(c2 - cost) / T);
        if (acc) cost = c2;
        else undo_sw(a1, b1, a2, b2);

        if (cost < epBest) { epBest = cost; lastImp = epIt; }
        if (cost == 0) {
            if (N > bestN) best_save();
            continue;
        }
        if (epIt - lastImp > PATIENCE || epIt >= EPOCH_MAX) {
            snap_load();
            cost = 0;
        }
    }

    if (bestN < 0) { printf("0 0\n"); return 0; }
    long long twice = 0;
    for (int v = 0; v < bestN; v++) twice += bestDeg[v];
    printf("%d %lld\n", bestN, twice / 2);
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestDeg[v]; i++) {
            int u = bestAdj[v][i];
            if (v < u) printf("%d %d\n", v, u);
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (seed generator).
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    hard_end = t0 + max(2.0, time_limit - 8.0)
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

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1 (Python): bi-Cayley voltage search for a regular seed, about 35% of the budget.
    py_end = t0 + 0.35 * (hard_end - t0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < py_end:
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
        res = _search(d, D, k, G, Ts, Invs, rng, py_end, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    n2, e2 = _slack_extend(best[0], best[1], d, D, rng, py_end)
    consider(n2, e2)

    # Phase 2 (C): vertex-pair insertion with 2-switch annealing and snapshot restarts.
    c_budget = hard_end - time.monotonic() - 1.0
    if c_budget >= 2.0 and d <= 16:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                            stdin_graph=best, timeout=c_budget + 8.0)
            n3, e3 = lib.parse_graph_text(out)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
