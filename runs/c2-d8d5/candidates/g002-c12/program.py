import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley simulated annealing over Z_m x| Z_k2.
#
# Same cost model as the Python _search below: for every vertex, count the
# block representatives NOT reached within D steps, plus a penalty per
# duplicate dart. The C loop runs one to two orders of magnitude more
# annealing steps per second than the numpy version, so many more groups
# and restarts fit in the budget.
#
# Usage: prog d D k m k2 r seed slice_seconds [iters] [patience]
# Output: "NONE", or "OK" followed by d lines, each holding k pairs "j s"
#         (layer l maps A-block i to B-block j with voltage s).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndd(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int d, D, k, m, k2, r, G, N, FULL;
static int *Ts, *Invs, *pw, *layers, *S, *nbr;
static unsigned char *reach, *tmp, *keep;
static const long PEN = 1000;
static int perm[64];

static int popc(unsigned v) { int c = 0; while (v) { c += (int)(v & 1u); v >>= 1; } return c; }

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = ((long long)a + (long long)pw[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

static void set_dart(int l, int i, int j, int s) {
    int *nb = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) nb[i * G + g] = (k + j) * G + Ts[(size_t)s * G + g];
    for (int h = 0; h < G; h++) nb[(k + j) * G + h] = i * G + Invs[(size_t)s * G + h];
}

/* Leaves the reach masks of the current state in `reach`. */
static int evalcost(void) {
    int nb2 = 2 * k;
    memset(reach, 0, (size_t)N);
    for (int b = 0; b < nb2; b++) reach[b * G] = (unsigned char)(1u << b);
    for (int t = 0; t < D; t++) {
        memcpy(tmp, reach, (size_t)N);
        for (int l = 0; l < d; l++) {
            const int *nb = nbr + (size_t)l * N;
            for (int v = 0; v < N; v++) tmp[v] |= reach[nb[v]];
        }
        unsigned char *sw = reach; reach = tmp; tmp = sw;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) cost += nb2 - popc(reach[v]);
    long dup = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            for (int l2 = 0; l2 < l; l2++)
                if (layers[l2 * k + i] == layers[l * k + i] && S[l2 * k + i] == S[l * k + i]) dup++;
    return (int)(cost + PEN * dup);
}

static void randomize(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) layers[l * k + i] = perm[i];
        for (int i = 0; i < k; i++) S[l * k + i] = rndi(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            set_dart(l, i, layers[l * k + i], S[l * k + i]);
}

static int anneal(long iters, long patience, double deadline) {
    randomize();
    int cost = evalcost();
    memcpy(keep, reach, (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int best = cost;
    long last = 0;
    for (long t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 255) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rndd() < 0.25) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int *L = layers + l * k;
            int t1 = L[i1]; L[i1] = L[i2]; L[i2] = t1;
            set_dart(l, i1, L[i1], S[l * k + i1]);
            set_dart(l, i2, L[i2], S[l * k + i2]);
            int c2 = evalcost();
            if (c2 <= cost || rndd() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(keep, reach, (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                t1 = L[i1]; L[i1] = L[i2]; L[i2] = t1;
                set_dart(l, i1, L[i1], S[l * k + i1]);
                set_dart(l, i2, L[i2], S[l * k + i2]);
            }
            continue;
        }

        int l = -1, i = -1, v = -1;
        if (rndd() < 0.4) {
            for (int tries = 0; tries < 64; tries++) {
                int u = rndi(N);
                if (keep[u] != FULL) { v = u; break; }
            }
        }
        if (v >= 0) {
            int block = v / G;
            l = rndi(d);
            if (block < k) {
                i = block;
            } else {
                int jj = block - k;
                for (int ii = 0; ii < k; ii++)
                    if (layers[l * k + ii] == jj) { i = ii; break; }
            }
        }
        if (i < 0) { l = rndi(d); i = rndi(k); }

        int old = S[l * k + i];
        int nw = rndi(G);
        if (nw == old) continue;
        S[l * k + i] = nw;
        set_dart(l, i, layers[l * k + i], nw);
        int c2 = evalcost();
        if (c2 <= cost || rndd() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(keep, reach, (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            S[l * k + i] = old;
            set_dart(l, i, layers[l * k + i], old);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d = atoi(argv[1]); D = atoi(argv[2]); k = atoi(argv[3]);
    m = atoi(argv[4]); k2 = atoi(argv[5]); r = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);
    long iters = argc > 9 ? atol(argv[9]) : 200000L;
    long patience = argc > 10 ? atol(argv[10]) : 20000L;

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > 64 || D < 1 || k < 1 || k > 4 || m < 1 || k2 < 1) { printf("NONE\n"); return 0; }
    G = m * k2;
    if (G > 2000) { printf("NONE\n"); return 0; }
    N = 2 * k * G;
    FULL = (1 << (2 * k)) - 1;

    Ts = malloc(sizeof(int) * (size_t)G * G);
    Invs = malloc(sizeof(int) * (size_t)G * G);
    pw = malloc(sizeof(int) * (size_t)k2);
    layers = malloc(sizeof(int) * (size_t)d * k);
    S = malloc(sizeof(int) * (size_t)d * k);
    nbr = malloc(sizeof(int) * (size_t)d * N);
    reach = malloc((size_t)N);
    tmp = malloc((size_t)N);
    keep = malloc((size_t)N);
    if (!Ts || !Invs || !pw || !layers || !S || !nbr || !reach || !tmp || !keep) {
        printf("NONE\n");
        return 0;
    }

    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int s = 0; s < G; s++)
        for (int x = 0; x < G; x++)
            Ts[(size_t)s * G + x] = gmul(x, s);
    for (int s = 0; s < G; s++)
        for (int x = 0; x < G; x++)
            Invs[(size_t)s * G + Ts[(size_t)s * G + x]] = x;

    double deadline = now() + slice;
    int found = 0;
    while (now() < deadline) {
        if (anneal(iters, patience, deadline)) { found = 1; break; }
    }
    if (!found) { printf("NONE\n"); return 0; }

    printf("OK\n");
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) printf("%d %d ", layers[l * k + i], S[l * k + i]);
        printf("\n");
    }
    return 0;
}
'''


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
# Edge-split pair insertion with 2-switch annealing.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (adj: list of sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _is_regular(n, edges, d):
    adj = lib.adjacency(n, edges)
    return all(len(a) == d for a in adj)


def _pair_insert(n, edges, d, D, rng, deadline, iters):
    """Try to grow a d-regular bipartite graph by two vertices. Returns (n+2, edges) or None."""
    adj0 = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj0):
        return None
    color = _bipartition(n, adj0)
    if color is None:
        return None

    adj = [set(a) for a in adj0] + [set(), set()]
    w, w2 = n, n + 1
    side1 = [v for v in range(n) if color[v] == 1]
    rng.shuffle(side1)
    used_a = set()
    picks = []
    for b in side1:
        cands = [a for a in adj[b] if a not in used_a]
        if not cands:
            continue
        a = rng.choice(cands)
        used_a.add(a)
        picks.append((a, b))
        if len(picks) == d:
            break
    if len(picks) < d:
        return None

    for a, b in picks:
        adj[a].discard(b)
        adj[b].discard(a)
        adj[w].add(b)
        adj[b].add(w)
        adj[w2].add(a)
        adj[a].add(w2)

    col = color + [0, 1]
    side0 = [v for v in range(n + 2) if col[v] == 0]
    E = []
    S = set()
    for a in side0:
        for b in adj[a]:
            E.append((a, b))
            S.add((a, b))

    N = n + 2
    cur = _bad_count(N, adj, D)
    T0 = 1.0 + 0.05 * cur
    m = len(E)
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        x1, y1 = E[i]
        x2, y2 = E[j]
        if (x1, y2) in S or (x2, y1) in S:
            continue
        adj[x1].discard(y1)
        adj[y1].discard(x1)
        adj[x2].discard(y2)
        adj[y2].discard(x2)
        adj[x1].add(y2)
        adj[y2].add(x1)
        adj[x2].add(y1)
        adj[y1].add(x2)
        new = _bad_count(N, adj, D)
        T = max(0.05, T0 * (1.0 - t / iters))
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            S.discard((x1, y1))
            S.discard((x2, y2))
            S.add((x1, y2))
            S.add((x2, y1))
            E[i] = (x1, y2)
            E[j] = (x2, y1)
        else:
            adj[x1].discard(y2)
            adj[y2].discard(x1)
            adj[x2].discard(y1)
            adj[y1].discard(x2)
            adj[x1].add(y1)
            adj[y1].add(x1)
            adj[x2].add(y2)
            adj[y2].add(x2)

    if cur != 0:
        return None
    return N, E


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d exactly.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_MAX_G = 2000   # largest group order passed to the C engine (G*G tables)
_SLICE = 1.5    # seconds of C annealing per sampled group


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
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Python simulated annealing with stagnation restarts (fallback). Returns (n, edges) or None."""
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


def _c_search(d, D, k, m, k2, r, seed, slice_s):
    """Run the C annealer on one group for slice_s seconds. Returns (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, f"{slice_s:.3f}", 200000, 20000],
                    timeout=slice_s + 30.0)
    tok = out.split()
    if not tok or tok[0] != "OK":
        return None
    vals = [int(x) for x in tok[1:]]
    if len(vals) != 2 * k * d:
        raise ValueError("malformed C output")
    G, Ts, Invs = _semidirect_tables(m, k2, r)
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    p = 0
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, vals[p], vals[p + 1])
            p += 2
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.6 * budget
    insert_deadline = start + 0.9 * budget
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main bi-Cayley search: C annealer first, Python fallback if C is unavailable.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    use_c = True

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n or G > _MAX_G:
            continue
        trials[k] += 1
        res = None
        if use_c:
            slice_s = min(_SLICE, search_deadline - time.monotonic())
            if slice_s < 0.1:
                break
            try:
                res = _c_search(d, D, k, m, k2, r, rng.randrange(1, 2 ** 31 - 1), slice_s)
            except (RuntimeError, ValueError, OSError):
                use_c = False
                res = None
        else:
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Repeated edge-split pair insertion from the best regular graph.
    if time.monotonic() < insert_deadline and _is_regular(best[0], best[1], d):
        fails = 0
        while time.monotonic() < insert_deadline and fails < 400:
            chunk = min(insert_deadline, time.monotonic() + 8.0)
            res = _pair_insert(best[0], best[1], d, D, rng, chunk, 800)
            if res is None:
                fails += 1
                continue
            fails = 0
            consider(res[0], res[1])

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
