"""Bi-Cayley voltage-lift search with a C inner engine.

Change: the simulated-annealing search over bi-Cayley voltage lifts (Z_m x| Z_k2)
now runs in a C engine (C_SOURCE). The reach/defect evaluation, which dominates
the Python version, runs in C, so each group gets far more moves and restarts in
the same time. The earlier numpy search is kept as a fallback if the C engine
fails to compile or run. Every candidate still passes lib.is_valid before use.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d exactly.
# Left multiplication is an automorphism, so the reach test only needs the
# 2k block representatives.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DLAY, DIAM, K, G, MM, K2, N;
static int POWR[256];
static int *NBR, *LAY, *VOLT;
static uint32_t *RA, *RB, *RC;
static unsigned char PC[256];
static uint32_t FULL;
static uint64_t RS = 88172645463325252ULL;

static uint64_t rnext(void) {
    RS ^= RS << 13;
    RS ^= RS >> 7;
    RS ^= RS << 17;
    return RS;
}
static int rbelow(int n) { return (int)(rnext() % (uint64_t)n); }
static double runit(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* (a,b)(c,e) = (a + r^b c, b + e) with element x = a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long aa = ((long long)a + (long long)POWR[b] * (long long)c) % MM;
    int bb = (b + e) % K2;
    return (int)aa * K2 + bb;
}

/* Write the neighbours of A-block i and B-block LAY[l*K+i] in layer l. */
static void set_dart(int l, int i) {
    int p = LAY[l * K + i], s = VOLT[l * K + i];
    int A = i * G, B = (K + p) * G;
    int *nb = NBR + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        nb[A + g] = B + h;
        nb[B + h] = A + g;
    }
}

/* Number of pairs of entries with the same (i, p, s): each is a duplicate edge. */
static int dupcount(void) {
    int c = 0;
    int tot = DLAY * K;
    for (int a = 0; a < tot; a++) {
        for (int b = a + 1; b < tot; b++) {
            if (a % K == b % K && LAY[a] == LAY[b] && VOLT[a] == VOLT[b]) c++;
        }
    }
    return c;
}

/* R[v] bit b is set when dist(v, rep_b) <= DIAM. */
static void compute_reach(uint32_t *R, uint32_t *T) {
    for (int v = 0; v < N; v++) R[v] = 0;
    for (int b = 0; b < 2 * K; b++) R[b * G] |= (1u << b);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = R[v];
            for (int l = 0; l < DLAY; l++) x |= R[NBR[(size_t)l * N + v]];
            T[v] = x;
            changed |= (x != R[v]);
        }
        memcpy(R, T, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
}

static long long unreached(const uint32_t *R) {
    long long c = 0;
    for (int v = 0; v < N; v++) c += (long long)(2 * K) - (long long)PC[R[v] & 255u];
    return c;
}

static long long total_cost(const uint32_t *R) {
    return unreached(R) + 1000LL * (long long)dupcount();
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    MM = atoi(argv[6]);
    K2 = atoi(argv[7]);
    int RR = atoi(argv[8]);
    if (d < 1 || D < 1 || K < 1 || K > 4 || MM < 2 || K2 < 1 || K2 > 200) {
        printf("0 0\n");
        return 0;
    }
    DLAY = d;
    DIAM = D;
    G = MM * K2;
    N = 2 * K * G;
    FULL = (1u << (2 * K)) - 1u;
    RS = (uint64_t)seed * 2654435761ULL + 88172645463325252ULL;
    if (RS == 0) RS = 1;

    POWR[0] = 1 % MM;
    for (int t = 1; t < K2; t++) POWR[t] = (int)((long long)POWR[t - 1] * RR % MM);

    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        PC[x] = (unsigned char)c;
    }

    NBR = malloc(sizeof(int) * (size_t)d * (size_t)N);
    LAY = malloc(sizeof(int) * (size_t)d * (size_t)K);
    VOLT = malloc(sizeof(int) * (size_t)d * (size_t)K);
    RA = malloc(sizeof(uint32_t) * (size_t)N);
    RB = malloc(sizeof(uint32_t) * (size_t)N);
    RC = malloc(sizeof(uint32_t) * (size_t)N);
    if (!NBR || !LAY || !VOLT || !RA || !RB || !RC) {
        printf("0 0\n");
        return 0;
    }

    const int ITERS = 20000;
    const int PATIENCE = 4000;
    double deadline = now_s() + limit;
    int found = 0;

    while (!found && now_s() < deadline) {
        /* Random layers (permutations) and random voltages. */
        for (int l = 0; l < d; l++) {
            int perm[4];
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rbelow(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            for (int i = 0; i < K; i++) {
                LAY[l * K + i] = perm[i];
                VOLT[l * K + i] = rbelow(G);
                set_dart(l, i);
            }
        }
        compute_reach(RA, RC);
        long long cost = total_cost(RA);
        double c0 = cost > 1 ? (double)cost : 1.0;
        long long best = cost;
        int last = 0;

        for (int t = 0; t < ITERS && cost != 0; t++) {
            if (t - last > PATIENCE) break;
            if ((t & 31) == 0 && now_s() >= deadline) break;
            double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
            if (temp < 0.5) temp = 0.5;

            if (K >= 2 && runit() < 0.25) {
                /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
                int l = rbelow(d);
                int i1 = rbelow(K);
                int i2 = rbelow(K - 1);
                if (i2 >= i1) i2++;
                int tmp = LAY[l * K + i1];
                LAY[l * K + i1] = LAY[l * K + i2];
                LAY[l * K + i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
                compute_reach(RB, RC);
                long long c2 = total_cost(RB);
                if (c2 <= cost || runit() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                    memcpy(RA, RB, sizeof(uint32_t) * (size_t)N);
                    if (cost < best) {
                        best = cost;
                        last = t;
                    }
                } else {
                    tmp = LAY[l * K + i1];
                    LAY[l * K + i1] = LAY[l * K + i2];
                    LAY[l * K + i2] = tmp;
                    set_dart(l, i1);
                    set_dart(l, i2);
                }
                continue;
            }

            /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
            int l = rbelow(d);
            int i = rbelow(K);
            if (runit() < 0.4) {
                int nbad = 0;
                for (int v = 0; v < N; v++)
                    if (RA[v] != FULL) nbad++;
                if (nbad > 0) {
                    int pick = rbelow(nbad);
                    int u = -1;
                    for (int v = 0; v < N; v++) {
                        if (RA[v] != FULL) {
                            if (pick == 0) {
                                u = v;
                                break;
                            }
                            pick--;
                        }
                    }
                    if (u >= 0) {
                        int block = u / G;
                        if (block < K) {
                            i = block;
                        } else {
                            int target = block - K;
                            for (int ii = 0; ii < K; ii++) {
                                if (LAY[l * K + ii] == target) {
                                    i = ii;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            int old = VOLT[l * K + i];
            int nw = rbelow(G);
            if (nw == old) continue;
            VOLT[l * K + i] = nw;
            set_dart(l, i);
            compute_reach(RB, RC);
            long long c2 = total_cost(RB);
            if (c2 <= cost || runit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(RA, RB, sizeof(uint32_t) * (size_t)N);
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                VOLT[l * K + i] = old;
                set_dart(l, i);
            }
        }
        if (cost == 0) found = 1;
    }

    if (found) {
        int E = d * K * G;
        printf("%d %d\n", N, E);
        for (int l = 0; l < d; l++) {
            for (int u = 0; u < K * G; u++) {
                printf("%d %d\n", u, NBR[(size_t)l * N + u]);
            }
        }
    } else {
        printf("0 0\n");
    }
    free(NBR);
    free(LAY);
    free(VOLT);
    free(RA);
    free(RB);
    free(RC);
    return 0;
}
"""


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type: (a,b)(c,e) = (a + (-1)^b c, b+e)
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (used only by the Python fallback)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
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
    """Python fallback: simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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


def _c_search(d, D, seed, k, m, k2, r, budget):
    """Run the C engine on one group. Returns (ok, result); ok is False if the engine could not run."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", k, m, k2, r],
                        timeout=budget + 15.0)
        n, edges = lib.parse_graph_text(out)
    except Exception:
        return False, None
    if n <= 0 or not edges:
        return True, None
    return True, (n, edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    c_ok = True

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break

        res = None
        if c_ok:
            ok, res = _c_search(d, D, rng.randrange(1 << 30), k, m, k2, r, min(3.0, remaining))
            c_ok = ok
        if not c_ok:
            Gt, Ts, Invs = _semidirect_tables(m, k2, r)
            res = _search(d, D, k, Gt, Ts, Invs, rng, deadline, 4000, 1200)

        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
