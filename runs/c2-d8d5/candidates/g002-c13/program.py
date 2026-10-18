"""Bi-Cayley lift search with a native C annealer.

New in this version:
  * The whole annealing loop (group sampling, bi-Cayley lift, uint8 reach
    bitsets over the 2k block representatives, defect-targeted and layer-swap
    moves, stagnation restarts) runs in C, so each evaluation is roughly
    10-50x cheaper than the Python/numpy version. That gives many more
    restarts per case.
  * The C engine has its own bandit over base sizes k and samples
    Z_m x| Z_k2 groups near the current best order, using wall-clock time.
  * D >= 5 no longer computes the W(q) quadrangle (it only helps at D = 4 and
    cost about 10 s of Python).
  * The previous Python annealer remains as a fallback if the C build or run
    fails. Every returned graph is checked with lib.is_valid.
"""
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

#define MAXK 4
#define MAXD 64
#define PEN 1000LL
#define ITERS 20000
#define PATIENCE 4000
#define MAXN 200000

static int d, D, K, G, N;
static int Gm, Gk2;
static int pw[64];
static int lay[MAXD][MAXK];
static int Sv[MAXD][MAXK];
static int *nbr = NULL;
static uint8_t *reachA = NULL, *reachB = NULL, *reachC = NULL;
static uint8_t pop8[256];
static uint64_t rs = 88172645463325252ULL;

static int bestN = 0, bestK = 0, bestG = 0, bestD = 0;
static int *bestNbr = NULL;

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x| Z_k2; element a*k2+b; (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a1 = x / Gk2, b1 = x % Gk2;
    int a2 = y / Gk2, b2 = y % Gk2;
    int a = (int)(((long long)pw[b1] * a2 + a1) % Gm);
    int b = (b1 + b2) % Gk2;
    return a * Gk2 + b;
}

static void setup_group(int m, int k2, int r) {
    Gm = m;
    Gk2 = k2;
    for (int t = 0; t < k2; t++) pw[t] = (int)pmod(r, t, m);
}

/* Vertices: A block i = i*G + g (i < K); B block j = (K+j)*G + h.
   Layer l joins A_{i,g} to B_{lay[l][i], g*s} with s = Sv[l][i]. */
static void set_layer(int l) {
    int *nb = nbr + (size_t)l * N;
    for (int i = 0; i < K; i++) {
        int j = lay[l][i], s = Sv[l][i];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + gmul(g, s);
            nb[a] = b;
            nb[b] = a;
        }
    }
}

/* Number of duplicate (i, j, s) darts; each duplicate is a multi-edge. */
static int dupcount(void) {
    int cnt = 0;
    for (int i = 0; i < K; i++) {
        for (int l = 0; l < d; l++) {
            int j = lay[l][i], s = Sv[l][i];
            for (int l2 = 0; l2 < l; l2++) {
                if (lay[l2][i] == j && Sv[l2][i] == s) { cnt++; break; }
            }
        }
    }
    return cnt;
}

/* out[v] = bit b set iff block representative b is within distance D of v.
   Cost = number of unreached (representative, vertex) pairs + penalty. */
static long long total_cost(uint8_t *out, uint8_t *scratch) {
    long long un = 2LL * K * N;
    memset(out, 0, (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[(size_t)b * G] |= (uint8_t)(1u << b);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t r = out[v];
            for (int l = 0; l < d; l++) r |= out[nbr[(size_t)l * N + v]];
            scratch[v] = r;
            if (r != out[v]) changed = 1;
        }
        memcpy(out, scratch, (size_t)N);
        if (!changed) break;
    }
    for (int v = 0; v < N; v++) un -= pop8[out[v]];
    return un + PEN * (long long)dupcount();
}

static int search(double deadline) {
    int full = (1 << (2 * K)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = tmp;
        }
        for (int i = 0; i < K; i++) Sv[l][i] = rndint(G);
        set_layer(l);
    }
    long long cost = total_cost(reachA, reachC);
    double c0 = (double)(cost > 1 ? cost : 1);
    long long best = cost;
    int last = 0;

    for (int t = 0; t < ITERS && cost != 0; t++) {
        if (t - last > PATIENCE) break;
        if ((t & 15) == 0 && now_sec() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            /* layer-swap move */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_layer(l);
            long long c2 = total_cost(reachB, reachC);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint8_t *sw = reachA; reachA = reachB; reachB = sw;
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
                set_layer(l);
            }
            continue;
        }

        /* voltage move, defect-targeted with probability 0.4 */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int start = rndint(N);
            for (int q = 0; q < N; q++) {
                int v = start + q;
                if (v >= N) v -= N;
                if (reachA[v] != full) {
                    int block = v / G;
                    l = rndint(d);
                    if (block < K) {
                        i = block;
                    } else {
                        for (int ii = 0; ii < K; ii++) {
                            if (lay[l][ii] == block - K) { i = ii; break; }
                        }
                    }
                    break;
                }
            }
        }
        if (i < 0) {
            l = rndint(d);
            i = rndint(K);
        }
        int old = Sv[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        Sv[l][i] = nw;
        set_layer(l);
        long long c2 = total_cost(reachB, reachC);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint8_t *sw = reachA; reachA = reachB; reachB = sw;
            if (cost < best) { best = cost; last = t; }
        } else {
            Sv[l][i] = old;
            set_layer(l);
        }
    }
    return cost == 0;
}

static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int target, int *om, int *ok2, int *orr) {
    for (int tr = 0; tr < 200; tr++) {
        int k2 = K2S[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
        } else if (k2 > 1 && m > 2) {
            int found = 0;
            for (int q = 0; q < 60 && !found; q++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) == 1 && pmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                }
            }
            if (!found) continue;
        }
        *om = m;
        *ok2 = k2;
        *orr = r;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double T = atof(argv[4]);
    int minN = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        pop8[x] = (uint8_t)c;
    }
    bestN = minN;
    double t0 = now_sec();
    double deadline = t0 + T;
    int trials[MAXK + 1] = {0};
    int wins[MAXK + 1] = {0};

    while (now_sec() < deadline) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        int base = bestN / (2 * k);
        int span = base / 8 + 1;
        if (span < 2) span = 2;
        int target = base + 1 + rndint(span);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        K = k;
        G = m * k2;
        N = 2 * K * G;
        if (N <= bestN || N > MAXN) continue;
        setup_group(m, k2, r);
        nbr = malloc(sizeof(int) * (size_t)d * N);
        reachA = malloc((size_t)N);
        reachB = malloc((size_t)N);
        reachC = malloc((size_t)N);
        if (!nbr || !reachA || !reachB || !reachC) {
            free(nbr); free(reachA); free(reachB); free(reachC);
            nbr = NULL; reachA = reachB = reachC = NULL;
            break;
        }
        trials[k]++;
        int ok = search(deadline);
        if (ok) {
            wins[k]++;
            bestN = N;
            bestK = K;
            bestG = G;
            bestD = d;
            free(bestNbr);
            bestNbr = malloc(sizeof(int) * (size_t)d * N);
            if (bestNbr) memcpy(bestNbr, nbr, sizeof(int) * (size_t)d * N);
        }
        free(nbr); free(reachA); free(reachB); free(reachC);
        nbr = NULL;
        reachA = reachB = reachC = NULL;
    }

    if (bestNbr == NULL || bestN <= minN) {
        printf("0 0\n");
        return 0;
    }
    int A = bestK * bestG;
    printf("%d %d\n", bestN, bestD * A);
    for (int u = 0; u < A; u++) {
        for (int l = 0; l < bestD; l++) {
            printf("%d %d\n", u, bestNbr[(size_t)l * bestN + u]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact and algebraic baselines.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add vertices with spare degree, accepting only valid graphs.
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
# Python fallback: bi-Cayley lifts over Z_m x| Z_k2 with simulated annealing.
# Used only if the C engine cannot be compiled or run.
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b)."""
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


def _python_search(d, D, best, rng, deadline):
    """Fallback annealing loop (Python). Returns the best valid (n, edges) found."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        best_n = best[0]
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            wins[k] += 1
            best = res
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    budget = max(2.0, min(0.75 * time_limit, time_limit - 10.0))
    c_deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 8.0)

    # Exact constructions. Calibration cases return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < c_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: native C annealer, with the Python loop as fallback.
    if time.monotonic() < c_deadline:
        used_c = False
        if 3 <= d <= 60:
            try:
                remaining = time_limit - 4.0 - (time.monotonic() - start)
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]],
                                timeout=max(3.0, remaining))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
                used_c = True
            except (RuntimeError, ValueError):
                used_c = False
        if not used_c:
            best = _python_search(d, D, best, rng, c_deadline)

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
