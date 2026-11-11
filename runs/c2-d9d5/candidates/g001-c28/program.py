"""Bi-Cayley lift search for bipartite graphs with max degree d and diameter D.

Structure: exact constructions first (PG(2,q) incidence, W(q) quadrangle), then a C
engine that runs simulated annealing over semidirect-product bi-Cayley lifts
Z_m x| Z_k2 with k base blocks per side. The C search is the main engine. Python
falls back to the older pure-Python annealing only if the C run fails.

Change in this version: the annealing moved into C_SOURCE. Reachability is a bitmask
per vertex, so each move costs O(N*d*D) in C instead of many numpy calls. This gives
roughly 10-50x more moves per second, so each group/voltage restart gets far more
iterations before it stagnates.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley simulated annealing over Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, G = m*k2.
# Layer l pairs A_i with B_{layers[l][i]} via voltage s: A_{i,g} ~ B_{j,g*s}.
# Each layer is a perfect matching of blocks, so every vertex has degree d.
# Cost = (number of (block representative, vertex) pairs at distance > D)
#        + PEN * (duplicate dart keys). Cost 0 means a valid graph.
#
# Usage: prog d D seed budget_seconds [min_n]
# Prints "n m" and the edges of the largest valid graph with n > min_n,
# or "0 0" if none was found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 4
#define MAXG 3000
#define MAXN (2 * MAXK * MAXG)
#define PEN 1000
#define ITERS 40000
#define PATIENCE 6000

static int d_, D_, k_, G_, N_;
static int m_, k2_;
static long long pw_[64];
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static int best_nbr[MAXD][MAXN];
static int best_d, best_k, best_G, best_N;
static uint8_t sc1[MAXN], sc2[MAXN], ra[MAXN], rb[MAXN];
static uint8_t *RC, *RN;
static int pc8[256];
static uint64_t rs;
static clock_t t_start;
static double budget_s;

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) {
    if (n <= 0) return 0;
    return (int)(rnext() % (uint64_t)n);
}

static double rdbl(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC;
}

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long long gcd_ll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Semidirect product Z_m x| Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int k2 = k2_;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    int aa = (int)(((long long)a + pw_[b] * (long long)c) % m_);
    int bb = (b + e) % k2;
    return aa * k2 + bb;
}

static int ginv(int x) {
    int k2 = k2_;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = (pw_[nb] * (long long)a) % m_;
    int aa = (int)((m_ - t) % m_);
    return aa * k2 + nb;
}

static void set_dart(int l, int i, int j, int s) {
    int G = G_, k = k_;
    int is = ginv(s);
    int *nb = nbr[l];
    for (int g = 0; g < G; g++) {
        nb[i * G + g] = (k + j) * G + gmul(g, s);
        nb[(k + j) * G + g] = i * G + gmul(g, is);
    }
}

/* Writes the reach bitmask per vertex into out; returns the number of unreached pairs. */
static long compute_reach(uint8_t *out) {
    int N = N_, G = G_, k = k_, d = d_;
    uint8_t *cur = sc1, *nxt = sc2;
    memset(cur, 0, (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[b * G] = (uint8_t)(1u << b);
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint8_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    memcpy(out, cur, (size_t)N);
    long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * k - pc8[out[v]];
    return unr;
}

static int dupcount(void) {
    int k = k_, dk = d_ * k_, dup = 0;
    for (int x = 0; x < dk; x++) {
        int l = x / k, i = x % k, j = layers[l][i], s = S[l][i];
        for (int y = 0; y < x; y++) {
            int l2 = y / k, i2 = y % k;
            if (i2 == i && layers[l2][i2] == j && S[l2][i2] == s) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static long full_cost(uint8_t *out) {
    long unr = compute_reach(out);
    return unr + (long)PEN * (long)dupcount();
}

static const int K2OPT[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Sets m_, k2_, pw_, G_ for a group of order >= target. Returns 1 on success. */
static int sample_group(int target) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2OPT[rint_(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long long r = 1;
        if (k2 == 2 && rdbl() < 0.3) {
            r = m - 1; /* dihedral type, always valid */
        } else if (k2 > 1 && m > 2) {
            for (int t = 0; t < 60; t++) {
                long long c = 2 + rint_(m - 2);
                if (gcd_ll(c, m) == 1 && pmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }
        m_ = m;
        k2_ = k2;
        pw_[0] = 1 % m;
        for (int b = 1; b < k2; b++) pw_[b] = (pw_[b - 1] * r) % m;
        G_ = m * k2;
        if (G_ > MAXG) continue;
        return 1;
    }
    return 0;
}

/* Simulated annealing from a random state. Returns 1 if a cost-0 state was reached. */
static int run_search(int iters, int patience) {
    int d = d_, k = k_, G = G_, N = N_;
    uint8_t full = (uint8_t)((1u << (2 * k)) - 1);

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            S[l][i] = rint_(G);
            set_dart(l, i, layers[l][i], S[l][i]);
        }
    }

    RC = ra;
    RN = rb;
    long cost = full_cost(RC);
    double c0 = (double)(cost > 1 ? cost : 1);
    long best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (elapsed() > budget_s) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        double x = rdbl();

        if (k >= 2 && x < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rint_(d);
            int i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = tmp;
            set_dart(l, i1, layers[l][i1], S[l][i1]);
            set_dart(l, i2, layers[l][i2], S[l][i2]);
            long c2 = full_cost(RN);
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint8_t *sw = RC;
                RC = RN;
                RN = sw;
                if (cost < best_cost) {
                    best_cost = cost;
                    last = t;
                }
            } else {
                tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                set_dart(l, i1, layers[l][i1], S[l][i1]);
                set_dart(l, i2, layers[l][i2], S[l][i2]);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int u = -1;
        if (rdbl() < 0.4) {
            int nbad = 0;
            for (int v = 0; v < N; v++)
                if (RC[v] != full) nbad++;
            if (nbad > 0) {
                int pick = rint_(nbad);
                for (int v = 0; v < N; v++) {
                    if (RC[v] != full) {
                        if (pick == 0) {
                            u = v;
                            break;
                        }
                        pick--;
                    }
                }
            }
        }
        int l, i;
        if (u >= 0) {
            int block = u / G;
            l = rint_(d);
            if (block < k) {
                i = block;
            } else {
                i = -1;
                for (int ii = 0; ii < k; ii++)
                    if (layers[l][ii] == block - k) {
                        i = ii;
                        break;
                    }
                if (i < 0) i = rint_(k);
            }
        } else {
            l = rint_(d);
            i = rint_(k);
        }

        int old = S[l][i];
        int nw = rint_(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i, layers[l][i], nw);
        long c2 = full_cost(RN);
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint8_t *sw = RC;
            RC = RN;
            RN = sw;
            if (cost < best_cost) {
                best_cost = cost;
                last = t;
            }
        } else {
            S[l][i] = old;
            set_dart(l, i, layers[l][i], old);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget [min_n]\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget_s = atof(argv[4]);
    long min_n = argc > 5 ? atol(argv[5]) : 0;
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    d_ = d;
    D_ = D;
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 4; i++) rnext();
    for (int i = 0; i < 256; i++) pc8[i] = (i ? pc8[i >> 1] : 0) + (i & 1);

    t_start = clock();
    best_N = 0;
    best_d = d;
    best_k = 0;
    best_G = 0;
    long best_n = min_n;
    int trials[MAXK + 1], wins[MAXK + 1];
    for (int i = 0; i <= MAXK; i++) {
        trials[i] = 0;
        wins[i] = 0;
    }

    while (elapsed() < budget_s) {
        int k;
        if (rdbl() < 0.2) {
            k = 1 + rint_(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rdbl();
                if (sc > bs) {
                    bs = sc;
                    k = kk;
                }
            }
        }
        long base = best_n / (2L * k);
        long span = base / 8 + 1;
        if (span < 2) span = 2;
        long target = base + 1 + (long)rint_((int)span);
        if (target < 2) target = 2;
        if (!sample_group((int)target)) continue;
        k_ = k;
        N_ = 2 * k * G_;
        if ((long)N_ <= best_n) continue;
        trials[k]++;
        int ok = run_search(ITERS, PATIENCE);
        if (ok) {
            wins[k]++;
            best_d = d;
            best_k = k;
            best_G = G_;
            best_N = N_;
            for (int l = 0; l < d; l++) memcpy(best_nbr[l], nbr[l], sizeof(int) * (size_t)N_);
            best_n = N_;
        }
    }

    if (best_N == 0) {
        printf("0 0\n");
        return 0;
    }
    int V = best_k * best_G;
    long M = (long)V * best_d;
    printf("%d %ld\n", best_N, M);
    for (int u = 0; u < V; u++)
        for (int l = 0; l < best_d; l++)
            printf("%d %d\n", u, best_nbr[l][u]);
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
# Python fallback: the same bi-Cayley annealing, used only if the C engine fails.
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

    # Main search: the C engine runs bi-Cayley annealing over the remaining budget.
    c_ok = False
    if 2 <= d <= 32 and time.monotonic() < deadline - 1.0:
        c_budget = deadline - time.monotonic() - 0.5
        remaining = time_limit - (time.monotonic() - start)
        timeout = max(2.0, min(c_budget + 4.0, remaining - 4.0))
        try:
            out = lib.run_c(C_SOURCE, [d, D, abs(int(seed)) % (1 << 62), round(c_budget, 2), best_n],
                            timeout=timeout)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
            c_ok = True
        except Exception:
            c_ok = False

    # Python fallback, used only if the C engine failed.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while not c_ok and time.monotonic() < deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
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
