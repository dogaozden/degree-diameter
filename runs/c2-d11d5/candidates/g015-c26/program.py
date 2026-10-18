"""Combined program: a Python bi-Cayley lift search as a safe baseline, then a C lift engine.

The C engine is a new construction path for large targets. It samples semidirect products
Z_m x| Z_k2 with k base vertices per side, anneals layer permutations and voltages, checks
each success with a full all-pairs bitset diameter test, and ratchets the order goal upward.
Every returned graph is checked with lib.is_valid, and K_{d,d} or a known construction is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer over semidirect products Z_m x|_r Z_k2.
 * Usage:  prog d D seed time_limit [baseline_n]   (stdin is ignored)
 * stdout: "n m" + edges of the best valid graph found, or "0 0".
 *
 * Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h.
 * Layer l joins A_i to B_{perm[l][i]} with voltage s: A_{i,g} ~ B_{p, g*s}.
 * Every layer is a permutation, so every vertex has degree d.
 * Left multiplication is an automorphism, so the diameter test only needs
 * distances from the 2K block representatives. A final full bitset check is run on success.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXK 32
#define MAXDEG 32
#define PEN 1000L

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ---- group Z_gm x|_r Z_gk2, element a*gk2 + b ---- */
static int gm, gk2, G;
static long long gpw[64];

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    G = m * k2;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        gpw[b] = p;
        p = p * r % m;
    }
}

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2;
    int c = y / gk2, e = y % gk2;
    long long t = ((long long)a + gpw[b] * c) % gm;
    return (int)(t * gk2 + (b + e) % gk2);
}

static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long long t = (gpw[nb] * a) % gm;
    long long na = (gm - t) % gm;
    return (int)(na * gk2 + nb);
}

static void sample_group(long target) {
    static const int K2S[16] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30, 36};
    int k2 = K2S[rndint(16)];
    long m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && m > 2) {
        for (int t = 0; t < 80; t++) {
            long c = 2 + rndint((int)(m - 2));
            if (gcd_i((int)c, (int)m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    set_group((int)m, k2, r);
}

/* ---- lift state ---- */
static int K, N;
static int perm[MAXDEG][MAXK];
static int volt[MAXDEG][MAXK];
static int nbr[MAXDEG][MAXN];
static uint64_t sA[MAXN], sB[MAXN], tmpr[MAXN], accr[MAXN];
static uint64_t vb1[MAXN * (MAXN / 64)], vb2[MAXN * (MAXN / 64)];

static int have_best = 0;
static int best_order = 0;
static int bestM = 0;
static long best_n = 0;
static int bestU[MAXN * MAXDEG], bestV[MAXN * MAXDEG];

static void set_pair(int l, int i) {
    int p = perm[l][i], s = volt[l][i];
    int si = ginv(s);
    int Abase = i * G, Bbase = (K + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][Abase + g] = Bbase + gmul(g, s);
        nbr[l][Bbase + g] = Abase + gmul(g, si);
    }
}

static void build_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_pair(l, i);
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (perm[l][i] == perm[l2][i] && volt[l][i] == volt[l2][i]) c++;
    return c;
}

/* Writes per-vertex reach masks (block-representative bits) to out; returns missing count. */
static long eval_miss(uint64_t *out) {
    uint64_t *cur = sA, *nxt = sB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long miss = 0;
    for (int v = 0; v < N; v++) {
        out[v] = cur[v];
        miss += 2 * K - __builtin_popcountll(cur[v]);
    }
    return miss;
}

/* Independent full check: simple, bipartite, degree d, diameter <= D over all pairs. */
static int verify_full(void) {
    int W = (N + 63) / 64;
    int AS = K * G;
    for (int v = 0; v < N; v++) {
        for (int l = 0; l < d; l++) {
            int u = nbr[l][v];
            if (u < 0 || u >= N || u == v) return 0;
            if ((v < AS) == (u < AS)) return 0;
            for (int l2 = 0; l2 < l; l2++)
                if (nbr[l2][v] == u) return 0;
            int sym = 0;
            for (int l2 = 0; l2 < d && !sym; l2++)
                if (nbr[l2][u] == v) sym = 1;
            if (!sym) return 0;
        }
    }
    size_t sz = (size_t)N * W;
    memset(vb1, 0, sizeof(uint64_t) * sz);
    for (int v = 0; v < N; v++) vb1[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    uint64_t *cur = vb1, *nxt = vb2;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int l = 0; l < d; l++) {
                const uint64_t *s = cur + (size_t)nbr[l][v] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        if (c != N) return 0;
    }
    return 1;
}

static void store_best(void) {
    bestM = 0;
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) {
            bestU[bestM] = v;
            bestV[bestM] = nbr[l][v];
            bestM++;
        }
    have_best = 1;
    best_order = N;
    best_n = N;
}

/* One simulated-annealing run for the current group and K. Returns 1 on a verified lift. */
static int sa_run(int iters, int patience) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) volt[l][i] = rndint(G);
    }
    build_all();
    long cost = eval_miss(tmpr) + PEN * dupcount();
    memcpy(accr, tmpr, sizeof(uint64_t) * N);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long bestc = cost;
    int last = 0;
    uint64_t FULL = (2 * K >= 64) ? ~0ULL : ((1ULL << (2 * K)) - 1);

    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > t_end) break;
        if (t - last > patience) break;
        double temp = c0 * 0.01 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rndint(100) < 25) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int a = perm[l][i1], b = perm[l][i2];
            perm[l][i1] = b;
            perm[l][i2] = a;
            set_pair(l, i1);
            set_pair(l, i2);
            long c2 = eval_miss(tmpr) + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(accr, tmpr, sizeof(uint64_t) * N);
                if (cost < bestc) {
                    bestc = cost;
                    last = t;
                }
            } else {
                perm[l][i1] = a;
                perm[l][i2] = b;
                set_pair(l, i1);
                set_pair(l, i2);
            }
        } else {
            int l = -1, i = -1, v = -1;
            if (rnd01() < 0.4) {
                for (int tr = 0; tr < 30; tr++) {
                    int x = rndint(N);
                    if (accr[x] != FULL) {
                        v = x;
                        break;
                    }
                }
            }
            if (v >= 0) {
                int a = v / G;
                l = rndint(d);
                if (a < K) {
                    i = a;
                } else {
                    int j = a - K;
                    for (int q = 0; q < K; q++)
                        if (perm[l][q] == j) {
                            i = q;
                            break;
                        }
                }
            } else {
                l = rndint(d);
                i = rndint(K);
            }
            if (i < 0) continue;
            int old = volt[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            volt[l][i] = nw;
            set_pair(l, i);
            long c2 = eval_miss(tmpr) + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(accr, tmpr, sizeof(uint64_t) * N);
                if (cost < bestc) {
                    bestc = cost;
                    last = t;
                }
            } else {
                volt[l][i] = old;
                set_pair(l, i);
            }
        }
    }
    if (cost != 0) return 0;
    build_all();
    return verify_full();
}

static void print_best(void) {
    if (!have_best) {
        printf("0 0\n");
        return;
    }
    printf("%d %d\n", best_order, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bestU[e], bestV[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [baseline_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long base = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }
    best_n = base;
    double goal = (double)base * 1.03;
    if (goal < 2.0 * d + 2) goal = 2.0 * d + 2;

    static const int KS[6] = {1, 2, 3, 4, 5, 6};
    int trials[6] = {0, 0, 0, 0, 0, 0};
    int wins[6] = {0, 0, 0, 0, 0, 0};

    while (now() < t_end) {
        int ki = 0;
        if (rnd01() < 0.2) {
            ki = rndint(6);
        } else {
            double bv = -1.0;
            for (int q = 0; q < 6; q++) {
                double v = (wins[q] + 1.0) / (trials[q] + 2.0) + 0.02 * rnd01();
                if (v > bv) {
                    bv = v;
                    ki = q;
                }
            }
        }
        int k = KS[ki];
        long target = (long)(goal / (2.0 * k)) + rndint(3);
        long cap = MAXN / (2 * k) - 40;
        if (target > cap) target = cap;
        if (target < 2) target = 2;
        sample_group(target);
        K = k;
        N = 2 * K * G;
        if (N > MAXN || N <= best_n) {
            double g = (double)best_n * 1.02;
            if (g > goal) goal = g;
            continue;
        }
        trials[ki]++;
        if (sa_run(15000, 4000)) {
            wins[ki]++;
            store_best();
            goal = N * 1.03;
        } else {
            double g1 = goal * 0.99, g2 = (double)best_n * 1.02;
            goal = g1 > g2 ? g1 : g2;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# Python bi-Cayley lift search (baseline, runs before the C engine).
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
    """Return (G, Ts, Invs) with Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
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
    """Bitmask per vertex: bit b set when block representative b is within distance D."""
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    if D == 2 or d < 2:
        return best

    # Phase 1: short Python bi-Cayley baseline (guarantees a lift even if C fails).
    lift_deadline = t0 + 0.15 * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < lift_deadline:
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C lift annealer for the remaining time, started above the current best order.
    remaining = final - time.monotonic() - 1.5
    if remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             stdin_graph=None, timeout=remaining + 15)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
