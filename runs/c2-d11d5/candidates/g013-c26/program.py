"""Combined program: a C simulated-annealing search over bi-Cayley voltage lifts on
semidirect products Z_m x| Z_k2 (block-representative reach bitmasks), with exact
constructions first and a pure-Python lift search as a fallback if the C engine fails.

Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define KMAX 6
#define MAXN 24000
#define PEN 1000.0
#define ITERS 6000L
#define PATIENCE 1500L

static int d, D;
static int K, G, N, M, K2, R;
static long pw[64];
static int nbr[MAXD][MAXN];
static int perm[MAXD][MAXK];
static long Sv[MAXD][MAXK];
static uint32_t bufA[MAXN], bufB[MAXN], bufT[MAXN];
static uint32_t *curR, *newR;
static int best_nbr[MAXD][MAXN];
static int have_best = 0, best_K = 0, best_G = 0, best_N = 0;
static double deadline;
static uint64_t rs = 88172645463325252ULL;
static long wins[KMAX + 1], trials[KMAX + 1];
static const long KCH[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static int popc(uint32_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    unsigned long long r = (unsigned long long)(1 % m);
    unsigned long long x = (unsigned long long)(b % m);
    while (e > 0) {
        if (e & 1) r = r * x % (unsigned long long)m;
        x = x * x % (unsigned long long)m;
        e >>= 1;
    }
    return (long)r;
}

/* Semidirect product Z_M x| Z_K2, element (a,b) coded as a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long na = ((long)a + pw[b] * (long)c) % M;
    int nb = (b + e) % K2;
    return (int)na * K2 + nb;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long na = (M - ((pw[nb] * (long)a) % M)) % M;
    return (int)na * K2 + nb;
}

static void setup_group(int k, long mm, long k2, long rr) {
    K = k;
    M = (int)mm;
    K2 = (int)k2;
    R = (int)rr;
    G = M * K2;
    N = 2 * K * G;
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (pw[b - 1] * R) % M;
}

static int sample_group(long target, long *mo, long *k2o, long *ro) {
    int nch = (int)(sizeof(KCH) / sizeof(KCH[0]));
    for (int att = 0; att < 200; att++) {
        long k2 = KCH[rndint(nch)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (gcdl(r, m) != 1 || powmod(r, 2, m) != 1 % m) continue;
        } else {
            r = -1;
            for (int t = 0; t < 60; t++) {
                long c = 1 + rndint((int)(m - 1));
                if (gcdl(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        *mo = m;
        *k2o = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

/* Layer l sends A-block i to B-block perm[l][i] with voltage Sv[l][i]:
   A_{i,x} ~ B_{j, x*s}. Writes both directions of that matching. */
static void set_dart(int l, int i) {
    int j = perm[l][i];
    int s = (int)Sv[l][i];
    int si = ginv(s);
    int ab = i * G, bb = (K + j) * G;
    for (int x = 0; x < G; x++) {
        nbr[l][ab + x] = bb + gmul(x, s);
        nbr[l][bb + x] = ab + gmul(x, si);
    }
}

static int dup_count(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 1; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (perm[l][i] == perm[l2][i] && Sv[l][i] == Sv[l2][i]) dup++;
    return dup;
}

/* Reach bitmask per vertex over the 2K block representatives (vertices b*G, identity).
   Left multiplication is an automorphism acting regularly on each block, so the
   diameter condition is exactly: every vertex reaches every representative within D.
   Returns the number of unreached (vertex, representative) pairs. */
static long compute_reach(uint32_t *out) {
    uint32_t *cur = out, *nxt = bufT;
    int NB = 2 * K;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < NB; b++) cur[b * G] |= (uint32_t)1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint32_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint32_t) * (size_t)N);
    long un = 0;
    for (int v = 0; v < N; v++) un += NB - popc(out[v]);
    return un;
}

static int search(long iters, long patience) {
    int NB = 2 * K;
    uint32_t full = (uint32_t)((1u << NB) - 1u);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            Sv[l][i] = rndint(G);
            set_dart(l, i);
        }
    }
    curR = bufA;
    newR = bufB;
    double cost = (double)compute_reach(curR) + PEN * dup_count();
    double c0 = cost > 1.0 ? cost : 1.0;
    double best = cost;
    long last = 0;
    for (long t = 0; t < iters && cost > 0.0; t++) {
        if (now() > deadline || t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            double c2 = (double)compute_reach(newR) + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp((cost - c2) / temp)) {
                uint32_t *sw = curR;
                curR = newR;
                newR = sw;
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tr = 0; tr < 30 && v < 0; tr++) {
                int cand = rndint(N);
                if (curR[cand] != full) v = cand;
            }
            if (v >= 0) {
                int block = v / G;
                l = rndint(d);
                if (block < K) {
                    i = block;
                } else {
                    int j = block - K;
                    for (int ii = 0; ii < K; ii++)
                        if (perm[l][ii] == j) { i = ii; break; }
                }
            }
        }
        if (l < 0) { l = rndint(d); i = -1; }
        if (i < 0) i = rndint(K);

        long old = Sv[l][i];
        long nw = rndint(G);
        if (nw == old) continue;
        Sv[l][i] = nw;
        set_dart(l, i);
        double c2 = (double)compute_reach(newR) + PEN * dup_count();
        if (c2 <= cost || rnd01() < exp((cost - c2) / temp)) {
            uint32_t *sw = curR;
            curR = newR;
            newR = sw;
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            Sv[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0.0;
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(KMAX);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= KMAX; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    deadline = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int bestN = min_n;
    double goal = bestN * 1.05;
    if (goal < 4.0) goal = 4.0;

    while (now() < deadline) {
        if (goal > MAXN) goal = MAXN;
        int k = pick_k();
        long target = (long)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        long m = 0, k2 = 0, r = 0;
        if (!sample_group(target, &m, &k2, &r)) {
            goal = fmax(bestN * 1.02, goal * 0.99);
            continue;
        }
        long Gs = m * k2;
        if (2L * k * Gs > MAXN) {
            goal = fmax(bestN * 1.02, goal * 0.99);
            continue;
        }
        if (2L * k * Gs <= bestN) {
            goal = fmax(goal, bestN * 1.02);
            continue;
        }
        setup_group(k, m, k2, r);
        trials[k]++;
        if (search(ITERS, PATIENCE)) {
            wins[k]++;
            bestN = N;
            have_best = 1;
            best_K = K;
            best_G = G;
            best_N = N;
            for (int l = 0; l < d; l++)
                memcpy(best_nbr[l], nbr[l], sizeof(int) * (size_t)N);
            goal = fmax(goal, N * 1.04);
        } else {
            goal = fmax(bestN * 1.02, goal * 0.99);
        }
    }

    if (have_best) {
        int A = best_K * best_G;
        printf("%d %ld\n", best_N, (long)A * d);
        for (int u = 0; u < A; u++)
            for (int l = 0; l < d; l++)
                printf("%d %d\n", u, best_nbr[l][u]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


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


# ----------------------------------------------------------------------------
# Python fallback: bi-Cayley lift search (used only if the C engine fails).
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6)
_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_PY_MAX_G = 2500


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
                c = rng.randrange(1, m)
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


def _search_py(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
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
    cost = int(_2k_minus(k, N, reach)) + _PENALTY * dupcount()
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
            c2 = int(_2k_minus(k, N, r2)) + _PENALTY * dupcount()
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
        c2 = int(_2k_minus(k, N, r2)) + _PENALTY * dupcount()
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


def _2k_minus(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _py_lift(d, D, rng, start_n, deadline):
    """Pure-Python lift search with a bandit over base sizes. Returns (n, edges) or None."""
    best = None
    best_n = start_n
    goal = float(start_n) * 1.05
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    while time.monotonic() < deadline:
        if rng.random() < 0.2:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        if m * k2 > _PY_MAX_G:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        trials[k] += 1
        res = _search_py(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            best, best_n = res, res[0]
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)
    return best


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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
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

    # Main phase: C lift search over semidirect-product voltage lifts.
    if d >= 2 and D >= 2 and final - time.monotonic() > 4.0:
        budget = final - time.monotonic() - 2.0
        c_ok = True
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                             timeout=budget + 3.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            c_ok = False
        if not c_ok and time.monotonic() < final - 2.0:
            try:
                res = _py_lift(d, D, rng, best_n, final - 1.0)
                if res is not None:
                    consider(*res)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
