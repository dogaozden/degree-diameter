"""Bi-Cayley voltage-lift search with a C annealer over semidirect products Z_m x| Z_k2.

New helper in this version: the lift annealer runs in C. Each layer is a block permutation
plus one voltage per base vertex. By left-regularity, the all-pairs distance check reduces to
one reach bitmask per vertex, which is cheap to recompute. Moves are targeted at unreached
pairs, and duplicate darts carry a large penalty. Small exact constructions are used when they apply.

Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage: prog d D seed time_limit K M K2 RG
 * Group: Z_M x|_RG Z_K2, element (a,b) coded as a*K2+b, (a,b)(c,e) = (a+RG^b c, b+e).
 * Base: K A-blocks and K B-blocks, d layers. Layer l pairs A_i with B_{lp[l][i]} via voltage vo[l][i]:
 *   A_{i,g} ~ B_{p, g*s}.  Each layer is a permutation, so every vertex has degree d.
 * Left multiplication by the group is an automorphism, so the all-pairs check reduces to
 * "every vertex reaches every block representative within D".
 * Output: "n m" + edges of a valid lift, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXL 32
#define MAXK 16
#define MAXNV 40000
#define MAXK2 4096
#define PEN 1000000L

static int d, D, K, G, M, K2, RG, NV;
static uint32_t FULL;
static int32_t nb[MAXL][MAXNV];
static int lp[MAXL][MAXK];
static int vo[MAXL][MAXK];
static long rpow[MAXK2];
static uint32_t R1[MAXNV], R2[MAXNV], RA[MAXNV], RB[MAXNV];
static uint32_t *cur, *tryr;
static uint64_t rs = 88172645463325252ULL;

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
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc(uint32_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    long t = ((long)a + rpow[b] * (long)c) % M;
    int lo = b + e;
    if (lo >= K2) lo -= K2;
    return (int)t * K2 + lo;
}

static void set_dart(int l, int i) {
    int p = lp[l][i], s = vo[l][i];
    int ai = i * G, bp = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        nb[l][ai + g] = bp + h;
        nb[l][bp + h] = ai + g;
    }
}

/* out[v] = bitmask of block representatives within distance D of v. */
static void compute_reach(uint32_t *out) {
    uint32_t *a = R1, *b = R2;
    memset(a, 0, sizeof(uint32_t) * (size_t)NV);
    for (int c = 0; c < 2 * K; c++) a[c * G] = 1u << c;
    for (int r = 0; r < D; r++) {
        memcpy(b, a, sizeof(uint32_t) * (size_t)NV);
        for (int l = 0; l < d; l++) {
            const int32_t *q = nb[l];
            for (int v = 0; v < NV; v++) b[v] |= a[q[v]];
        }
        uint32_t *t = a; a = b; b = t;
    }
    memcpy(out, a, sizeof(uint32_t) * (size_t)NV);
}

static long cost_of(const uint32_t *res) {
    long u = 0;
    for (int v = 0; v < NV; v++) u += 2 * K - pc(res[v]);
    return u;
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = 0; l2 < l1; l2++)
                if (lp[l1][i] == lp[l2][i] && vo[l1][i] == vo[l2][i]) c++;
    return c;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lp[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lp[l][i]; lp[l][i] = lp[l][j]; lp[l][j] = t;
        }
        for (int i = 0; i < K; i++) vo[l][i] = rndint(G);
        for (int i = 0; i < K; i++) set_dart(l, i);
    }
}

/* One annealing run from a random start. Returns 1 with nb/cur valid, or 0. */
static int anneal(double window, double until) {
    random_init();
    compute_reach(cur);
    long cost = cost_of(cur) + PEN * dupcount();
    double start = now(), T = 3.0, T0 = 3.0, T1 = 0.25;
    for (long t = 0;; t++) {
        if (cost == 0) return 1;
        if ((t & 31) == 0) {
            double nw = now();
            if (nw > until || nw - start > window) return 0;
            T = T0 * pow(T1 / T0, (nw - start) / window);
        }
        if (K >= 2 && rnd64() % 100 < 20) {
            /* swap two block targets inside one layer */
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lp[l][i1]; lp[l][i1] = lp[l][i2]; lp[l][i2] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            compute_reach(tryr);
            long nc = cost_of(tryr) + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                uint32_t *s = cur; cur = tryr; tryr = s;
            } else {
                tmp = lp[l][i1]; lp[l][i1] = lp[l][i2]; lp[l][i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }
        /* voltage change; with prob 0.6 aim at a vertex that is not yet fully reached */
        int l = -1, i = -1;
        if (rnd01() < 0.6) {
            int v = rndint(NV);
            for (int tries = 0; tries < 40 && cur[v] == FULL; tries++) v = rndint(NV);
            if (cur[v] != FULL) {
                int c = v / G;
                l = rndint(d);
                if (c < K) {
                    i = c;
                } else {
                    for (int ii = 0; ii < K; ii++)
                        if (lp[l][ii] == c - K) { i = ii; break; }
                }
            }
        }
        if (i < 0) { l = rndint(d); i = rndint(K); }
        int old = vo[l][i];
        int ns = rndint(G);
        if (ns == old) continue;
        vo[l][i] = ns;
        set_dart(l, i);
        compute_reach(tryr);
        long nc = cost_of(tryr) + PEN * dupcount();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            uint32_t *s = cur; cur = tryr; tryr = s;
        } else {
            vo[l][i] = old;
            set_dart(l, i);
        }
    }
    return 0;
}

static void print_graph(void) {
    int A = K * G;
    printf("%d %d\n", NV, A * d);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++) printf("%d %d\n", u, (int)nb[l][u]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    RG = atoi(argv[8]);
    double t0 = now();
    double until = t0 + limit * 0.9 - 0.1;
    if (d < 1 || d > MAXL || D < 1 || K < 1 || K > MAXK - 1 || M < 1 || K2 < 1 || K2 > MAXK2) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    NV = 2 * K * G;
    if (NV > MAXNV) { printf("0 0\n"); return 0; }
    FULL = (1u << (2 * K)) - 1;
    RG %= M;
    if (M > 1 && gcdl(RG, M) != 1) { printf("0 0\n"); return 0; }
    rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) rpow[b] = (rpow[b - 1] * RG) % M;
    if (((rpow[K2 - 1] * RG) % M) != (1 % M)) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    cur = RA;
    tryr = RB;
    while (1) {
        double left = until - now();
        if (left < 0.05) break;
        double window = left < 3.0 ? left : 3.0;
        if (anneal(window, until)) {
            print_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


_KS = (1, 2, 3, 4, 5, 6)
_SLICE = 6.0      # seconds per lift attempt
_MAX_N = 12000    # keep 2*K*G within the C engine's capacity


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
# Group sampling and the C lift runner.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with m*k2 >= target, or None."""
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


def _run_lift(d, D, seed, budget, k, m, k2, r):
    """Run the C lift annealer once. Returns (n, edges) or None."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), k, m, k2, r],
                         stdin_graph=None, timeout=budget + 20)
        n, edges = lib.parse_graph_text(text)
    except Exception:
        return None
    if n <= 0 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2 or d == 1:
        # K_{d,d} is extremal for diameter 2.
        return lib.haar_graph(d, range(d))

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

    # Exact constructions (calibration-style cases return immediately).
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

    # Lift search: ratcheted order goal, bandit over block counts K.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = final - time.monotonic()
        if remaining < 1.5:
            break
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(best_n * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        n_try = 2 * k * m * k2
        if n_try <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        if n_try > _MAX_N:
            goal = max(best_n * 1.02, goal * 0.97)
            continue
        budget = min(remaining - 1.0, _SLICE)
        trials[k] += 1
        res = _run_lift(d, D, rng.randrange(1 << 30), budget, k, m, k2, r)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            goal = max(goal, res[0] * 1.08)
        else:
            goal = max(best_n * 1.02, goal * 0.97)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
