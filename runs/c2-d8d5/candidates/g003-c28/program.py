"""Bi-Cayley lift search over Z_m x| Z_k2 with a C annealing engine.

New in this version: the whole annealing loop (voltage moves, layer swaps, defect-
targeted proposals, restarts) runs in a C engine. The diameter oracle is an
orbit-representative bitmask: a vertex stores which of the 2k block
representatives lie within distance D. Left-multiplication automorphisms make
these representatives sufficient, so one bit-parallel sweep costs O(D * N * d).
Python handles constructions, group sampling, a bandit over base sizes k, and
validation.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXV 32768
#define MAXK2 64
#define PEN 1000LL
#define ITERS 400000LL
#define PATIENCE 25000LL

static int d, D, k, k2, m, rr, G, N;
static int pw[MAXK2];
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD][MAXV];
static uint32_t bufA[MAXV], bufB[MAXV], tmpb[MAXV];
static uint64_t rs = 88172645463325252ULL;

static uint64_t nxt(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(nxt() % (uint64_t)n); }
static double rfloat(void) { return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* element a*k2+b  ~  (a,b); (a,b)(c,e) = (a + r^b c, b+e) */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2;
    int c = y / k2, e = y % k2;
    int aa = (int)((a + (long long)pw[b] * c) % m);
    int bb = (b + e) % k2;
    return aa * k2 + bb;
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static int ginv(int x) {
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = (long long)pw[nb] * a % m;
    int na = (int)((m - t) % m);
    return na * k2 + nb;
}

/* A_{i,g} ~ B_{p,g s}, with p = layers[l][i], s = S[l][i] */
static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    int si = ginv(s);
    int ba = i * G, bb = (k + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ba + g] = bb + gmul(g, s);
        nbr[l][bb + g] = ba + gmul(g, si);
    }
}

static int popc(uint32_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

/* duplicate edges appear only for equal (i, p, s) across layers */
static long long dupcount(void) {
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) dup++;
    return dup;
}

/* out[v] bit b set iff block representative b is within distance D of v */
static long long evalcost(uint32_t *out) {
    int K2 = 2 * k;
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < K2; b++) out[b * G] |= 1u << b;
    uint32_t *cur = out, *nx = tmpb;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nx[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *sw = cur; cur = nx; nx = sw;
        if (!changed) break;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint32_t) * (size_t)N);
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += K2 - popc(out[v]);
    return unr + PEN * dupcount();
}

static void print_graph(void) {
    printf("%d %d\n", N, k * G * d);
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[l][u]);
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = layers[l][i]; layers[l][i] = layers[l][j]; layers[l][j] = t;
        }
        for (int i = 0; i < k; i++) S[l][i] = rint_(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D seed time k k2 m r\n");
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    k = atoi(argv[5]);
    k2 = atoi(argv[6]);
    m = atoi(argv[7]);
    rr = atoi(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK ||
        k2 < 1 || k2 > MAXK2 || m < 1) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    N = 2 * k * G;
    if (N > MAXV) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * rr % m);

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) nxt();

    double end = now_sec() + tl;
    while (now_sec() < end) {
        random_state();
        uint32_t *cur = bufA;
        long long c = evalcost(cur);
        long long c0 = c > 0 ? c : 1;
        long long best = c, last = 0;

        for (long long it = 0; it < ITERS && c != 0; it++) {
            if (it - last > PATIENCE) break;
            if ((it & 127) == 0 && now_sec() >= end) break;
            double temp = 0.01 * (double)c0 * (1.0 - (double)it / (double)ITERS);
            if (temp < 0.5) temp = 0.5;
            uint32_t *nw = (cur == bufA) ? bufB : bufA;

            if (k >= 2 && rfloat() < 0.25) {
                /* layer swap: exchange B-targets of two A-blocks in one layer */
                int l = rint_(d);
                int i1 = rint_(k), i2 = rint_(k - 1);
                if (i2 >= i1) i2++;
                int t = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = t;
                set_dart(l, i1); set_dart(l, i2);
                long long c2 = evalcost(nw);
                if (c2 <= c || rfloat() < exp(-(double)(c2 - c) / temp)) {
                    cur = nw; c = c2;
                    if (c < best) { best = c; last = it; }
                } else {
                    t = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = t;
                    set_dart(l, i1); set_dart(l, i2);
                }
                continue;
            }

            /* voltage move: defect-targeted with probability 0.4 */
            int l = -1, i = -1;
            if (rfloat() < 0.4) {
                uint32_t full = (1u << (2 * k)) - 1u;
                int v = -1;
                for (int tr = 0; tr < 64; tr++) {
                    int u = rint_(N);
                    if (cur[u] != full) { v = u; break; }
                }
                if (v >= 0) {
                    int blk = v / G;
                    l = rint_(d);
                    if (blk < k) {
                        i = blk;
                    } else {
                        int p = blk - k;
                        for (int j = 0; j < k; j++)
                            if (layers[l][j] == p) { i = j; break; }
                    }
                }
            }
            if (i < 0) { l = rint_(d); i = rint_(k); }

            int old = S[l][i];
            int nsv = rint_(G);
            if (nsv == old) continue;
            S[l][i] = nsv;
            set_dart(l, i);
            long long c2 = evalcost(nw);
            if (c2 <= c || rfloat() < exp(-(double)(c2 - c) / temp)) {
                cur = nw; c = c2;
                if (c < best) { best = c; last = it; }
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }

        if (c == 0) {
            print_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions for calibration cases.
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
# Group sampling and the C-backed lift search.
# ----------------------------------------------------------------------------

_MAXD = 32
_MAXV = 32768
_KS = (1, 2, 3, 4, 5, 6)
_SUB = 6.0  # seconds per C call for one group


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


def _c_lift(d, D, k, m, k2, r, seed, sub):
    """Run the C annealer on one group. Returns (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{sub:.2f}", k, k2, m, r], timeout=sub + 3.0)
    n, edges = lib.parse_graph_text(out)
    if n <= 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
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

    # Exact constructions for calibration-style cases.
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

    if d > _MAXD:
        return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    failures = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.5:
            break
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n or 2 * k * G > _MAXV:
            continue

        sub = min(_SUB, remaining - 1.0)
        trials[k] += 1
        try:
            res = _c_lift(d, D, k, m, k2, r, rng.randrange(1 << 30), sub)
        except (RuntimeError, ValueError):
            failures += 1
            if failures >= 3:
                break
            continue
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
