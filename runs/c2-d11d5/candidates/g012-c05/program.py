"""Bi-Cayley lift search with a full-C annealing engine.

Replaces the parent's Python lift search and grow-by-two engine. For each sampled group
G = Z_m x| Z_k2 and block count k, C anneals d perfect matchings between k A-blocks and k
B-blocks, with voltages in G, so every vertex has degree d. Left multiplication by G is an
automorphism, so checking distances from each vertex to the k+k block representatives is
enough for the full diameter. Each candidate is checked with lib.is_valid, and the best
valid graph (K_{d,d} or a known construction) is always the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley voltage-lift annealer.
 * Usage: prog d D seed time_limit k m k2 r
 * Group: G = Z_m x| Z_k2, element (a,b) coded as a*k2+b,
 *        (a,b)(c,e) = (a + r^b c, b + e), needs r^k2 = 1 mod m and gcd(r,m) = 1.
 * Graph: A blocks i<k, B blocks j<k, vertex A(i,g) = i*G+g, B(j,h) = (k+j)*G+h.
 * Layer l is a perfect matching P[l] (A block i -> B block P[l][i]) with voltage Sv[l][i]:
 *   A(i,g) ~ B(P[l][i], g*s).
 * Prints "n m" and the edges of the first valid lift found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 8
#define MAXL 32
#define MAXG 8192
#define MAXN (2 * MAXK * MAXG)
#define MAXPW 64
#define PENALTY 50

static int d, D, k, m, k2, G, N;
static int powr[MAXPW];
static int P[MAXL][MAXK];
static int Sv[MAXL][MAXK];
static int nbr[MAXN][MAXL];
static uint32_t bufa[MAXN], bufb[MAXN];
static uint64_t rs = 88172645463325252ULL;

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

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (long long)a + (long long)powr[b] * c;
    int aa = (int)(t % m);
    int bb = (b + e) % k2;
    return aa * k2 + bb;
}

/* Full evaluation: rebuild neighbours, propagate block-representative reach for D rounds.
 * cost = unreached (vertex, representative) pairs + PENALTY * duplicate darts. */
static void evaluate(long *cost) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int p = P[l][i], s = Sv[l][i];
            int A0 = i * G, B0 = (k + p) * G;
            for (int g = 0; g < G; g++) {
                int A = A0 + g;
                int B = B0 + gmul(g, s);
                nbr[A][l] = B;
                nbr[B][l] = A;
            }
        }
    }
    int bits = 2 * k;
    uint32_t full = (1u << bits) - 1u;
    uint32_t *cur = bufa, *nxt = bufb;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < bits; b++) cur[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[v][l]];
            nxt[v] = x;
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += bits - __builtin_popcount(cur[v] & full);
    long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (P[l1][i] == P[l2][i] && Sv[l1][i] == Sv[l2][i]) dup++;
    *cost = unr + PENALTY * dup;
}

static void print_graph(void) {
    long mc = (long)k * G * d;
    printf("%d %ld\n", N, mc);
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[v][l]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d < 2 || d > MAXL || D < 2 || k < 1 || k > MAXK || m < 2 || k2 < 1 || k2 > MAXPW) {
        printf("0 0\n");
        return 0;
    }
    if (r < 0 || r >= m || gcd_int(r, m) != 1) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    if (G > MAXG) {
        printf("0 0\n");
        return 0;
    }
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    if ((long long)powr[k2 - 1] * r % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * k * G;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) P[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < k; i++) Sv[l][i] = rndint(G);
    }

    double deadline = t0 + limit - 0.3;
    long cost;
    evaluate(&cost);
    double start = now();
    double span = deadline - start;
    if (span < 0.1) span = 0.1;
    long it = 0;

    while (cost > 0) {
        if ((it & 7) == 0 && now() > deadline) break;
        it++;
        double frac = (now() - start) / span;
        if (frac > 1.0) frac = 1.0;
        double T = 2.0 * (1.0 - frac) + 0.1;
        long nc;
        if (k >= 2 && rnd01() < 0.3) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int t = P[l][i1];
            P[l][i1] = P[l][i2];
            P[l][i2] = t;
            evaluate(&nc);
            double dl = (double)(nc - cost);
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                cost = nc;
            } else {
                t = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = t;
            }
        } else {
            int l = rndint(d);
            int i = rndint(k);
            int old = Sv[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            Sv[l][i] = nv;
            evaluate(&nc);
            double dl = (double)(nc - cost);
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                cost = nc;
            } else {
                Sv[l][i] = old;
            }
        }
    }

    evaluate(&cost);
    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }
    print_graph();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (unchanged from the parent).
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
# Group sampling for Z_m x| Z_k2.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6)
_GMAX = 8192


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

    # Exact constructions (calibration cases return immediately).
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

    # Main phase: bi-Cayley lift annealing in C, one sampled group per call.
    # The order goal ratchets up on success and eases down on failure.
    if d >= 3 and D >= 3 and d <= 32 and time.monotonic() < final - 2.0:
        moore = lib.moore_bound(d, D)
        goal = max(best_n * 1.05, 0.25 * moore)
        trials = {kk: 0 for kk in _KS}
        wins = {kk: 0 for kk in _KS}
        while True:
            budget = min(6.0, final - time.monotonic() - 0.5)
            if budget < 1.0:
                break
            if rng.random() < 0.2:
                k = rng.choice(_KS)
            else:
                k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())
            target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
            g = _sample_group(target, rng)
            if g is None:
                goal = max(best_n * 1.02, goal * 0.97)
                continue
            m, k2, r = g
            G = m * k2
            if G > _GMAX or 2 * k * G <= best_n:
                goal = max(best_n * 1.02, goal * 0.97)
                continue
            trials[k] += 1
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, rng.randrange(1 << 30), round(budget, 2), k, m, k2, r],
                                 timeout=budget + 10)
                n_new, e_new = lib.parse_graph_text(text)
            except Exception:
                n_new, e_new = 0, []
            if n_new > 0:
                wins[k] += 1
                consider(n_new, e_new)
                goal = max(goal, n_new * 1.04)
            else:
                goal = max(best_n * 1.02, goal * 0.97)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
