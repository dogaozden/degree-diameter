import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of small bipartite base graphs.
#
# The lift is over a semidirect product G = Z_M x|_R Z_K (element a*K+b, product
# (a,b)(c,e) = (a + R^b c, b+e)). The base graph has kk vertices per side and is
# d-regular: dart (t, i) joins A_i to B_{perm[t][i]} with voltage volt[t][i].
# The lift has 2*kk*G vertices, is bipartite and d-regular (when no duplicate
# edges exist).
#
# Left multiplication by G is an automorphism of the lift, so distances only
# need to be measured from one representative per base vertex. Cost = sum over
# the 2*kk representatives of the number of vertices at distance > D, plus a
# penalty for duplicate edges. Cost 0 means a valid graph.
#
# Moves: change one voltage, or swap two entries of one permutation.
# Output: the lift when cost 0 is reached, otherwise "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 2048
#define MAXKK 8
#define MAXD 32
#define MAXN (2 * MAXKK * MAXG)
#define STALL 3000

static int d, D, kk, G, M, K, R;
static int RP[64];
static int MT[MAXG * MAXG];
static int INV[MAXG];
static int perm[MAXD][MAXKK], volt[MAXD][MAXKK], pinv[MAXD][MAXKK];
static int sv_perm[MAXD][MAXKK], sv_volt[MAXD][MAXKK];
static int bp[MAXD][MAXKK], bv[MAXD][MAXKK];
static int stampv[MAXN];
static int curStamp = 0;
static int qbuf[MAXN];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    long long t = (long long)a + (long long)RP[b] * c;
    int aa = (int)(t % M);
    return aa * K + (b + e) % K;
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    long long t = (long long)RP[nb] * a;
    int aa = (int)((M - t % M) % M);
    return aa * K + nb;
}

/* Number of vertices at distance > D from src in the lift. */
static int ballfar(int src) {
    int nA = kk * G;
    int N = 2 * nA;
    curStamp++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    stampv[src] = curStamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            if (v < nA) {
                int i = v / G, x = v - i * G;
                for (int t = 0; t < d; t++) {
                    int j = perm[t][i];
                    int w = (kk + j) * G + MT[x * G + volt[t][i]];
                    if (stampv[w] != curStamp) {
                        stampv[w] = curStamp;
                        qbuf[tail++] = w;
                    }
                }
            } else {
                int jj = v / G - kk;
                int y = v - (kk + jj) * G;
                for (int t = 0; t < d; t++) {
                    int i = pinv[t][jj];
                    int w = i * G + MT[y * G + INV[volt[t][i]]];
                    if (stampv[w] != curStamp) {
                        stampv[w] = curStamp;
                        qbuf[tail++] = w;
                    }
                }
            }
        }
    }
    return N - tail;
}

static long long cost_eval(void) {
    long long pen = 0, sum = 0;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < kk; i++)
            pinv[t][perm[t][i]] = i;
    for (int i = 0; i < kk; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++)
                if (perm[t1][i] == perm[t2][i] && volt[t1][i] == volt[t2][i])
                    pen++;
    for (int i = 0; i < kk; i++) sum += ballfar(i * G);
    for (int j = 0; j < kk; j++) sum += ballfar((kk + j) * G);
    return sum + 1000LL * pen;
}

static void random_init(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < kk; i++) perm[t][i] = i;
        for (int i = kk - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int tmp = perm[t][i];
            perm[t][i] = perm[t][j];
            perm[t][j] = tmp;
        }
        for (int i = 0; i < kk; i++) volt[t][i] = rnd(G);
    }
}

static void mutate(void) {
    if (kk >= 2 && rnd(2) == 0) {
        int t = rnd(d), i1 = rnd(kk), i2 = rnd(kk - 1);
        if (i2 >= i1) i2++;
        int tmp = perm[t][i1];
        perm[t][i1] = perm[t][i2];
        perm[t][i2] = tmp;
    } else {
        int t = rnd(d), i = rnd(kk);
        int g = rnd(G - 1);
        if (g >= volt[t][i]) g++;
        volt[t][i] = g;
    }
}

static void save_best(void) {
    memcpy(bp, perm, sizeof perm);
    memcpy(bv, volt, sizeof volt);
}

static void restore_best(void) {
    memcpy(perm, bp, sizeof perm);
    memcpy(volt, bv, sizeof volt);
}

int main(int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    kk = atoi(argv[5]);
    G = atoi(argv[6]);
    M = atoi(argv[7]);
    K = atoi(argv[8]);
    R = atoi(argv[9]);
    if (d < 1 || d > MAXD || D < 1 || kk < 1 || kk > MAXKK || G < 2 || G > MAXG ||
        M < 2 || K < 1 || (long long)M * K != G || tl <= 0 || R < 1 || R >= M) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    RP[0] = 1 % M;
    for (int b = 1; b < K; b++) RP[b] = (int)((long long)RP[b - 1] * R % M);
    if (K >= 2 && (int)((long long)RP[K - 1] * R % M) != 1 % M) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MT[x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) INV[x] = ginv(x);

    random_init();
    long long cur = cost_eval();
    save_best();
    long long best = cur;
    long stall = 0;
    clock_t c0 = clock();

    while (cur > 0) {
        double frac = ((double)(clock() - c0) / CLOCKS_PER_SEC) / tl;
        if (frac >= 1.0) break;
        double T = 1.2 * (1.0 - frac) + 0.12;

        memcpy(sv_perm, perm, sizeof perm);
        memcpy(sv_volt, volt, sizeof volt);
        mutate();
        long long c2 = cost_eval();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            memcpy(perm, sv_perm, sizeof perm);
            memcpy(volt, sv_volt, sizeof volt);
        }

        if (cur < best) {
            best = cur;
            save_best();
            stall = 0;
        } else {
            stall++;
        }
        if (stall > STALL) {
            restore_best();
            for (int k = 0; k < 3; k++) mutate();
            cur = cost_eval();
            stall = 0;
        }
    }

    if (cur == 0) {
        int nA = kk * G;
        int m = kk * d * G;
        printf("%d %d\n", 2 * nA, m);
        for (int i = 0; i < kk; i++)
            for (int t = 0; t < d; t++)
                for (int x = 0; x < G; x++)
                    printf("%d %d\n", i * G + x,
                           (kk + perm[t][i]) * G + MT[x * G + volt[t][i]]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of W(q). Returns (n, edges, side): degree q+1, diameter 4."""
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

    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    n = P + len(lines)
    side = [0] * P + [1] * len(lines)
    return n, edges, side


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate(n, edges, side, d, rng):
    """Join deficient opposite-side vertices greedily in random order."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    left = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _pick_group(G, rng):
    """Random semidirect product Z_M x| Z_K of order G as (M, K, R), or None."""
    choices = []
    for K in range(1, 13):
        if G % K:
            continue
        M = G // K
        if M < 2:
            continue
        if K == 1:
            choices.append((M, 1, 1))
            continue
        rs = [r for r in range(1, M) if math.gcd(r, M) == 1 and pow(r, K, M) == 1]
        if rs:
            choices.append((M, K, rng.choice(rs)))
    if not choices:
        return None
    return rng.choice(choices)


def _run_lift(d, D, kk, G, grp, seed, budget):
    """Run the C lift annealer; return (n, edges) or None if it found nothing."""
    M, K, R = grp
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", kk, G, M, K, R],
                    timeout=budget + 6.0)
    n, e = lib.parse_graph_text(out)
    if n > 0 and e:
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(res):
        nonlocal best, best_n
        if res is None:
            return
        n, e = res
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured starts: projective plane (D = 3) or generalized quadrangle (D >= 4).
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(lib.projective_plane_incidence(q))
                break
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            n, e, side = gq
            consider((n, e))
            consider((n, _saturate(n, e, side, d, rng)))

    # Main phase: voltage-lift annealing in C over several base sizes.
    # Target order for each base size is a bit below the Moore bound.
    # A success raises the target order by one group element; repeated failures
    # lower it again.
    moore = lib.moore_bound(d, D)
    kks = [1, 1, 2, 2, 3, 4]
    cap = {}
    for kk in (1, 2, 3, 4):
        cap[kk] = max(best_n // (2 * kk) + 1, int(0.78 * moore / (2 * kk)))
    fails = {kk: 0 for kk in cap}
    attempt = 0
    end = start + 0.92 * tl - 1.0

    while True:
        remaining = end - time.monotonic()
        if remaining < 2.5:
            break
        kk = rng.choice(kks)
        G = max(cap[kk], best_n // (2 * kk) + 1, 2)
        grp = _pick_group(G, rng)
        if grp is None:
            cap[kk] = G + 1
            continue
        budget = min(remaining - 0.5, max(3.0, 0.4 * remaining))
        attempt += 1
        try:
            res = _run_lift(d, D, kk, G, grp, seed * 7919 + attempt, budget)
        except Exception:
            res = None
        if res is not None:
            consider(res)
            cap[kk] = G + 1
            fails[kk] = 0
        else:
            fails[kk] += 1
            if fails[kk] >= 2:
                fails[kk] = 0
                cap[kk] = max(best_n // (2 * kk) + 1, G - max(1, G // 120))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
