import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of a semidirect product
# Z_M x| Z_K2 (order G = M*K2) with K base vertices per side and degree d.
#
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (K+j)*G + h.
# Layer l gives a permutation pm[l][*] of the base and voltages vol[l][i];
# dart (l,i) joins A_{i,g} to B_{pm[l][i], g*s} for every g, s = vol[l][i].
# Left multiplication is an automorphism, so distances from the 2K
# representatives A_{i,e} and B_{j,e} to everything decide diameter <= D.
# Cost = unreached (representative, vertex) pairs + large penalty per
# duplicate dart (same i, same j, same voltage). Cost 0 gives a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 2000
#define MAXK 8
#define MAXD 16
#define MAXN (2 * MAXK * MAXG)
#define BIGP 1000000L

static int d, D, K, M, K2, R, G, N;
static int *mt;
static int pw[MAXG + 1];
static int vol[MAXD][MAXK], pm[MAXD][MAXK];
static int bvol[MAXD][MAXK], bpm[MAXD][MAXK];
static int nb[MAXN * MAXD];
static int fillc[MAXN];
static int stampa[MAXN];
static int qu[MAXN];
static int stampv = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) {
    return (int)(rnext() % (uint64_t)n);
}

static double rdbl(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int semimul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M) * K2 + (b + e) % K2;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) pm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = pm[l][i];
            pm[l][i] = pm[l][j];
            pm[l][j] = t;
        }
        for (int i = 0; i < K; i++) vol[l][i] = rint_(G);
    }
}

static long evaluate(void) {
    long dups = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (pm[l][i] == pm[l2][i] && vol[l][i] == vol[l2][i]) dups++;

    memset(fillc, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) {
            int j = pm[l][i], s = vol[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + mt[g * G + s];
                nb[a * d + fillc[a]++] = b;
                nb[b * d + fillc[b]++] = a;
            }
        }
    }

    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stampv++;
        int head = 0, tail = 0;
        qu[tail++] = src;
        stampa[src] = stampv;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                const int *nu = nb + u * d;
                for (int t = 0; t < d; t++) {
                    int v = nu[t];
                    if (stampa[v] != stampv) {
                        stampa[v] = stampv;
                        qu[tail++] = v;
                    }
                }
            }
        }
        unreached += (long)(N - tail);
    }
    return unreached + dups * BIGP;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    if (d < 1 || d > MAXD || D < 1 || K < 1 || K > MAXK || M < 1 || K2 < 1) {
        printf("0 0\n");
        return 0;
    }
    if ((long)M * K2 < 2 || (long)M * K2 > MAXG) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2 * K * G;

    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)(((long)pw[b - 1] * R) % M);
    mt = (int *)malloc(sizeof(int) * (size_t)G * (size_t)G);
    if (!mt) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[x * G + y] = semimul(x, y);

    random_state();
    double t0 = now();
    long cur = evaluate();
    long bestc = cur;
    memcpy(bvol, vol, sizeof(vol));
    memcpy(bpm, pm, sizeof(pm));

    double T0 = 3.0, T1 = 0.1;
    long iter = 0;
    double f = 0.0;
    while (bestc > 0) {
        if ((iter & 63) == 0) {
            double el = now() - t0;
            if (el >= tl) break;
            f = el / tl;
        }
        iter++;
        double T = T0 * pow(T1 / T0, f);
        int l = rint_(d), i = rint_(K);
        int kind = (K > 1 && rint_(4) == 0) ? 1 : 0;
        int oldv = 0, i2 = 0;
        if (kind == 0) {
            oldv = vol[l][i];
            vol[l][i] = rint_(G);
            if (vol[l][i] == oldv) continue;
        } else {
            i2 = rint_(K);
            if (i2 == i) continue;
            int t = pm[l][i];
            pm[l][i] = pm[l][i2];
            pm[l][i2] = t;
        }
        long c2 = evaluate();
        if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bvol, vol, sizeof(vol));
                memcpy(bpm, pm, sizeof(pm));
            }
        } else {
            if (kind == 0) {
                vol[l][i] = oldv;
            } else {
                int t = pm[l][i];
                pm[l][i] = pm[l][i2];
                pm[l][i2] = t;
            }
        }
    }

    if (bestc == 0) {
        memcpy(vol, bvol, sizeof(vol));
        memcpy(pm, bpm, sizeof(pm));
        evaluate();
        int m = K * G * d;
        printf("%d %d\n", N, m);
        for (int a = 0; a < K * G; a++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", a, nb[a * d + t]);
    } else {
        printf("0 0\n");
    }
    free(mt);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (valid fallbacks).
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
# Group choice for the C engine.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (M, K2, R) with M*K2 = G giving a semidirect product Z_M x| Z_K2, or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if k2 == 1:
            return (m, 1, 1)
        if m < 2:
            continue
        cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return (m, k2, rng.choice(cands))
    return None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    deadline = t_start + 0.78 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    bound = lib.moore_bound(d, D)
    if d < 3 or D < 3 or best_n >= bound:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Main search: C annealing over semidirect voltage lifts, with several
    # base sizes K and target group orders just above the current best / (2K).
    calls = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0 or best_n >= bound:
            break
        K = rng.choice([1, 1, 2, 2, 3, 4])
        base = best_n // (2 * K)
        G = max(2, base + 1 + rng.randrange(0, 2 + base // 25))
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        M, K2, R = grp
        budget = min(rng.uniform(4.0, 10.0), remaining - 2.0)
        if budget < 1.0:
            break
        calls += 1
        call_seed = rng.randrange(1, 2**31 - 1)
        try:
            out = lib.run_c(C_SOURCE, [d, D, call_seed, budget, K, M, K2, R],
                            timeout=budget + 3.0)
            n, e = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            continue
        if n > 0:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
