"""Bold variant: C simulated annealing over bi-Cayley voltage lifts (semidirect groups Z_m x| Z_k2).

Instead of a Python/numpy search, the C engine anneals the layer permutations and voltages directly.
It checks diameter with block-representative bitsets, using left-translation symmetry. Python grows
the target size geometrically, and every result is checked with lib.is_valid. K_{d,d} (or an exact
construction) is always kept as the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage: prog d D seed time_limit M K2 R K
 * Group: Z_M x|_R Z_K2, element (a,b) coded as a*K2+b, with R^K2 = 1 mod M.
 * Base: K "A" blocks and K "B" blocks. Layer l maps A-block i to B-block lay[l][i] with voltage vol[l][i]:
 *   A_{i,g} ~ B_{j, g*s}.  Each layer is a perfect matching, so the graph is d-regular.
 * Output: "N m" and edges of a valid graph (diameter <= D), or "0 0" if none was found in time.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int d, D, K, M, K2, R, G, N;
static int powr[64];
static int *sinv;
static int *nbr;
static int *lay;
static int *vol;
static uint64_t *ra, *rb;
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

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return ((a + powr[b] * c) % M) * K2 + (b + e) % K2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int na = (M - (powr[nb] * a) % M) % M;
    return na * K2 + nb;
}

static void rebuild_layer(int l) {
    int pinv[64];
    const int *L = lay + (size_t)l * K;
    const int *S = vol + (size_t)l * K;
    int *nb = nbr + (size_t)l * N;
    for (int i = 0; i < K; i++) pinv[L[i]] = i;
    for (int i = 0; i < K; i++) {
        int s = S[i], j = L[i];
        for (int g = 0; g < G; g++) nb[i * G + g] = (K + j) * G + gmul(g, s);
    }
    for (int j = 0; j < K; j++) {
        int i = pinv[j];
        int si = sinv[S[i]];
        for (int h = 0; h < G; h++) nb[(K + j) * G + h] = i * G + gmul(h, si);
    }
}

/* Duplicate darts: same A-block, same B-block and same voltage in two layers. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1 * K + i] == lay[l2 * K + i] && vol[l1 * K + i] == vol[l2 * K + i]) c++;
    return c;
}

/* Number of (representative block, vertex) pairs at distance > D. */
static long unreached(void) {
    uint64_t *cur = ra, *nxt = rb;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * G] |= 1ULL << b;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long c = 0;
    for (int v = 0; v < N; v++) c += 2 * K - __builtin_popcountll(cur[v]);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D seed time_limit M K2 R K\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    M = atoi(argv[5]);
    K2 = atoi(argv[6]);
    R = atoi(argv[7]);
    K = atoi(argv[8]);

    if (d < 1 || d > 32 || D < 2 || K < 1 || 2 * K > 63 || K2 < 1 || K2 > 64 || M < 2) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2 * K * G;
    if (G > 16000 || N > 16000) {
        printf("0 0\n");
        return 0;
    }
    powr[0] = 1 % M;
    for (int t = 1; t < K2; t++) powr[t] = (int)((long)powr[t - 1] * (R % M) % M);
    if ((long)powr[K2 - 1] * (R % M) % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now();
    t_end = t0 + limit - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    sinv = malloc(sizeof(int) * G);
    nbr = malloc(sizeof(int) * (size_t)d * N);
    lay = malloc(sizeof(int) * (size_t)d * K);
    vol = malloc(sizeof(int) * (size_t)d * K);
    ra = malloc(sizeof(uint64_t) * N);
    rb = malloc(sizeof(uint64_t) * N);
    if (!sinv || !nbr || !lay || !vol || !ra || !rb) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < G; x++) sinv[x] = ginv(x);

    for (int l = 0; l < d; l++) {
        int perm[64];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            lay[l * K + i] = perm[i];
            vol[l * K + i] = rndint(G);
        }
        rebuild_layer(l);
    }

    const long PEN = 4L * G;
    long cost = unreached() + PEN * dupcount();
    long c0 = cost > 0 ? cost : 1;
    double tstart = now();
    double span = t_end - tstart;
    if (span < 0.1) span = 0.1;
    long it = 0;

    while (cost > 0) {
        if ((it & 7) == 0 && now() > t_end) break;
        it++;
        double frac = (now() - tstart) / span;
        if (frac > 1.0) frac = 1.0;
        double T = 0.5 + 0.002 * (double)c0 * (1.0 - frac);

        if (K >= 2 && rndint(100) < 20) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int tmp = lay[l * K + i1];
            lay[l * K + i1] = lay[l * K + i2];
            lay[l * K + i2] = tmp;
            rebuild_layer(l);
            long nc = unreached() + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = lay[l * K + i1];
                lay[l * K + i1] = lay[l * K + i2];
                lay[l * K + i2] = tmp;
                rebuild_layer(l);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = vol[l * K + i];
            int nw = rndint(G);
            if (nw == old) continue;
            vol[l * K + i] = nw;
            rebuild_layer(l);
            long nc = unreached() + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                vol[l * K + i] = old;
                rebuild_layer(l);
            }
        }
    }

    if (cost == 0) {
        long m = (long)K * G * d;
        printf("%d %ld\n", N, m);
        for (int v = 0; v < K * G; v++)
            for (int l = 0; l < d; l++)
                printf("%d %d\n", v, nbr[(size_t)l * N + v]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent program).
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

_KS = (1, 2, 3, 4, 6, 8)


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

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)
    cap = min(lib.moore_bound(d, D), 16000)

    # Grow the target size geometrically; each success doubles the step, each failure halves it.
    inc = max(4, best_n // 8)
    while True:
        remaining = final - time.monotonic()
        if remaining < 4.0 or best_n >= cap:
            break
        slice_s = min(remaining - 1.5, 12.0)
        k = rng.choice(_KS)
        target = min(cap, best_n + inc)
        g = _sample_group(-(-target // (2 * k)), rng)
        if g is None:
            inc = max(2, inc // 2)
            continue
        m, k2, r = g
        n_try = 2 * k * m * k2
        if n_try > cap or n_try <= best_n or 2 * k > 62:
            inc = max(2, inc // 2)
            continue
        try:
            text = lib.run_c(C_SOURCE, [d, D, rng.randrange(1 << 30), round(slice_s, 2), m, k2, r, k],
                             timeout=slice_s + 10)
            n, e = lib.parse_graph_text(text)
        except Exception:
            n, e = 0, []
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n
            inc = min(max(4, inc * 2), cap)
        else:
            inc = max(2, inc // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
