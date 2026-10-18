import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: bi-Cayley lifts over Z_m x| Z_k2 (simulated annealing).
#
# Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h, G = m*k2.
# Layer l pairs A_i with B_{lay[l][i]} through voltage s: A_{i,g} ~ B_{j, g*s}.
# Each layer is a permutation, so every vertex has degree d exactly.
# Cost = unreached (block, vertex) pairs + PEN * duplicate darts.
# Reach sets are 2K-bit masks (K <= 4), so one byte per vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000L

static int d_, D_, K, M, K2, G, N;
static int *pw, *sinv, *lay, *linv, *S, *nb;
static uint8_t *rch, *rtmp, *rsave;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double runi(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc8(uint8_t x) { int c = 0; while (x) { c += x & 1; x >>= 1; } return c; }

/* (a,b)(c,e) = (a + r^b c, b + e) with element a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long t = ((long)a + (long)pw[b] * c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static void rebuild(void) {
    for (int l = 0; l < d_; l++) {
        for (int u = 0; u < N; u++) {
            int blk = u / G, g = u % G, v;
            if (blk < K) {
                int i = blk, j = lay[l * K + i];
                v = (K + j) * G + gmul(g, S[l * K + i]);
            } else {
                int j = blk - K, i = linv[l * K + j];
                v = i * G + gmul(g, sinv[S[l * K + i]]);
            }
            nb[l * N + u] = v;
        }
    }
}

static long eval_cost(void) {
    memset(rch, 0, (size_t)N);
    for (int b = 0; b < 2 * K; b++) rch[(long)b * G] = (uint8_t)(1u << b);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = rch[v];
            for (int l = 0; l < d_; l++) x |= rch[nb[l * N + v]];
            rtmp[v] = x;
            if (x != rch[v]) changed = 1;
        }
        uint8_t *t = rch; rch = rtmp; rtmp = t;
        if (!changed) break;
    }
    long pop = 0;
    for (int v = 0; v < N; v++) pop += pc8(rch[v]);
    long unreached = 2L * K * N - pop;
    long dup = 0;
    int T = d_ * K;
    for (int a = 0; a < T; a++)
        for (int b = 0; b < a; b++)
            if (a % K == b % K && lay[a] == lay[b] && S[a] == S[b]) dup++;
    return unreached + PEN * dup;
}

static void swap_lay(int l, int i1, int i2) {
    int *la = lay + l * K, *li = linv + l * K;
    int t = la[i1]; la[i1] = la[i2]; la[i2] = t;
    li[la[i1]] = i1;
    li[la[i2]] = i2;
}

int main(int argc, char **argv) {
    if (argc < 11) { fprintf(stderr, "usage: d D k m k2 r seed iters patience tlim\n"); return 1; }
    clock_t t0 = clock();
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int R = atoi(argv[6]);
    rs ^= (uint64_t)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd();
    long iters = atol(argv[8]);
    long patience = atol(argv[9]);
    double tlim = atof(argv[10]);

    G = M * K2;
    N = 2 * K * G;

    pw = malloc(sizeof(int) * K2);
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long)pw[b - 1] * R % M);

    sinv = malloc(sizeof(int) * G);
    for (int s = 0; s < G; s++) {
        int a = s / K2, b = s % K2, nbk = (K2 - b) % K2;
        long na = (M - ((long)pw[nbk] * a) % M) % M;
        sinv[s] = (int)(na * K2 + nbk);
    }

    lay = malloc(sizeof(int) * d_ * K);
    linv = malloc(sizeof(int) * d_ * K);
    S = malloc(sizeof(int) * d_ * K);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc((size_t)N);
    rtmp = malloc((size_t)N);
    rsave = malloc((size_t)N);

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) lay[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1), t = lay[l * K + i];
            lay[l * K + i] = lay[l * K + j];
            lay[l * K + j] = t;
        }
        for (int i = 0; i < K; i++) linv[l * K + lay[l * K + i]] = i;
        for (int i = 0; i < K; i++) S[l * K + i] = rint_(G);
    }

    rebuild();
    long cost = eval_cost();
    long c0 = cost > 1 ? cost : 1;
    long best_cost = cost;
    long last = 0;
    int full = (1 << (2 * K)) - 1;

    for (long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last > patience) break;
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > tlim) break;
        double temp = 0.01 * (double)c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        memcpy(rsave, rch, (size_t)N);

        if (K >= 2 && runi() < 0.25) {
            int l = rint_(d_);
            int i1 = rint_(K);
            int i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            swap_lay(l, i1, i2);
            rebuild();
            long c2 = eval_cost();
            if (c2 <= cost || runi() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                swap_lay(l, i1, i2);
                rebuild();
                memcpy(rch, rsave, (size_t)N);
            }
            continue;
        }

        int l, i;
        int bad_cnt = 0;
        int targeted = runi() < 0.4;
        if (targeted) {
            for (int v = 0; v < N; v++) if (rch[v] != full) bad_cnt++;
        }
        if (targeted && bad_cnt > 0) {
            int pick = rint_(bad_cnt), u = -1;
            for (int v = 0; v < N; v++) {
                if (rch[v] != full) {
                    if (pick == 0) { u = v; break; }
                    pick--;
                }
            }
            int blk = u / G;
            l = rint_(d_);
            if (blk < K) i = blk;
            else i = linv[l * K + (blk - K)];
        } else {
            l = rint_(d_);
            i = rint_(K);
        }

        int idx = l * K + i;
        int old = S[idx];
        int nw = rint_(G);
        if (nw == old) continue;
        S[idx] = nw;
        rebuild();
        long c2 = eval_cost();
        if (c2 <= cost || runi() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            S[idx] = old;
            rebuild();
            memcpy(rch, rsave, (size_t)N);
        }
    }

    if (cost == 0) {
        long edges = (long)K * G * d_;
        printf("%d %ld\n", N, edges);
        for (int u = 0; u < K * G; u++)
            for (int l = 0; l < d_; l++)
                printf("%d %d\n", u, nb[l * N + u]);
    } else {
        printf("0 0\n");
    }
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


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 3.0))
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

    # Main search: C annealing per sampled group, bandit over base sizes k.
    ks = (1, 2, 3, 4)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    errors = 0
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        slice_t = min(remaining, 6.0)
        try:
            txt = lib.run_c(
                C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 2 ** 31), 20000, 4000, slice_t],
                timeout=slice_t + 10.0,
            )
            n, e = lib.parse_graph_text(txt)
        except (RuntimeError, ValueError):
            errors += 1
            if errors >= 3:
                break
            continue
        if n > 0:
            wins[k] += 1
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
