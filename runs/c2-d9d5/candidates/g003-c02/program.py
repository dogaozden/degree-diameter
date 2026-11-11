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
#include <time.h>
#include <math.h>

#define MAXD 16
#define MAXK 8
#define MAXB 64
#define PENALTY 1000.0
#define PATIENCE 2500
#define REHEAT 4000

/* Bi-Cayley lift search over G = Z_M x| Z_K2 (element a*K2+b, (a,b)(c,e) = (a+r^b c, b+e)).
   Vertices: A-block i occupies i*G..i*G+G-1, B-block j occupies (K+j)*G..(K+j+1)*G-1.
   Layer l joins A-block i to B-block tgt[l][i] by voltage vol[l][i]: A_g ~ B_{g*s}.
   Each layer is a permutation of blocks, so every vertex has degree dg.
   Cost = number of (block start, vertex) pairs at distance > dia (computed with bitmasks),
   plus a penalty for duplicate darts. Left multiplication is an automorphism, so the
   block starts suffice. */

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int dg, dia, K, M, K2, R, G, N;
static int rp[MAXB];
static int *invS;
static int tgt[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int *nbr;
static uint32_t *rch, *rch2;

static int popcnt(uint32_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    long long ra = ((long long)a + (long long)rp[b] * c) % M;
    int rb = (b + e) % K2;
    return (int)ra * K2 + rb;
}

static void set_block(int l, int i) {
    int j = tgt[l][i], s = vol[l][i];
    int ua = i * G, ub = (K + j) * G, is = invS[s];
    int *A = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        A[ua + g] = ub + gmul(g, s);
        A[ub + g] = ua + gmul(g, is);
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < dg; l1++)
            for (int l2 = l1 + 1; l2 < dg; l2++)
                if (tgt[l1][i] == tgt[l2][i] && vol[l1][i] == vol[l2][i]) c++;
    return c;
}

static double compute_cost(void) {
    int nb = 2 * K;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < nb; b++) rch[b * G] |= (1u << b);
    for (int t = 0; t < dia; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = rch[v];
            for (int l = 0; l < dg; l++) x |= rch[nbr[(size_t)l * N + v]];
            rch2[v] = x;
            changed |= (x != rch[v]);
        }
        uint32_t *tmp = rch; rch = rch2; rch2 = tmp;
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) cost += nb - popcnt(rch[v]);
    return (double)cost + PENALTY * (double)dupcount();
}

static void random_init(void) {
    for (int l = 0; l < dg; l++) {
        for (int i = 0; i < K; i++) tgt[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rnd_int(i + 1);
            int t = tgt[l][i]; tgt[l][i] = tgt[l][r]; tgt[l][r] = t;
        }
        for (int i = 0; i < K; i++) vol[l][i] = rnd_int(G);
        for (int i = 0; i < K; i++) set_block(l, i);
    }
}

static int find_i(int l, int j) {
    for (int i = 0; i < K; i++) if (tgt[l][i] == j) return i;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    dg = atoi(argv[1]);
    dia = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    double t_end = now_sec() + tl;
    if (dg < 1 || dg > MAXD || K < 1 || K > MAXK || M < 2 || K2 < 1 || K2 > MAXB || dia < 1) {
        printf("0 0\n"); return 0;
    }
    G = M * K2;
    N = 2 * K * G;

    rp[0] = 1 % M;
    for (int b = 1; b < K2; b++) rp[b] = (int)((long long)rp[b - 1] * R % M);
    if ((long long)rp[K2 - 1] * R % M != (long long)(1 % M)) { printf("0 0\n"); return 0; }
    {
        int a = R, b = M;
        while (b) { int t = a % b; a = b; b = t; }
        if (a != 1) { printf("0 0\n"); return 0; }
    }

    rs = seed * 2654435761ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int t = 0; t < 20; t++) rnd64();

    invS = malloc(sizeof(int) * (size_t)G);
    nbr = malloc(sizeof(int) * (size_t)dg * (size_t)N);
    rch = malloc(sizeof(uint32_t) * (size_t)N);
    rch2 = malloc(sizeof(uint32_t) * (size_t)N);
    if (!invS || !nbr || !rch || !rch2) { printf("0 0\n"); return 0; }
    for (int s = 0; s < G; s++) {
        int a = s / K2, b = s % K2;
        int bp = (K2 - b) % K2;
        long long na = (M - ((long long)rp[bp] * a) % M) % M;
        invS[s] = (int)na * K2 + bp;
    }

    uint32_t full = (1u << (2 * K)) - 1u;
    int found = 0;
    while (!found && now_sec() < t_end) {
        random_init();
        double cost = compute_cost();
        double c0 = cost > 1.0 ? cost : 1.0;
        long best_it = 0;
        double best_c = cost;
        for (long t = 0;; t++) {
            if (cost == 0.0) { found = 1; break; }
            if ((t & 127) == 0 && now_sec() >= t_end) break;
            if (t - best_it > PATIENCE) break;
            double temp = 0.02 * c0 * (1.0 - (double)(t % REHEAT) / REHEAT);
            if (temp < 0.3) temp = 0.3;

            if (K >= 2 && rnd_unit() < 0.25) {
                int l = rnd_int(dg);
                int i1 = rnd_int(K), i2 = rnd_int(K - 1);
                if (i2 >= i1) i2++;
                int tt = tgt[l][i1]; tgt[l][i1] = tgt[l][i2]; tgt[l][i2] = tt;
                set_block(l, i1); set_block(l, i2);
                double nc = compute_cost();
                if (nc <= cost || rnd_unit() < exp(-(nc - cost) / temp)) {
                    cost = nc;
                    if (cost < best_c) { best_c = cost; best_it = t; }
                } else {
                    tt = tgt[l][i1]; tgt[l][i1] = tgt[l][i2]; tgt[l][i2] = tt;
                    set_block(l, i1); set_block(l, i2);
                }
                continue;
            }

            int l = rnd_int(dg), i = rnd_int(K);
            if (rnd_unit() < 0.4) {
                int v = -1;
                for (int tries = 0; tries < 30; tries++) {
                    int c = rnd_int(N);
                    if (rch[c] != full) { v = c; break; }
                }
                if (v >= 0) {
                    int u = v / G;
                    if (u < K) i = u;
                    else i = find_i(l, u - K);
                }
            }
            int old = vol[l][i];
            int nv = rnd_int(G);
            if (nv == old) continue;
            vol[l][i] = nv;
            set_block(l, i);
            double nc = compute_cost();
            if (nc <= cost || rnd_unit() < exp(-(nc - cost) / temp)) {
                cost = nc;
                if (cost < best_c) { best_c = cost; best_it = t; }
            } else {
                vol[l][i] = old;
                set_block(l, i);
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    long mE = (long)K * G * dg;
    printf("%d %ld\n", N, mE);
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < dg; l++)
            printf("%d %d\n", u, nbr[(size_t)l * N + u]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact or structured starting graphs.
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
# Group choice (new helper): pick Z_M x| Z_K2 with order just above a target,
# sampling several automorphisms r with r^K2 = 1 mod M.
# ----------------------------------------------------------------------------

_K2S = (1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12)


def _pick_group(gmin, rng):
    """Return (M, K2, R) with M * K2 >= gmin and R a unit of order dividing K2 mod M."""
    for _ in range(40):
        k2 = rng.choice(_K2S)
        m = max(2, -(-gmin // k2))
        if k2 == 1:
            return m, 1, 1
        opts = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if opts:
            return m, k2, rng.choice(opts)
    return max(2, gmin), 1, 1


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search in C; each call searches one (K, group) pair and
    # returns at the first valid lift, so each success raises the target.
    failures = 0
    K_CHOICES = (1, 2, 2, 3, 4, 6, 8)
    while failures < 3:
        remain = end - time.monotonic()
        if remain < 2.5:
            break
        K = rng.choice(K_CHOICES)
        gmin = best_n // (2 * K) + 1
        gmin += rng.randrange(0, gmin // 50 + 2)
        m, k2, r = _pick_group(gmin, rng)
        if 2 * K * m * k2 <= best_n:
            continue
        slice_s = min(remain - 0.5, rng.uniform(4.0, 9.0))
        if slice_s < 1.5:
            break
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1, 1 << 30), round(slice_s - 0.8, 2), K, m, k2, r],
                timeout=slice_s + 5.0,
            )
            n, e = lib.parse_graph_text(out)
            failures = 0
        except (RuntimeError, ValueError):
            failures += 1
            continue
        if n > 1:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
