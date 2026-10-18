"""Bi-Cayley lift search in C (replaces the Python/numpy annealer).

Every candidate is a voltage lift of a k-vertex-per-side base over a semidirect product
Z_m x| Z_k2. The C engine runs a bandit over base sizes k and group choices, anneals the
voltages until every block representative is within distance D of every vertex, and keeps
the largest valid lift. Lifts with permutation layers are exactly d-regular and bipartite.

Python supplies exact constructions (projective planes, Araujo-Pardo-Lopez, W(q)) as
fallbacks. Every returned graph is checked with lib.is_valid, and K_{d,d} is the last resort.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXD 32
#define MAXK 6
#define PEN 1000
#define ITERS 4000
#define PATIENCE 1200

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_gm x| Z_gk2 with (a,b)(c,e) = (a + r^b c, b + e); element coded a*gk2 + b. */
static int gm, gk2;
static long long gpw[64];

static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        gpw[b] = p;
        p = (p * r) % m;
    }
}
static int gmul(int x, int y) {
    int a = x / gk2, b = x - a * gk2;
    int c = y / gk2, e = y - c * gk2;
    long long t = ((long long)a + gpw[b] * c) % gm;
    int f = (b + e) % gk2;
    return (int)(t * gk2 + f);
}
static int ginv(int s) {
    int c = s / gk2, e = s - c * gk2;
    int b = (gk2 - e) % gk2;
    long long t = (gpw[b] * c) % gm;
    long long a = (gm - t) % gm;
    return (int)(a * gk2 + b);
}

/* Lift state: K base vertices per side, G group elements, NV = 2*K*G vertices. */
static int K, G, NV;
static int lay[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int nbr[MAXN][MAXD];
static int bestNbr[MAXN][MAXD];
static int bestNV = 0, bestK = 0, bestG = 0;
static uint64_t RA[MAXN], RB[MAXN], bufA[MAXN], bufB[MAXN];

/* A block i vertex i*G+g joins B block j=lay[l][i] vertex (K+j)*G + g*s. */
static void set_block(int l, int i) {
    int j = lay[l][i], s = sv[l][i];
    int is = ginv(s);
    int ao = i * G, bo = (K + j) * G;
    for (int g = 0; g < G; g++) nbr[ao + g][l] = bo + gmul(g, s);
    for (int h = 0; h < G; h++) nbr[bo + h][l] = ao + gmul(h, is);
}

/* Bit b of out[v] is set when v is within distance D of block representative b*G. */
static int evaluate(uint64_t *out) {
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < NV; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(long)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[v][l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    int unreached = 0;
    for (int v = 0; v < NV; v++) {
        out[v] = cur[v];
        unreached += 2 * K - __builtin_popcountll(cur[v]);
    }
    return unreached;
}

/* Duplicate edges arise only from equal (i, j, s) triples in two layers. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

/* Anneal layers and voltages until every vertex reaches every block representative. */
static int anneal(double deadline) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            lay[l][i] = p[i];
            sv[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_block(l, i);

    uint64_t *cur_r = RA, *cand_r = RB;
    long cost = evaluate(cur_r) + (long)PEN * dupcount();
    double c0 = cost > 0 ? (double)cost : 1.0;
    double T0 = 2.0 + 0.02 * c0, T1 = 0.3;
    uint64_t full = (2 * K >= 64) ? ~0ULL : ((1ULL << (2 * K)) - 1);
    long bestc = cost;
    int last = 0;

    for (int t = 0; t < ITERS; t++) {
        if (cost == 0) break;
        if (t - last > PATIENCE) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / ITERS);

        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tmp;
            set_block(l, i1);
            set_block(l, i2);
            long c2 = evaluate(cand_r) + (long)PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                uint64_t *sw = cur_r;
                cur_r = cand_r;
                cand_r = sw;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tmp = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tmp;
                set_block(l, i1);
                set_block(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            if (rnd01() < 0.5) {
                int v = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int w = rndint(NV);
                    if (cur_r[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    if (v < K * G) {
                        i = v / G;
                    } else {
                        int j = v / G - K;
                        for (int q = 0; q < K; q++)
                            if (lay[l][q] == j) { i = q; break; }
                    }
                }
            }
            int old = sv[l][i], nv = rndint(G);
            if (nv == old) continue;
            sv[l][i] = nv;
            set_block(l, i);
            long c2 = evaluate(cand_r) + (long)PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                uint64_t *sw = cur_r;
                cur_r = cand_r;
                cand_r = sw;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                sv[l][i] = old;
                set_block(l, i);
            }
        }
    }
    return cost == 0;
}

/* Random semidirect group with order m*k2 >= Gt. */
static int sample_group(int Gt, int *mo, int *k2o, int *ro) {
    static const int K2S[12] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16};
    for (int tr = 0; tr < 100; tr++) {
        int k2 = K2S[rndint(12)];
        int m = (Gt + k2 - 1) / k2 + rndint(3);
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1 && rnd01() < 0.6) {
            if (m < 3) continue;
            int found = 0;
            for (int q = 0; q < 200; q++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) != 1) continue;
                if (powmod_ll(c, k2, m) == 1 % m) { r = c; found = 1; break; }
            }
            if (!found) continue;
        }
        *mo = m;
        *k2o = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

static void print_best(void) {
    long m = (long)bestK * bestG * d;
    printf("%d %ld\n", bestNV, m);
    for (int v = 0; v < bestK * bestG; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, bestNbr[v][l]);
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
    long bestN = argc > 5 ? atol(argv[5]) : 0;
    if (bestN < 0) bestN = 0;
    double t0 = now();
    double deadline = t0 + limit * 0.85 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || D < 3 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    long lim = moore_bound();
    if (lim > MAXN) lim = MAXN;

    double f = 1.05;
    int trials[MAXK + 1], wins[MAXK + 1];
    for (int c = 0; c <= MAXK; c++) { trials[c] = 0; wins[c] = 0; }

    while (now() < deadline) {
        if (bestN + 2 > lim) break;
        int k = 1;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.05 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        double tg = (double)bestN * f;
        long target = (long)ceil(tg);
        if (target < bestN + 2) target = bestN + 2;
        if (target > lim) target = lim;
        int Gt = (int)((target + 2 * k - 1) / (2 * k));
        if (Gt < 2) Gt = 2;

        int m, k2, r;
        if (!sample_group(Gt, &m, &k2, &r)) {
            f = (f - 0.01 < 1.0) ? 1.0 : f - 0.01;
            continue;
        }
        long Gc = (long)m * k2;
        long NVc = 2L * k * Gc;
        if (NVc <= bestN || NVc > lim) {
            f = (f - 0.01 < 1.0) ? 1.0 : f - 0.01;
            continue;
        }

        K = k;
        G = (int)Gc;
        NV = (int)NVc;
        set_group(m, k2, r);
        trials[k]++;
        int ok = anneal(deadline);
        if (ok) {
            wins[k]++;
            memcpy(bestNbr, nbr, sizeof(nbr));
            bestNV = NV;
            bestK = K;
            bestG = G;
            bestN = NV;
            f = (f + 0.03 > 1.15) ? 1.15 : f + 0.03;
        } else {
            f = (f - 0.01 < 1.0) ? 1.0 : f - 0.01;
        }
    }

    if (bestNV > 0) print_best();
    else printf("0 0\n");
    return 0;
}
'''


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

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

    if D <= 2 or d < 3:
        return best

    # Bi-Cayley lift search in C, seeded with the current best order.
    remaining = final - time.monotonic() - 1.5
    if remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             stdin_graph=None, timeout=remaining + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
