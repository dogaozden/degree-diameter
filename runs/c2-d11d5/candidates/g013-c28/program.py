"""Bi-Cayley voltage-lift annealing over semidirect groups, run entirely in C.

Construction: vertices are A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, where G = Z_m x| Z_k2
(element a*k2+b). Layer l joins A_i to B_{p} through voltage s, so A_{i,g} ~ B_{p, g*s}. Each layer
is a permutation of the k blocks, so the graph is d-regular and bipartite. Left multiplication by
the group is an automorphism, so the distance condition only needs checking from the 2k block
representatives. C anneals the layer permutations and voltages with bitset reachability, over
k up to 16 blocks, and ratchets the target order upward. The fallbacks are K_{d,d}, PG(2,q),
Araujo-Lopez, and W(q) for D = 4. Every returned graph passes lib.is_valid.
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

#define MAXK 16
#define MAXD 32
#define MAXV 16384
#define MAXGRP 64
#define PENALTY 1000L

static int d, D;
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
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_gm x|_r Z_gk2, element a*gk2 + b, product (a,b)(c,e) = (a + r^b c, b + e). */
static int gm = 2, gk2 = 1, go = 2;
static int gpw[MAXGRP];

static void setup_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        gpw[b] = (int)p;
        p = (p * r) % m;
    }
}
static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    int t = (a + gpw[b] * c) % gm;
    return t * gk2 + (b + e) % gk2;
}
static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    int t = (gm - (gpw[nb] * a) % gm) % gm;
    return t * gk2 + nb;
}

static int kb, nv;
static uint64_t FULL;
static int lay[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int nbr[MAXD][MAXV];
static uint64_t RA[MAXV], RB[MAXV], curR[MAXV];
static uint64_t *last_res = NULL;
static int bL[MAXD][MAXK], bV[MAXD][MAXK];

static void setdart(int l, int i) {
    int p = lay[l][i], s = volt[l][i], si = ginv(s);
    for (int g = 0; g < go; g++) {
        nbr[l][i * go + g] = (kb + p) * go + gmul(g, s);
        nbr[l][(kb + p) * go + g] = i * go + gmul(g, si);
    }
}

/* Unordered pairs at distance > D, summed over block representatives (times symmetry). */
static long reach_cost(void) {
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)nv);
    for (int b = 0; b < 2 * kb; b++) cur[(size_t)b * go] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < nv; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < nv; v++) bad += 2 * kb - __builtin_popcountll(cur[v]);
    last_res = cur;
    return bad;
}

/* Number of repeated (block, voltage) choices, which would create multi-edges. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < kb; i++)
        for (int a = 0; a < d; a++)
            for (int b = a + 1; b < d; b++)
                if (lay[a][i] == lay[b][i] && volt[a][i] == volt[b][i]) c++;
    return c;
}

static int anneal(double deadline, long iters, long patience) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) lay[l][i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1), t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < kb; i++) {
            volt[l][i] = rndint(go);
            setdart(l, i);
        }
    }
    long cost = reach_cost() + PENALTY * dup_count();
    memcpy(curR, last_res, sizeof(uint64_t) * (size_t)nv);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (kb >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(kb), i2 = rndint(kb - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tmp;
            setdart(l, i1);
            setdart(l, i2);
            long c2 = reach_cost() + PENALTY * dup_count();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(curR, last_res, sizeof(uint64_t) * (size_t)nv);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tmp;
                setdart(l, i1);
                setdart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tr = 0; tr < 30 && v < 0; tr++) {
                int c = rndint(nv);
                if (curR[c] != FULL) v = c;
            }
            if (v >= 0) {
                int blk = v / go;
                l = rndint(d);
                if (blk < kb) {
                    i = blk;
                } else {
                    for (int q = 0; q < kb; q++)
                        if (lay[l][q] == blk - kb) { i = q; break; }
                }
            }
        }
        if (i < 0) {
            l = rndint(d);
            i = rndint(kb);
        }
        int old = volt[l][i], nw = rndint(go);
        if (nw == old) continue;
        volt[l][i] = nw;
        setdart(l, i);
        long c2 = reach_cost() + PENALTY * dup_count();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(curR, last_res, sizeof(uint64_t) * (size_t)nv);
            if (cost < best) { best = cost; last = t; }
        } else {
            volt[l][i] = old;
            setdart(l, i);
        }
    }
    return cost == 0;
}

static int pick_k(const double *trials, const double *wins) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bestk = 1;
    double bs = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bestk = k; }
    }
    return bestk;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    double t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20,
                              24, 30, 32, 36, 40, 48, 60};
    const int nk2 = (int)(sizeof(K2S) / sizeof(K2S[0]));
    double trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0.0; wins[k] = 0.0; }

    double goal = start_n > 0 ? 1.02 * (double)start_n : 4.0 * d;
    long best_n = start_n;
    int have = 0, bk = 0, bm = 0, bk2 = 0, br = 0;

    while (1) {
        double left = t_end - now();
        if (left < 0.3) break;
        int k = pick_k(trials, wins);
        int tg = (int)(goal / (2.0 * k) + rndint(3));
        if (tg < 2) tg = 2;
        int k2 = K2S[rndint(nk2)];
        int m = (tg + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1) {
            r = -1;
            for (int tr = 0; tr < 80 && m >= 3; tr++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) {
                goal = fmax((double)best_n * 1.02, goal * 0.99);
                continue;
            }
        }
        long gord = (long)m * k2;
        if (gord < 2 || 2L * k * gord > MAXV) {
            goal = fmax((double)best_n * 1.02, goal * 0.97);
            continue;
        }
        if (2L * k * gord <= best_n) {
            goal = fmax(goal, (double)best_n * 1.02);
            continue;
        }

        setup_group(m, k2, r);
        kb = k;
        go = (int)gord;
        nv = 2 * kb * go;
        FULL = (1ULL << (2 * kb)) - 1;
        trials[k] += 1.0;
        double cap = now() + fmax(1.5, left / 3.0);
        double dl = cap < t_end ? cap : t_end;

        if (anneal(dl, 300000, 25000)) {
            wins[k] += 1.0;
            best_n = nv;
            have = 1;
            bk = kb;
            bm = m;
            bk2 = k2;
            br = r;
            memcpy(bL, lay, sizeof(lay));
            memcpy(bV, volt, sizeof(volt));
            goal = fmax(goal, (double)nv * 1.04);
        } else {
            goal = fmax((double)best_n * 1.02, goal * 0.99);
        }
    }

    if (!have) { printf("0 0\n"); return 0; }

    kb = bk;
    setup_group(bm, bk2, br);
    go = bm * bk2;
    nv = 2 * kb * go;
    long M = (long)d * kb * go;
    printf("%d %ld\n", nv, M);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < kb; i++) {
            int p = bL[l][i], s = bV[l][i];
            for (int g = 0; g < go; g++)
                printf("%d %d\n", i * go + g, (kb + p) * go + gmul(g, s));
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (fallbacks and calibration cases).
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

    # Safe fallback: K_{d,d} is bipartite, d-regular and has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions. Calibration-style cases return immediately.
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

    # Main search: the C engine anneals bi-Cayley lifts over semidirect groups, with
    # up to 16 base blocks per side, and ratchets the target order upward.
    # best_n is passed in only so C knows the bar to beat; C returns its own lift or "0 0".
    remaining = final - time.monotonic()
    if d >= 2 and D >= 3 and remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 2.0, 2), best_n],
                             stdin_graph=None, timeout=remaining + 5.0)
            n_out, e_out = lib.parse_graph_text(text)
            consider(n_out, e_out)
        except Exception:
            pass

    return best
