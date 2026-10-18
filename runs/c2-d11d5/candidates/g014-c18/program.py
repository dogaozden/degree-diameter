"""Bi-Cayley voltage-lift search with the whole search loop in C.

Exact constructions (projective planes, Araujo-Pardo-Lopez, generalized quadrangles) are
built in Python first. A C engine then anneals bi-Cayley lifts over semidirect products
Z_m x| Z_k2 with k base vertices per side. Each lift is an incidence structure whose d layers
are block permutations with voltages. Diameter is checked on the 2k block representatives only,
using bitmasks, since left translation by the group is an automorphism.

Changes from the parent: the lift search and bandit now run in C with incremental dart updates,
so far more candidates are tested per second. Every returned graph is checked with lib.is_valid,
and K_{d,d} is the fallback.
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

#define MAXK 8
#define MAXL 64
#define MAXN 16384
#define MAXG 8192
#define PEN 1000L
#define KMAX 6
#define ITERS 30000L
#define PATIENCE 6000L

/* Lift: vertices A_{i,g} = i*G + g and B_{p,h} = (k+p)*G + h, group Z_m x| Z_k2, element (a,b) = a*k2+b.
 * Layer l joins A_{i,g} to B_{layer[l][i], g*vol[l][i]}. Each layer is a permutation of the blocks,
 * so every vertex has degree d. */
typedef struct {
    int k, G, m, k2, r;
    int pw[64];
    int layer[MAXL][MAXK];
    int vol[MAXL][MAXK];
} Lift;

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static int nbr[MAXL][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN];
static uint64_t *reach_now = bufA;

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
static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Random semidirect group Z_m x| Z_k2 with m*k2 >= target and r^k2 = 1 mod m. */
static int sample_group(int target, int *mo, int *k2o, int *ro) {
    static const int K2[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = -1;
        if (k2 == 1) {
            r = 1;
        } else {
            int tryneg = (k2 == 2 && rndint(10) < 3);
            if (tryneg) {
                r = m - 1;
                if (r < 1 || gcd_i(r, m) != 1 || powmod_l(r, k2, m) != 1 % m) r = -1;
            }
            if (r < 0) {
                for (int c = 0; c < 60; c++) {
                    int cand = (m > 2) ? 2 + rndint(m - 2) : 1;
                    if (gcd_i(cand, m) == 1 && powmod_l(cand, k2, m) == 1 % m) { r = cand; break; }
                }
            }
            if (r < 0) continue;
        }
        *mo = m;
        *k2o = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

static int mulg(const Lift *L, int x, int y) {
    int k2 = L->k2, m = L->m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    int aa = (int)(((long)a + (long)L->pw[b] * c) % m);
    int bb = (b + e) % k2;
    return aa * k2 + bb;
}

static int invg(const Lift *L, int x) {
    int k2 = L->k2, m = L->m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long t = (-(long)L->pw[nb] * a) % m;
    if (t < 0) t += m;
    return (int)t * k2 + nb;
}

static void random_lift(Lift *L, int k, int G, int m, int k2, int r) {
    L->k = k;
    L->G = G;
    L->m = m;
    L->k2 = k2;
    L->r = r;
    L->pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) L->pw[b] = (int)((long)L->pw[b - 1] * r % m);
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            L->layer[l][i] = perm[i];
            L->vol[l][i] = rndint(G);
        }
    }
}

/* Rewrite the neighbour table entries of dart (l, i): A-block i and its partner B-block. */
static void set_dart(const Lift *L, int l, int i) {
    int k = L->k, G = L->G;
    int p = L->layer[l][i], s = L->vol[l][i], si = invg(L, s);
    int ai = i * G, bp = (k + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ai + g] = bp + mulg(L, g, s);
        nbr[l][bp + g] = ai + mulg(L, g, si);
    }
}

static void build_all(const Lift *L) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < L->k; i++) set_dart(L, l, i);
}

/* Unreached (vertex, representative) pairs after D rounds; sets reach_now to the final masks. */
static long compute_reach(const Lift *L) {
    int k = L->k, G = L->G, N = 2 * k * G;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(long)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long un = 0;
    for (int v = 0; v < N; v++) un += 2 * k - __builtin_popcountll(cur[v]);
    reach_now = cur;
    return un;
}

/* Repeated (block, voltage) keys on one A-block make a multi-edge. */
static long dupcount(const Lift *L) {
    long c = 0;
    for (int i = 0; i < L->k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (L->layer[l1][i] == L->layer[l2][i] && L->vol[l1][i] == L->vol[l2][i]) c++;
    return c;
}

/* Simulated annealing. Returns 1 when cost 0 is reached (valid graph in L). */
static int anneal(Lift *L, long iters, long patience, double deadline) {
    int k = L->k, G = L->G, N = 2 * k * G;
    uint64_t full = (1ULL << (2 * k)) - 1;
    build_all(L);
    long cost = compute_reach(L) + PEN * dupcount(L);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_c = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        long c2;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = L->layer[l][i1];
            L->layer[l][i1] = L->layer[l][i2];
            L->layer[l][i2] = tmp;
            set_dart(L, l, i1);
            set_dart(L, l, i2);
            c2 = compute_reach(L) + PEN * dupcount(L);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best_c) { best_c = cost; last = t; }
            } else {
                tmp = L->layer[l][i1];
                L->layer[l][i1] = L->layer[l][i2];
                L->layer[l][i2] = tmp;
                set_dart(L, l, i1);
                set_dart(L, l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tr = 0; tr < 30; tr++) {
                int c = rndint(N);
                if (reach_now[c] != full) { v = c; break; }
            }
            if (v >= 0) {
                int blk = v / G;
                l = rndint(d);
                if (blk < k) {
                    i = blk;
                } else {
                    int p = blk - k;
                    for (int j = 0; j < k; j++)
                        if (L->layer[l][j] == p) { i = j; break; }
                }
            }
        }
        if (i < 0) {
            l = rndint(d);
            i = rndint(k);
        }
        int old = L->vol[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        L->vol[l][i] = nw;
        set_dart(L, l, i);
        c2 = compute_reach(L) + PEN * dupcount(L);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best_c) { best_c = cost; last = t; }
        } else {
            L->vol[l][i] = old;
            set_dart(L, l, i);
        }
    }
    return cost == 0;
}

static void print_lift(const Lift *L) {
    int k = L->k, G = L->G, N = 2 * k * G;
    long m = (long)(k * G) * d;
    printf("%d %ld\n", N, m);
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[l][u]);
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
    long best_N = argc > 5 ? atol(argv[5]) : 0;
    double deadline = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXL || D < 2) {
        printf("0 0\n");
        return 0;
    }

    static Lift cur, best;
    int have = 0;
    double goal = (double)best_N * 1.05;
    if (goal < 32.0) goal = 32.0;
    long trials[KMAX + 1], wins[KMAX + 1];
    for (int j = 0; j <= KMAX; j++) { trials[j] = 0; wins[j] = 0; }

    while (now() < deadline) {
        if (goal > MAXN - 1000) goal = MAXN - 1000;
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(KMAX);
        } else {
            double bestv = -1.0;
            k = 1;
            for (int j = 1; j <= KMAX; j++) {
                double v = (wins[j] + 1.0) / (trials[j] + 2.0) + 0.02 * rnd01();
                if (v > bestv) { bestv = v; k = j; }
            }
        }
        int target = (int)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) {
            goal = fmax((double)best_N * 1.02, goal * 0.99);
            continue;
        }
        int G = m * k2;
        long N = 2L * k * G;
        if (G > MAXG || N > MAXN || N <= best_N) {
            if (goal < (double)best_N * 1.02) goal = (double)best_N * 1.02;
            if (N > MAXN) goal *= 0.99;
            continue;
        }
        trials[k]++;
        random_lift(&cur, k, G, m, k2, r);
        int ok = anneal(&cur, ITERS, PATIENCE, deadline);
        if (ok) {
            wins[k]++;
            best = cur;
            have = 1;
            best_N = N;
            if (goal < (double)N * 1.04) goal = (double)N * 1.04;
        } else {
            goal = fmax((double)best_N * 1.02, goal * 0.99);
        }
    }

    if (have) {
        build_all(&best);
        long c = compute_reach(&best) + PEN * dupcount(&best);
        if (c == 0) {
            print_lift(&best);
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


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

    # C bi-Cayley lift search over the remaining budget. It only returns graphs
    # strictly larger than best_n, and each one is re-checked here.
    remaining = final - time.monotonic()
    if remaining > 2.0 and d <= 64:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.0, 2), best_n],
                             timeout=remaining + 10)
            n, edges = lib.parse_graph_text(text)
            if n > 0:
                consider(n, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
