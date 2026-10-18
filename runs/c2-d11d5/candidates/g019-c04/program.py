"""Bi-Cayley voltage-lift search in C, over semidirect products Z_m x| Z_k2.

Python handles exact small constructions and validation. The C engine searches for lifts of
2k-block bi-Cayley graphs with simulated annealing on voltages and block permutations. Its cost
is the number of (vertex, block) pairs at distance > D, with a penalty for duplicate darts. Only
block representatives need checking, by left-transitivity. Every returned graph is re-checked
with lib.is_valid. K_{d,d} is the fallback.
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

#define MAXN 65536
#define MAXD 32
#define MAXK 32
#define GMAX 2500
#define NKS 7
#define PEN 1000L
#define ITERS 60000L
#define PATIENCE 10000L

static int d, D;
static double t_end;
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

/* Group Z_m x| Z_k2 with element a*k2+b, product (a,b)(c,e) = (a + r^b c, b + e). */
static int G, GM, GK, GR;
static int powr[64];
static uint16_t MUL[GMAX * GMAX];
static int INVT[GMAX];

static void build_group(int m, int k2, int r) {
    GM = m; GK = k2; GR = r; G = m * k2;
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long)powr[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            MUL[x * G + y] = (uint16_t)(((a + (long)powr[b] * c) % m) * k2 + (b + e) % k2);
        }
    }
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        int nb = (k2 - b) % k2;
        INVT[x] = (int)(((m - ((long)powr[nb] * a) % m) % m) * k2 + nb);
    }
}

static int sample_group(int target, int *om, int *ok, int *orr) {
    static const int K2[] = {1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12, 16, 20, 24};
    for (int t = 0; t < 200; t++) {
        int k2 = K2[rndint((int)(sizeof K2 / sizeof K2[0]))];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        m += rndint(3);
        if ((long)m * k2 > GMAX) continue;
        int r = 1;
        if (k2 > 1 && m > 2) {
            double u = rnd01();
            if (u < 0.3) {
                r = m - 1;
            } else if (u < 0.8) {
                for (int q = 0; q < 80; q++) {
                    int c = 2 + rndint(m - 2);
                    if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            }
        }
        if (gcd_i(r, m) != 1 || powmod(r, k2, m) != 1 % m) r = 1;
        *om = m; *ok = k2; *orr = r;
        return 1;
    }
    return 0;
}

/* Lift state. Vertices: A block i -> i*G+g, B block p -> (K+p)*G+h. */
static int K;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXN * MAXD];
static int bestnbr[MAXN * MAXD];
static uint64_t bufA[MAXN], bufB[MAXN];
static uint64_t *lastreach = bufA;
static int best_half = 0, best_N = 0, best_d = 0;

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i], is = INVT[s];
    int bi = i * G, bp = (K + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[(bi + g) * d + l] = bp + MUL[g * G + s];
        nbr[(bp + g) * d + l] = bi + MUL[g * G + is];
    }
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Sum over vertices of (2K - #block representatives within distance D). */
static long unreached(void) {
    int N = 2 * K * G;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nb[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    lastreach = cur;
    long c = 0;
    int full = 2 * K;
    for (int v = 0; v < N; v++) c += full - __builtin_popcountll(cur[v]);
    return c;
}

static long full_cost(void) { return unreached() + PEN * dupcount(); }

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layers[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i]; layers[l][i] = layers[l][j]; layers[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static long anneal(void) {
    int N = 2 * K * G;
    uint64_t fullm = (1ULL << (2 * K)) - 1;
    long cost = full_cost();
    long best = cost, last = 0;
    double c0 = (double)(cost > 0 ? cost : 1);
    for (long t = 0; t < ITERS && cost > 0; t++) {
        if ((t & 63) == 0 && now() > t_end) break;
        if (t - last > PATIENCE) break;
        double frac = 1.0 - (double)t / (double)ITERS;
        double temp = 0.5 + 0.01 * c0 * frac;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long nc = full_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
                cost = nc;
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            if (rnd01() < 0.4) {
                int v = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int c = rndint(N);
                    if (lastreach[c] != fullm) { v = c; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    if (b < K) {
                        i = b;
                    } else {
                        int p = b - K;
                        for (int q = 0; q < K; q++)
                            if (layers[l][q] == p) { i = q; break; }
                    }
                }
            }
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            long nc = full_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
                cost = nc;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < best) { best = cost; last = t; }
    }
    return cost;
}

static void print_best(void) {
    if (best_N == 0) { printf("0 0\n"); return; }
    printf("%d %ld\n", best_N, (long)best_half * best_d);
    for (int v = 0; v < best_half; v++)
        for (int l = 0; l < best_d; l++)
            printf("%d %d\n", v, bestnbr[v * best_d + l]);
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
    long minn = argc > 5 ? atol(argv[5]) : 0;
    t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    static const int KS[NKS] = {2, 3, 4, 5, 6, 8, 10};
    static long trials[NKS], wins[NKS];
    long mb = moore_bound();
    double goal = (double)minn * 1.02;
    if (goal < 0.2 * (double)mb) goal = 0.2 * (double)mb;
    if (goal > (double)mb) goal = (double)mb;
    long bestn = minn;

    while (now() < t_end - 0.5) {
        int ki;
        if (rnd01() < 0.2) {
            ki = rndint(NKS);
        } else {
            double bv = -1.0;
            ki = 0;
            for (int j = 0; j < NKS; j++) {
                double v = (wins[j] + 1.0) / (trials[j] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; ki = j; }
            }
        }
        K = KS[ki];
        long target = (long)(goal / (2.0 * K)) + rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group((int)target, &m, &k2, &r)) {
            goal = fmax((double)bestn * 1.02, goal * 0.98);
            continue;
        }
        build_group(m, k2, r);
        long N = 2L * K * G;
        if (N > MAXN) { goal = fmax((double)bestn * 1.02, goal * 0.98); continue; }
        if (N <= bestn) { goal = fmax(goal, (double)bestn * 1.02); continue; }

        trials[ki]++;
        random_state();
        long c = anneal();
        if (c == 0 && dupcount() == 0) {
            wins[ki]++;
            bestn = N;
            best_N = (int)N;
            best_half = K * G;
            best_d = d;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)N * d);
            goal = (double)N * 1.03;
        } else {
            goal = fmax((double)bestn * 1.02, goal * 0.98);
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact small constructions.
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

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
    if D == 4 and time.monotonic() - t0 < time_limit * 0.3:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # C lift search over the remaining budget.
    budget = 0.85 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                             stdin_graph=None, timeout=budget + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
