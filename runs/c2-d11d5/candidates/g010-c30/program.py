"""Bold rewrite: a C bi-Cayley lift annealer replaces the Python/numpy search.

Construction: a voltage lift of a base bipartite graph with k vertices per side over a
semidirect product group Z_m x| Z_k2 (left-regular action, so every vertex of a block
is equivalent). Distances from the 2k block representatives therefore decide the whole
diameter, and a full all-pairs bitset check confirms every accepted graph before output.

Search: C simulated annealing over layer permutations and voltages, with targeted moves
at unreached (representative, vertex) pairs, a ratcheting order goal, and a bandit over
base sizes k. Safe fallbacks: K_{d,d}, cycles for d = 2, projective-plane and
Araujo-Lopez constructions where they apply. Every returned graph is checked with lib.is_valid.
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

#define MAXN 12288
#define MAXL 40
#define MAXK 6
#define NCAP 12000
#define PEN 200
#define ITERS 30000
#define PATIENCE 2500

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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}
static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ---- group Z_M x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
static int M_, K2, G;
static int pw[64];

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M_) * K2 + (b + e) % K2;
}
static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long t = (long)pw[nb] * a % M_;
    int na = (int)((M_ - t) % M_);
    return na * K2 + nb;
}

static int sample_group(int gt) {
    static const int K2s[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    int nk = (int)(sizeof K2s / sizeof K2s[0]);
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2s[rndint(nk)];
        int m = (gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        long r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int t = 0; t < 200 && !found; t++) {
                long c = (t == 0) ? (long)(m - 1) : (long)(1 + rndint(m - 1));
                if (gcd_l(c, m) == 1 && powmod_l(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                }
            }
            if (!found) continue;
        }
        M_ = m;
        K2 = k2;
        G = m * k2;
        long p = 1 % m;
        for (int b = 0; b < k2; b++) {
            pw[b] = (int)p;
            p = p * r % m;
        }
        return 1;
    }
    return 0;
}

/* ---- lift state: layer l pairs A_i with B_{lay[l][i]} via voltage sv[l][i] ---- */
static int K, N;
static int lay[MAXL][MAXK];
static int sv[MAXL][MAXK];
static int nbr[MAXL][MAXN];
static uint64_t rA[MAXN], rB[MAXN];

static int bestK = 0, bestG = 0, bestN = 0;
static int bestnbr[MAXL][MAXN];

static void set_dart(int l, int i) {
    int p = lay[l][i], s = sv[l][i];
    int ab = i * G, bb = (K + p) * G;
    int is = ginv(s);
    for (int g = 0; g < G; g++) {
        nbr[l][ab + g] = bb + gmul(g, s);
        nbr[l][bb + g] = ab + gmul(g, is);
    }
}

static void build_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static long dup_count(void) {
    long c = 0;
    int T = d * K;
    for (int a = 0; a < T; a++) {
        int la = a / K, ia = a % K;
        for (int b = a + 1; b < T; b++) {
            int lb = b / K, ib = b % K;
            if (ia == ib && lay[la][ia] == lay[lb][ib] && sv[la][ia] == sv[lb][ib]) c++;
        }
    }
    return c;
}

/* Unreached (representative, vertex) pairs; the result is left in rA. */
static long evaluate(void) {
    int reps = 2 * K;
    uint64_t *cur = rA, *nx = rB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < reps; b++) cur[b * G] |= 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nx[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nx;
        nx = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += reps - __builtin_popcountll(cur[v]);
    if (cur != rA) memcpy(rA, cur, sizeof(uint64_t) * (size_t)N);
    return unr;
}

/* All-pairs check on the actual graph, independent of the symmetry argument. */
static int verify_full(void) {
    int W = (N + 63) / 64;
    uint64_t *A = malloc(sizeof(uint64_t) * (size_t)N * W);
    uint64_t *B = malloc(sizeof(uint64_t) * (size_t)N * W);
    if (!A || !B) {
        free(A);
        free(B);
        return 0;
    }
    memset(A, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) A[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    uint64_t *cur = A, *nx = B;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nx + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int l = 0; l < d; l++) {
                const uint64_t *s = cur + (size_t)nbr[l][v] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nx;
        nx = t;
    }
    int ok = 1;
    for (int v = 0; v < N && ok; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        if (c != N) ok = 0;
    }
    free(A);
    free(B);
    return ok;
}

static int anneal(long maxit, long patience, double deadline) {
    uint64_t full = (1ULL << (2 * K)) - 1;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            lay[l][i] = perm[i];
            sv[l][i] = rndint(G);
        }
    }
    build_all();
    long cost = evaluate() + PEN * dup_count();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long last = 0, bestc = cost;

    for (long t = 0; t < maxit && cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double T = 0.01 * c0 * (1.0 - (double)t / (double)maxit);
        if (T < 0.3) T = 0.3;

        if (K >= 2 && rnd01() < 0.15) {
            int l = rndint(d);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = evaluate() + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                tmp = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = -1;
            if (rnd01() < 0.5) {
                int v = -1;
                for (int tr = 0; tr < 40; tr++) {
                    int c = rndint(N);
                    if (rA[c] != full) {
                        v = c;
                        break;
                    }
                }
                if (v >= 0) {
                    int u = v / G;
                    if (u < K) {
                        i = u;
                    } else {
                        for (int j = 0; j < K; j++) {
                            if (lay[l][j] == u - K) {
                                i = j;
                                break;
                            }
                        }
                    }
                }
            }
            if (i < 0) i = rndint(K);
            int old = sv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            set_dart(l, i);
            long c2 = evaluate() + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                sv[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = t;
        }
    }

    if (cost != 0) return 0;
    if (!verify_full()) return 0;
    for (int l = 0; l < d; l++) memcpy(bestnbr[l], nbr[l], sizeof(int) * (size_t)N);
    bestK = K;
    bestG = G;
    bestN = N;
    return 1;
}

static void print_kdd(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) printf("%d %d\n", i, d + j);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXL) {
        print_kdd();
        return 0;
    }
    bestN = 2 * d;
    bestK = 0;

    long trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) {
        trials[k] = 0;
        wins[k] = 0;
    }
    double goal = bestN * 1.1 + 2.0;

    while (now() < t_end) {
        int k;
        if (rnd01() < 0.3) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.05 * rnd01();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        if (goal > NCAP) goal = NCAP;
        int kmax = NCAP / (2 * k) - 30;
        int gt = (int)(goal / (2.0 * k)) + rndint(3);
        if (gt > kmax) gt = kmax;
        if (gt < 2) gt = 2;
        if (!sample_group(gt)) continue;
        int Nn = 2 * k * G;
        if (Nn > NCAP) continue;
        if (Nn <= bestN) {
            goal = bestN * 1.02 + 2.0;
            continue;
        }
        K = k;
        N = Nn;
        trials[k]++;
        int ok = anneal(ITERS, PATIENCE, t_end);
        double floor_ = bestN * 1.02 + 2.0;
        if (ok) {
            wins[k]++;
            goal = Nn * 1.04 + 2.0;
        } else {
            goal = floor_ + (goal - floor_) * 0.6;
            if (goal < floor_) goal = floor_;
        }
    }

    if (bestK == 0) {
        print_kdd();
        return 0;
    }
    int A = bestK * bestG;
    printf("%d %d\n", bestN, d * A);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, bestnbr[l][v]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (kept as strong starting points for other cases).
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


def _kdd(d):
    """K_{d,d}: diameter 2, always valid for D >= 2."""
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return _kdd(d)
    if D == 2:
        return _kdd(d)

    best = _kdd(d)
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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C bi-Cayley lift annealer using the remaining time.
    total = max(1.0, 0.85 * time_limit - 3.0)
    remaining = total - (time.monotonic() - t0)
    if remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=None, timeout=remaining + 4.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
