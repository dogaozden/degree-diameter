"""Bi-Cayley lift search in C with symmetry-reduced validation, plus exact fallbacks.

New idea: a lift over a group G acting regularly on each block is distance-transitive
within blocks, because left multiplication by G is an automorphism. So
dist((x,g),(y,h)) = dist((x,e),(y,g^-1 h)). Validity therefore reduces to checking
the 2K representative vertices (one per block), using one 2K-bit reach mask per vertex.
This makes each cost evaluation O(D * d * N) bit operations in C, with no all-pairs BFS.
The C engine anneals over layer permutations and voltages on semidirect products
Z_m x| Z_k2 and ratchets the order upward. Every output is re-checked with lib.is_valid,
and K_{d,d} or an exact projective-plane / Araujo-Pardo-Lopez graph is the fallback.
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

/* Usage: prog d D seed time_limit   (stdin ignored)
 * Output: "n m" then m edges "u v" of the best valid bi-Cayley lift found (or "0 0").
 *
 * Model: K base vertices per side, group G = Z_M x| Z_K2 (element a*K2+b, product
 * (a,b)(c,e) = (a + r^b c, b+e)). Layer l pairs A_i with B_{perm[l][i]} via voltage s:
 * A_{i,g} ~ B_{j, g*s}. Each layer is a perfect matching, so the graph is d-regular.
 * Cost = (block-rep, vertex) pairs at distance > D + 1000 * duplicate-edge count.
 */

#define MAXD 64
#define MAXK 4
#define MAXN 32768
#define PEN 1000

static int d, D, K, G, M, K2, R;
static int pw[64];
static int perm[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN], candR[MAXN], curR[MAXN];
static long bestN = 0;
static int bestK, bestG, bestM, bestK2, bestR;
static int bestPerm[MAXD][MAXK], bestVolt[MAXD][MAXK];
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

static long long pwmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void set_pw(void) {
    for (int b = 0; b < K2; b++) pw[b] = (int)pwmod(R, b, M);
}

static int mulg(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = (long long)a + (long long)pw[b] * c;
    int ra = (int)(t % M);
    return ra * K2 + (b + e) % K2;
}

/* Write layer l's matching for base vertex i (both directions). */
static void set_dart(int l, int i) {
    int j = perm[l][i], s = volt[l][i];
    for (int g = 0; g < G; g++) {
        int a = i * G + g;
        int b = (K + j) * G + mulg(g, s);
        nbr[l][a] = b;
        nbr[l][b] = a;
    }
}

static uint64_t *reach_calc(void) {
    int N = 2 * K * G;
    uint64_t *a = bufA, *b = bufB;
    memset(a, 0, sizeof(uint64_t) * (size_t)N);
    for (int bb = 0; bb < 2 * K; bb++) a[bb * G] = 1ULL << bb;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t x = a[v];
            for (int l = 0; l < d; l++) x |= a[nbr[l][v]];
            b[v] = x;
        }
        uint64_t *tmp = a;
        a = b;
        b = tmp;
    }
    return a;
}

/* Cost; the reach masks are left in candR. */
static long eval_cost(void) {
    int N = 2 * K * G;
    uint64_t *res = reach_calc();
    long unreached = 0;
    for (int v = 0; v < N; v++) {
        candR[v] = res[v];
        unreached += 2 * K - __builtin_popcountll(res[v]);
    }
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && volt[l1][i] == volt[l2][i]) dup++;
    return unreached + (long)PEN * dup;
}

static int accept(long nc, long cc, double T) {
    if (nc <= cc) return 1;
    return rnd01() < exp(-(double)(nc - cc) / T);
}

static const int K2LIST[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Pick Z_M x| Z_K2 with M*K2 >= Gmin and 2*K*G <= MAXN. Returns 1 on success. */
static int setup_group(int Gmin) {
    for (int attempt = 0; attempt < 200; attempt++) {
        int k2 = K2LIST[rndint(20)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1) {
            r = -1;
            if (m > 2) {
                for (int t = 0; t < 300; t++) {
                    int c = 2 + rndint(m - 2);
                    if (gcdl(c, m) == 1 && pwmod(c, k2, m) == 1 % m) {
                        r = c;
                        break;
                    }
                }
            }
            if (r < 0) continue;
        }
        M = m;
        K2 = k2;
        R = r;
        G = M * K2;
        if (2 * K * G > MAXN) continue;
        set_pw();
        return 1;
    }
    return 0;
}

static void random_config(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) volt[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Simulated annealing on the current (K, G) setting. Returns 1 if a valid lift was found. */
static int anneal(int iters) {
    int N = 2 * K * G;
    uint64_t full = (1ULL << (2 * K)) - 1;
    random_config();
    long cost = eval_cost();
    memcpy(curR, candR, sizeof(uint64_t) * (size_t)N);
    long c0 = cost, bestc = cost;
    int lastImp = 0;
    double T0 = 2.0 + 0.05 * (double)c0, T1 = 0.2;

    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > t_end) break;
        if (t - lastImp > 1500) break;
        double T = T0 * pow(T1 / T0, (double)t / iters);
        int l = rndint(d), i = rndint(K);

        /* Focus half the moves on a vertex that is still unreached. */
        if (rnd01() < 0.5) {
            int v = -1;
            for (int tr = 0; tr < 40; tr++) {
                int c = rndint(N);
                if (curR[c] != full) {
                    v = c;
                    break;
                }
            }
            if (v >= 0) {
                int blk = v / G;
                if (blk < K) {
                    i = blk;
                } else {
                    int j = blk - K;
                    for (int ii = 0; ii < K; ii++)
                        if (perm[l][ii] == j) {
                            i = ii;
                            break;
                        }
                }
            }
        }

        if (K >= 2 && rnd01() < 0.15) {
            int i2 = rndint(K - 1);
            if (i2 >= i) i2++;
            int p1 = perm[l][i], p2 = perm[l][i2];
            perm[l][i] = p2;
            perm[l][i2] = p1;
            set_dart(l, i);
            set_dart(l, i2);
            long nc = eval_cost();
            if (accept(nc, cost, T)) {
                cost = nc;
                memcpy(curR, candR, sizeof(uint64_t) * (size_t)N);
            } else {
                perm[l][i] = p1;
                perm[l][i2] = p2;
                set_dart(l, i);
                set_dart(l, i2);
            }
        } else {
            int old = volt[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            volt[l][i] = nv;
            set_dart(l, i);
            long nc = eval_cost();
            if (accept(nc, cost, T)) {
                cost = nc;
                memcpy(curR, candR, sizeof(uint64_t) * (size_t)N);
            } else {
                volt[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            lastImp = t;
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    t_end = now() + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    while (now() < t_end) {
        K = 1 + rndint(MAXK);
        long base = bestN > 2L * d ? bestN : 2L * d;
        long Gmin = base / (2 * K) + 1 + rndint(2);
        if (!setup_group((int)Gmin)) continue;
        if (anneal(3000)) {
            long N = 2L * K * G;
            if (N > bestN) {
                bestN = N;
                bestK = K;
                bestG = G;
                bestM = M;
                bestK2 = K2;
                bestR = R;
                memcpy(bestPerm, perm, sizeof(perm));
                memcpy(bestVolt, volt, sizeof(volt));
            }
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    K = bestK;
    G = bestG;
    M = bestM;
    K2 = bestK2;
    R = bestR;
    set_pw();
    memcpy(perm, bestPerm, sizeof(perm));
    memcpy(volt, bestVolt, sizeof(volt));
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
    printf("%ld %ld\n", bestN, (long)d * K * G);
    for (int l = 0; l < d; l++)
        for (int a = 0; a < K * G; a++) printf("%d %d\n", a, nbr[l][a]);
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

    # Fallback: K_{d,d}, diameter 2 and optimal for D = 2.
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

    # Main search: symmetry-reduced bi-Cayley lift annealing in C.
    budget = 0.85 * time_limit - 2.5 - (time.monotonic() - t0)
    if d >= 3 and D >= 3 and budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
