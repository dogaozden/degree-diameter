"""Bi-Cayley lift search in C over semidirect groups Z_m x| Z_k2, with a Python fallback chain.

Changes from the parent: the grow-by-two Python/C stage is replaced by a C annealer that searches
voltage lifts over many base sizes k and many groups, with incremental group tables and a
bitmask reachability cost. Exact constructions (projective planes, Araujo-Pardo-Lopez, W(q))
are still built first. K_{d,d} is the fallback, and every returned graph is checked with lib.is_valid.
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
#define MAXE 300000
#define PEN 1000

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

/* Group Z_M x| Z_K2, element (a,b) coded as a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int M, K2, RR, G;
static int PW[64];

static void set_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    RR = r;
    G = m * k2;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        PW[b] = (int)p;
        p = p * r % m;
    }
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int aa = (int)((a + (long)PW[b] * c) % M);
    return aa * K2 + (b + e) % K2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int c = (int)(((long)(M - a) % M) * PW[nb] % M);
    return c * K2 + nb;
}

static const int K2LIST[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmod(long b, int e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int sample_group(int target) {
    for (int tr = 0; tr < 300; tr++) {
        int k2 = K2LIST[rndint(20)];
        int m = (target + k2 - 1) / k2 + rndint(3);
        if (m < 2) m = 2;
        if (k2 == 1) {
            set_group(m, 1, 1);
            return 1;
        }
        if (m < 3) continue;
        for (int t2 = 0; t2 < 200; t2++) {
            int c = (t2 == 0 && k2 == 2) ? m - 1 : 2 + rndint(m - 2);
            if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                set_group(m, k2, c);
                return 1;
            }
        }
    }
    return 0;
}

/* Lift state: K A-blocks and K B-blocks, d layers, each layer a bijection A-block -> B-block. */
static int K;
static int layers[MAXD][MAXK];
static int Sv[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t Rcur[MAXN], Rnew[MAXN];
static uint32_t bufA[MAXN], bufB[MAXN];

static int bestE[2 * MAXE];
static int sol_m = 0, sol_N = 0;

static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = layers[l][i], s = Sv[l][i], si = ginv(s);
        int ra = i * G, rb = (K + j) * G;
        for (int g = 0; g < G; g++) {
            nbr[l][ra + g] = rb + gmul(g, s);
            nbr[l][rb + g] = ra + gmul(g, si);
        }
    }
}

/* out[u] = bitmask of block representatives within distance D of u; returns unreached count. */
static long compute_reach(uint32_t *out) {
    int N = 2 * K * G, full = 2 * K;
    uint32_t *cur = bufA, *nxt = bufB;
    for (int u = 0; u < N; u++) cur[u] = 0;
    for (int b = 0; b < full; b++) cur[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int u = 0; u < N; u++) {
            uint32_t x = cur[u];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][u]];
            nxt[u] = x;
            changed |= (x != cur[u]);
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int u = 0; u < N; u++) {
        out[u] = cur[u];
        unr += full - __builtin_popcount(cur[u]);
    }
    return unr;
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (layers[l][i] == layers[l2][i] && Sv[l][i] == Sv[l2][i]) c++;
    return c;
}

static long total_cost(uint32_t *R) {
    return compute_reach(R) + (long)PEN * dupcount();
}

static int anneal(double deadline, long max_iters, long patience) {
    int N = 2 * K * G, full = (1 << (2 * K)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layers[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < K; i++) Sv[l][i] = rndint(G);
        rebuild_layer(l);
    }
    long cost = total_cost(Rcur);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long last = 0, best = cost;
    for (long it = 0; it < max_iters; it++) {
        if (cost == 0) return 1;
        if ((it & 31) == 0 && now() > deadline) return 0;
        if (it - last > patience) return 0;
        double temp = 0.01 * c0 * (1.0 - (double)it / (double)max_iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = t;
            rebuild_layer(l);
            long c2 = total_cost(Rnew);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(Rcur, Rnew, sizeof(uint32_t) * N);
            } else {
                t = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = t;
                rebuild_layer(l);
            }
        } else {
            int l = 0, i = 0, u = -1;
            if (rnd01() < 0.4) {
                for (int tr = 0; tr < 30; tr++) {
                    int c = rndint(N);
                    if (Rcur[c] != (uint32_t)full) {
                        u = c;
                        break;
                    }
                }
            }
            if (u >= 0) {
                int blk = u / G;
                l = rndint(d);
                if (blk < K) {
                    i = blk;
                } else {
                    int j = blk - K;
                    i = 0;
                    for (int ii = 0; ii < K; ii++)
                        if (layers[l][ii] == j) {
                            i = ii;
                            break;
                        }
                }
            } else {
                l = rndint(d);
                i = rndint(K);
            }
            int old = Sv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            Sv[l][i] = nw;
            rebuild_layer(l);
            long c2 = total_cost(Rnew);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(Rcur, Rnew, sizeof(uint32_t) * N);
            } else {
                Sv[l][i] = old;
                rebuild_layer(l);
            }
        }
        if (cost < best) {
            best = cost;
            last = it;
        }
    }
    return cost == 0;
}

static void save_solution(void) {
    int N = 2 * K * G, A = K * G, cnt = 0;
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++) {
            if (cnt >= MAXE) break;
            bestE[2 * cnt] = u;
            bestE[2 * cnt + 1] = nbr[l][u];
            cnt++;
        }
    sol_m = cnt;
    sol_N = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_order]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long target = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    double deadline = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    long bestN = target;
    double goal = (double)target * 1.02 + 2.0;
    int trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) {
        trials[k] = 0;
        wins[k] = 0;
    }

    while (now() < deadline) {
        int k = 1;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            for (int kk = 1; kk <= MAXK; kk++) {
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    k = kk;
                }
            }
        }
        long Gmin = (long)((goal + 2.0 * k - 1.0) / (2.0 * k));
        if (Gmin < 2) Gmin = 2;
        long tgt = Gmin + rndint(3);
        if (tgt > (long)MAXN / (2 * k)) tgt = (long)MAXN / (2 * k);
        if (tgt < 2) tgt = 2;
        if (!sample_group((int)tgt)) {
            goal = 0.5 * (goal + bestN * 1.01 + 1.0);
            continue;
        }
        K = k;
        if (2 * K * G > MAXN) {
            goal = 0.5 * (goal + bestN * 1.01 + 1.0);
            continue;
        }
        trials[k]++;
        double rem = deadline - now();
        if (rem < 0.2) break;
        double slice = rem < 6.0 ? rem : 6.0;
        int ok = anneal(now() + slice, 20000, 3000);
        if (ok) {
            wins[k]++;
            long N = 2L * K * G;
            if (N > bestN) {
                bestN = N;
                save_solution();
            }
            goal = (double)N * 1.03 + 2.0;
            if (goal < bestN * 1.01 + 1.0) goal = bestN * 1.01 + 1.0;
        } else {
            double back = bestN * 1.01 + 1.0;
            goal = 0.5 * (goal + back);
            if (goal < back) goal = back;
        }
    }

    if (sol_m > 0) {
        printf("%d %d\n", sol_N, sol_m);
        for (int e = 0; e < sol_m; e++) printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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

    # Main search: C bi-Cayley voltage-lift annealer over semidirect groups.
    remaining = final - time.monotonic() - 1.0
    if D >= 3 and d >= 2 and remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
