"""Bi-Cayley voltage-lift search over semidirect groups Z_m x| Z_k2, with the annealing done in C.

Each candidate is a lift of a 2k-block base graph by G = m*k2 (k blocks per side). Layer l pairs A-block i
with B-block layers[l][i] through voltage s: A_{i,g} ~ B_{p, g*s}. Every layer is a perfect matching between
blocks, so the lift is d-regular when there are no duplicate darts. The C engine anneals layer permutations
and voltages to make the diameter at most D, then prints the graph. Python ratchets the target order upward,
validates every output with lib.is_valid, and keeps the best of the exact constructions as a fallback.
"""
import math
import random
import time

import lib


C_LIFT = r'''
/* Bi-Cayley lift annealer.
 * Usage: prog d D K M K2 R seed time_limit
 * Group: Z_M x| Z_K2 with element a*K2+b, (a,b)(c,e) = (a + R^b c, b + e); needs R^K2 = 1 mod M.
 * Base: K blocks per side, G = M*K2, N = 2*K*G. A-block i, layer l pairs with B-block LAY[l][i]
 * through voltage S[l][i]: A_{i,g} ~ B_{p, g*s}. Output "N m" and the edges, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXG 16384
#define MAXK 32
#define MAXL 40
#define PEN 100L
#define T0 30.0
#define T1 0.3

static int d, D, K, G, M, K2, R;
static int POWR[MAXG];
static int LAY[MAXL][MAXK];
static int S[MAXL][MAXK];
static int nbr[MAXL][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN];
static uint64_t *cur = bufA;
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

static void init_group(void) {
    POWR[0] = 1 % M;
    for (int t = 1; t < K2; t++) POWR[t] = (int)((long)POWR[t - 1] * R % M);
}

static int gmul(int x, int y) {
    int a1 = x / K2, b1 = x - a1 * K2;
    int a2 = y / K2, b2 = y - a2 * K2;
    long a = ((long)a1 + (long)POWR[b1] * a2) % M;
    int b = (b1 + b2) % K2;
    return (int)a * K2 + b;
}

/* Fill both endpoints of every dart of layer l. */
static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int p = LAY[l][i], s = S[l][i];
        for (int g = 0; g < G; g++) {
            int A = i * G + g;
            int B = (K + p) * G + gmul(g, s);
            nbr[l][A] = B;
            nbr[l][B] = A;
        }
    }
}

/* Number of pairs of darts that coincide (same block pair and voltage in the same block). */
static long dup_count(void) {
    int tot = d * K;
    long c = 0;
    for (int a = 0; a < tot; a++) {
        int la = a / K, ia = a % K;
        for (int b = a + 1; b < tot; b++) {
            int lb = b / K, ib = b % K;
            if (ia == ib && LAY[la][ia] == LAY[lb][ib] && S[la][ia] == S[lb][ib]) c++;
        }
    }
    return c;
}

/* Sum over vertices of the number of block representatives NOT within distance D. */
static long reach_cost(void) {
    int N = 2 * K * G;
    uint64_t *c = bufA, *x = bufB;
    for (int v = 0; v < N; v++) c[v] = 0;
    for (int b = 0; b < 2 * K; b++) c[(long)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t y = c[v];
            for (int l = 0; l < d; l++) y |= c[nbr[l][v]];
            x[v] = y;
            changed |= (y != c[v]);
        }
        uint64_t *t = c;
        c = x;
        x = t;
        if (!changed) break;
    }
    cur = c;
    long un = 0;
    for (int v = 0; v < N; v++) un += 2 * K - __builtin_popcountll(c[v]);
    return un;
}

static long total_cost(void) { return reach_cost() + PEN * dup_count(); }

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) LAY[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = LAY[l][i];
            LAY[l][i] = LAY[l][j];
            LAY[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        rebuild_layer(l);
    }
}

/* One annealing run. Returns 1 when cost reaches 0 (state is valid), 0 on time-out. */
static int anneal(double run_len, double hard) {
    random_init();
    long cost = total_cost();
    int N = 2 * K * G;
    uint64_t fullm = (2 * K == 64) ? ~0ULL : ((1ULL << (2 * K)) - 1);
    double t0 = now(), temp = T0;
    long it = 0;
    while (cost != 0) {
        if ((it & 127) == 0) {
            double nt = now();
            if (nt - t0 > run_len || nt > hard) return 0;
            temp = T0 * pow(T1 / T0, (nt - t0) / run_len);
        }
        it++;
        if (K >= 2 && rndint(100) < 25) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = LAY[l][i1];
            LAY[l][i1] = LAY[l][i2];
            LAY[l][i2] = t;
            rebuild_layer(l);
            long nc = total_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
                cost = nc;
            } else {
                t = LAY[l][i1];
                LAY[l][i1] = LAY[l][i2];
                LAY[l][i2] = t;
                rebuild_layer(l);
            }
        } else {
            /* Voltage move, aimed at a vertex that is still too far from some block. */
            int l = rndint(d), i = -1, v = -1;
            for (int tries = 0; tries < 30; tries++) {
                int w = rndint(N);
                if (cur[w] != fullm) { v = w; break; }
            }
            if (v >= 0) {
                int blk = v / G;
                if (blk < K) {
                    i = blk;
                } else {
                    for (int q = 0; q < K; q++)
                        if (LAY[l][q] == blk - K) { i = q; break; }
                }
            }
            if (i < 0) i = rndint(K);
            int old = S[l][i], nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            rebuild_layer(l);
            long nc = total_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
                cost = nc;
            } else {
                S[l][i] = old;
                rebuild_layer(l);
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D K M K2 R seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    R = atoi(argv[6]);
    long seed = atol(argv[7]);
    double limit = atof(argv[8]);
    if (d < 2 || d > MAXL || D < 2 || K < 1 || K > MAXK || 2 * K > 64 ||
        M < 2 || K2 < 1 || R < 0 || R >= M) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (G > MAXG || 2L * K * G > MAXN) {
        printf("0 0\n");
        return 0;
    }
    long p = 1 % M;
    for (int t = 0; t < K2; t++) p = p * R % M;
    if (p != 1 % M) {
        printf("0 0\n");
        return 0;
    }
    init_group();
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double deadline = now() + limit * 0.9 - 0.2;
    int ok = 0;
    while (!ok && now() < deadline) {
        double rem = deadline - now();
        double run = rem * 0.5;
        if (run < 0.5) run = rem;
        ok = anneal(run, deadline);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    int N = 2 * K * G;
    printf("%d %ld\n", N, (long)K * G * d);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[l][v]);
    return 0;
}
'''


_MAXN_PY = 16384


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pick_r(m, k2, rng):
    """Return r with gcd(r, m) = 1 and r^k2 = 1 mod m (r = 1 always works)."""
    if k2 == 1 or m < 3:
        return 1
    for _ in range(300):
        r = rng.randrange(2, m)
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return r
    return 1


def _lift_candidates(goal, rng, count):
    """Sorted list of (N, k, m, k2, r) with N = 2*k*m*k2 >= goal and N within the C limit."""
    seen = {}
    for _ in range(40 * count):
        if len(seen) >= count:
            break
        k = rng.choice((1, 2, 3, 4, 5, 6, 8))
        k2 = rng.choice((1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12))
        need = -(-goal // (2 * k))
        m = max(2, -(-need // k2)) + rng.randrange(0, 3)
        N = 2 * k * m * k2
        if N < goal or N > _MAXN_PY:
            continue
        r = _pick_r(m, k2, rng)
        seen[(N, k, m, k2, r)] = True
    return sorted(seen)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.88 * time_limit - 2.0)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration cases return immediately).
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

    # Lift search: ratchet the target order upward after each success.
    if d >= 3 and D >= 3:
        slice_s = 4.0
        goal = max(best_n + 1, int(0.19 * lib.moore_bound(d, D)))
        step = 0
        while final - time.monotonic() > 3.0:
            cands = _lift_candidates(goal, rng, 3)
            found = False
            for N, k, m, k2, r in cands:
                left = final - time.monotonic()
                if left < 3.0:
                    break
                step += 1
                sl = min(slice_s, left - 1.0)
                try:
                    text = lib.run_c(C_LIFT, [d, D, k, m, k2, r, seed * 7919 + step, round(sl, 2)],
                                     timeout=sl + 10.0)
                    n_out, edges = lib.parse_graph_text(text)
                except Exception:
                    continue
                if n_out > best_n and lib.is_valid(n_out, edges, d, D):
                    best, best_n = (n_out, edges), n_out
                    found = True
                    goal = best_n + max(1, best_n // 200)
                    break
            if not found:
                goal = max(best_n + 1, int(goal * 0.995))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
