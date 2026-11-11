"""Bi-Cayley lifts over small non-abelian groups, searched in C.

Construction: for a group G of order N and a set S of d elements containing the
identity, let A_g ~ B_{g*s} for s in S. This is a bipartite d-regular graph on 2N
vertices. Left translation is an automorphism, so the diameter condition reduces to
three covering conditions in G (with T = S S^-1, U = S^-1 S, a = D//2, b = (D-1)//2):

    T^{<=a} = G   (A-A distances),
    U^{<=a} = G   (B-B distances),
    S U^{<=b} = G (A-B distances).

The search is a simulated annealing over S in C, one call per group Z_m x| Z_k.
The group order N is grown by galloping from the K_{d,d} fallback. Every accepted
graph is re-checked with lib.is_valid, and K_{d,d} (or an exact construction) is
kept as the fallback.
"""
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
/* Bi-Cayley set-covering search over the group Z_m x|_r Z_k (order N = m*k).
 * Usage: prog d D m k r seed time_limit
 * Prints "ok s_0 ... s_{d-1}" (a valid S, s_0 = 0) or "none".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64
#define MAXG 4096
#define STALL 3000
#define TEMP 0.7

static int N, d, Da, Db;
static int *M, *INV;
static int stampc = 0;
static int mark[MAXG];
static int Tg[MAXG], Ug[MAXG], res1[MAXG], res2[MAXG], tmpb[MAXG];
static int ident[1] = {0};
static double t_end;
static uint64_t rs;

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

static int inS(const int *S, int cnt, int x) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Set product X * Y = { x*y }, written to out (distinct entries). Returns size. */
static int prod(const int *X, int nx, const int *Y, int ny, int *out) {
    int cnt = 0;
    if (++stampc == 0x7fffffff) {
        memset(mark, 0, sizeof(mark));
        stampc = 1;
    }
    for (int i = 0; i < nx; i++) {
        const int *row = M + (size_t)X[i] * N;
        for (int j = 0; j < ny; j++) {
            int z = row[Y[j]];
            if (mark[z] != stampc) {
                mark[z] = stampc;
                out[cnt++] = z;
            }
        }
    }
    return cnt;
}

/* res = init * gen^reps (as set products). Returns size of res. */
static int iterate(const int *init, int ninit, const int *gen, int ng, int reps, int *res) {
    if (reps <= 0) {
        memcpy(res, init, sizeof(int) * ninit);
        return ninit;
    }
    int cnt = prod(init, ninit, gen, ng, res);
    for (int r = 1; r < reps; r++) {
        int c2 = prod(res, cnt, gen, ng, tmpb);
        memcpy(res, tmpb, sizeof(int) * c2);
        cnt = c2;
    }
    return cnt;
}

/* Number of uncovered group elements over the three conditions (0 = valid). */
static int cost(const int *S, const int *Sinv) {
    int nT = prod(S, d, Sinv, d, Tg);
    int nU = prod(Sinv, d, S, d, Ug);
    int ca = iterate(ident, 1, Tg, nT, Da, res1);
    int cu = iterate(ident, 1, Ug, nU, Da, res2);
    int cb = iterate(S, d, Ug, nU, Db, res1);
    return (N - ca) + (N - cu) + (N - cb);
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: %s d D m k r seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    int m = atoi(argv[3]);
    int k = atoi(argv[4]);
    int r = atoi(argv[5]);
    long seed = atol(argv[6]);
    double limit = atof(argv[7]);
    if (d < 2 || d > MAXD || D < 2 || m < 1 || k < 1) {
        printf("none\n");
        return 0;
    }
    N = m * k;
    if (N < d || N > MAXG) {
        printf("none\n");
        return 0;
    }
    Da = D / 2;
    Db = (D - 1) / 2;

    rs = 88172645463325252ULL ^ ((uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL);
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int *rp = malloc(sizeof(int) * (size_t)k);
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);

    M = malloc(sizeof(int) * (size_t)N * N);
    INV = malloc(sizeof(int) * (size_t)N);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int a2 = y / k, b2 = y % k;
            M[(size_t)x * N + y] = (int)(((a1 + (long)rp[b1] * a2) % m) * k + (b1 + b2) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (M[(size_t)x * N + y] == 0) {
                INV[x] = y;
                break;
            }
    }
    free(rp);

    t_end = now() + limit;
    int S[MAXD], Sinv[MAXD];
    while (now() < t_end) {
        S[0] = 0;
        for (int i = 1; i < d; i++) {
            int x;
            do {
                x = rndint(N);
            } while (inS(S, i, x));
            S[i] = x;
        }
        for (int i = 0; i < d; i++) Sinv[i] = INV[S[i]];
        int c = cost(S, Sinv);
        int stall = 0;
        for (long it = 0; c > 0; it++) {
            if ((it & 127) == 0 && now() >= t_end) break;
            if (stall > STALL) break;
            int i = 1 + rndint(d - 1);
            int x = rndint(N);
            if (inS(S, d, x)) continue;
            int old = S[i];
            S[i] = x;
            Sinv[i] = INV[x];
            int c2 = cost(S, Sinv);
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / TEMP)) {
                if (c2 < c) stall = 0;
                else stall++;
                c = c2;
            } else {
                S[i] = old;
                Sinv[i] = INV[old];
                stall++;
            }
        }
        if (c == 0) {
            printf("ok");
            for (int i = 0; i < d; i++) printf(" %d", S[i]);
            printf("\n");
            free(M);
            free(INV);
            return 0;
        }
    }
    printf("none\n");
    free(M);
    free(INV);
    return 0;
}
'''


def _group_candidates(N):
    """All (m, k, r) with Z_m x|_r Z_k of order N (cyclic when r = 1)."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, k, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _graph_from(N, m, k, r, S, d):
    """Bi-Cayley graph: A_g = g, B_h = N + h, A_g ~ B_{g*s} for s in S."""
    rp = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    s = np.array(S, dtype=np.int64)
    sa = a[s]
    sb = b[s]
    P = ((a[:, None] + rp[b][:, None] * sa[None, :]) % m) * k + (b[:, None] + sb[None, :]) % k
    edges = [(g, N + h) for g, row in enumerate(P.tolist()) for h in row]
    return 2 * N, edges


def _try_order(N, d, D, rng, budget):
    """Try a few groups of order N; return a valid (n, edges) or None."""
    cands = _group_candidates(N)
    if not cands:
        return None
    rng.shuffle(cands)
    cands = cands[:4]
    per = budget / len(cands)
    for m, k, r in cands:
        text = lib.run_c(C_SOURCE, [d, D, m, k, r, rng.randrange(1 << 30), round(per, 3)],
                         timeout=per + 15)
        parts = text.split()
        if len(parts) == d + 1 and parts[0] == "ok":
            S = [int(x) for x in parts[1:]]
            n, edges = _graph_from(N, m, k, r, S, d)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def _group_search(best, d, D, rng, end):
    """Gallop the group order N upward from the current best; keep only valid graphs."""
    moore = lib.moore_bound(d, D)
    cur = best[0] // 2
    step = max(1, cur // 8)
    fails = 0
    while True:
        remaining = end - time.monotonic()
        if remaining < 1.0:
            break
        N = cur + step
        if 2 * N > moore or N > 2000:
            if step == 1:
                break
            step = max(1, step // 2)
            continue
        budget = min(remaining - 0.5, 8.0 if step == 1 else 3.0)
        if budget < 0.5:
            break
        try:
            res = _try_order(N, d, D, rng, budget)
        except (RuntimeError, ValueError):
            res = None
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
            cur = N
            step *= 2
            fails = 0
        else:
            if step == 1:
                fails += 1
                if fails >= 3:
                    break
            step = max(1, step // 2)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    # Exact constructions (calibration case returns immediately).
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        pg = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(pg[0], pg[1], d, D):
            return pg
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            if ar[0] > best[0] and lib.is_valid(ar[0], ar[1], d, D):
                best = ar
        except (ValueError, RuntimeError):
            pass

    # Main search: bi-Cayley lifts over small non-abelian groups.
    if d >= 2 and D >= 2:
        try:
            best = _group_search(best, d, D, rng, end)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
