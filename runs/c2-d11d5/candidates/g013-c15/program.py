"""Cayley bipartite-double search for the weakest targets (d=11, D=5).

Construction: for a finite group G of order g and a set S of d distinct elements, the bipartite
double of the Cayley digraph has vertices (x,0), (x,1) for x in G, with edges (x,0)-(x*s,1) for s in S.
It is d-regular and bipartite, and left multiplication is an automorphism. So diameter <= D holds iff
BFS from (e,0) reaches every vertex within D and BFS from (e,1) reaches every side-1 vertex within D.
The order is 2|G|. C simulated annealing searches S over semidirect products Z_m x| Z_k.

Safety: K_{d,d}, Projective-plane and Araujo-Pardo-Lopez constructions are kept as fallbacks.
Every returned graph passes lib.is_valid.
"""
import math
import random
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

/* Cayley bipartite double search.
 * Group: Z_M x|_R Z_K, element (a,b) coded as a*K+b, (a,b)(c,e) = (a + R^b c, b + e).
 * Graph: vertex (g,0) = g, (g,1) = G+g; edges (g,0)-(g*s,1) for s in S, |S| = d.
 * Diameter <= D iff BFS from (e,0) reaches all states within D, and BFS from (e,1)
 * reaches all side-1 states within D.
 * Simulated annealing over S minimises the count of unreached pairs.
 * usage: prog d D seed time_limit M K R
 */

#define MAXG 20000
#define MAXD 32
#define STALL 20000

static int d, D, G, M, K, R;
static int RP[MAXG];
static int S[MAXD], IS[MAXD];
static int Rt[MAXD][MAXG], Ri[MAXD][MAXG];
static int dist[2 * MAXG], qu[2 * MAXG];
static uint64_t rs = 88172645463325252ULL;
static double t_end;

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

static int mulf(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    long t = (long)RP[b] * c % M;
    int v = (int)(((long)a + t) % M);
    return v * K + (b + e) % K;
}

static int invf(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    long na = ((long)(M - RP[nb]) % M) * a % M;
    return (int)na * K + nb;
}

static void set_col(int s) {
    IS[s] = invf(S[s]);
    for (int x = 0; x < G; x++) {
        Rt[s][x] = mulf(x, S[s]);
        Ri[s][x] = mulf(x, IS[s]);
    }
}

static int in_set(int x) {
    for (int t = 0; t < d; t++)
        if (S[t] == x) return 1;
    return 0;
}

static void randomize(void) {
    for (int s = 0; s < d; s++) {
        int x, ok;
        do {
            x = rndint(G);
            ok = 1;
            for (int t = 0; t < s; t++)
                if (S[t] == x) { ok = 0; break; }
        } while (!ok);
        S[s] = x;
        set_col(s);
    }
}

static long eval_cost(void) {
    long unreached = 0;
    int NS = 2 * G;
    for (int src = 0; src < 2; src++) {
        for (int i = 0; i < NS; i++) dist[i] = -1;
        int start = src * G;
        int head = 0, tail = 0;
        dist[start] = 0;
        qu[tail++] = start;
        while (head < tail) {
            int u = qu[head++];
            if (dist[u] >= D) continue;
            int nd = dist[u] + 1;
            if (u < G) {
                for (int s = 0; s < d; s++) {
                    int v = G + Rt[s][u];
                    if (dist[v] < 0) { dist[v] = nd; qu[tail++] = v; }
                }
            } else {
                int x = u - G;
                for (int s = 0; s < d; s++) {
                    int v = Ri[s][x];
                    if (dist[v] < 0) { dist[v] = nd; qu[tail++] = v; }
                }
            }
        }
        if (src == 0) {
            unreached += NS - tail;
        } else {
            int r1 = 0;
            for (int i = 0; i < tail; i++)
                if (qu[i] >= G) r1++;
            unreached += G - r1;
        }
    }
    return unreached;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: %s d D seed time M K R\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    M = atoi(argv[5]);
    K = atoi(argv[6]);
    R = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit;
    if (d < 1 || d > MAXD || D < 2 || M < 1 || K < 1) { printf("0 0\n"); return 0; }
    long Gl = (long)M * K;
    if (Gl > MAXG || Gl <= d) { printf("0 0\n"); return 0; }
    G = (int)Gl;

    int Rm = R % M;
    RP[0] = 1 % M;
    for (int t = 1; t < K; t++) RP[t] = (int)((long)RP[t - 1] * Rm % M);
    if ((long)RP[K - 1] * Rm % M != 1 % M) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    randomize();
    long cost = eval_cost();
    long best = cost, stall = 0, it = 0;
    const double Temp = 0.7;
    while (cost > 0) {
        if ((it & 31) == 0 && now() > t_end) break;
        it++;
        int i = rndint(d);
        int old = S[i];
        int x;
        do { x = rndint(G); } while (in_set(x));
        S[i] = x;
        set_col(i);
        long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Temp)) {
            cost = c2;
            if (cost < best) { best = cost; stall = 0; }
            else stall++;
        } else {
            S[i] = old;
            set_col(i);
            stall++;
        }
        if (stall > STALL) {
            randomize();
            cost = eval_cost();
            best = cost;
            stall = 0;
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    printf("%d %ld\n", 2 * G, (long)G * d);
    for (int x = 0; x < G; x++)
        for (int s = 0; s < d; s++)
            printf("%d %d\n", x, G + Rt[s][x]);
    return 0;
}
'''


_HINT = {(11, 5): 5850}  # record orders used only to set the starting group size


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_options(G, rng):
    """Semidirect parameters (m, k, r) with m*k = G, always including the cyclic group."""
    opts = [(G, 1, 1)]
    for k in range(2, min(G, 60) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        cands = {1}  # direct product Z_m x Z_k
        if k == 2 and m > 2:
            cands.add(m - 1)
        if m > 2:
            for _ in range(30):
                r = rng.randrange(2, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cands.add(r)
        for r in cands:
            opts.append((m, k, r))
    return opts


def _pick_group(T, rng):
    """Return (G, (m, k, r)) with G >= T, preferring non-abelian groups."""
    first = None
    for G in range(T, T + 300):
        opts = _group_options(G, rng)
        nonab = [o for o in opts if o[1] > 1]
        if nonab and rng.random() < 0.85:
            return G, rng.choice(nonab)
        if first is None:
            first = (G, rng.choice(opts))
    return first


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    # K_{d,d} is optimal for bipartite diameter 2; the Cayley search needs d <= 32 (C limit).
    if D == 2 or d < 2 or d > 32:
        return best

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Group order needed to beat the current best: |V| = 2|G|.
    rec_T = max(best_n, _HINT.get((d, D), best_n + best_n // 20)) // 2 + 1
    T = rec_T
    lo = 0
    attempt = 0
    while True:
        remaining = final - time.monotonic()
        if remaining < 3.0:
            break
        if lo and T <= lo:
            T = lo + 1
        G, (m, k, r) = _pick_group(max(2, T), rng)
        slice_s = min(remaining - 1.5, max(3.0, remaining / 4.0))
        attempt += 1
        n, e = 0, []
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 1000 + attempt, round(slice_s, 2), m, k, r],
                             timeout=slice_s + 8.0)
            n, e = lib.parse_graph_text(text)
        except Exception:
            n = 0
        if n > 0 and lib.is_valid(n, e, d, D):
            consider(n, e)
            lo = max(lo, n // 2)
            if lo >= rec_T:
                T = lo + max(1, lo // 60)
            else:
                T = (lo + rec_T) // 2 + 1
        elif lo == 0:
            T = max(2, int(T * 0.8))
        else:
            T = (lo + T) // 2 + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
