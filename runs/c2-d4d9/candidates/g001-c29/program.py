"""Bi-Cayley search: a different construction from the voltage-lift engine.

Vertices are two copies of a finite group G of order N: A-vertex x and B-vertex y
are adjacent iff x^{-1} y lies in a connection set S with |S| = d. G is a semidirect
product Z_m x| Z_k. Left multiplication is an automorphism that is transitive on each
side, so the diameter equals the larger of two BFS eccentricities (from A-identity and
from B-identity). Each candidate is therefore checked with two BFS passes, not a full
all-pairs check. Simulated annealing on S grows N one step at a time.

Safe fallback: K_{d,d}, or the known Python construction when it is larger. Every
returned graph is checked with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over semidirect groups Z_m x| Z_k.
 * Usage: prog d D seed time_limit   (stdin ignored)
 * Output: "n m" then edges, a valid d-regular bipartite graph of diameter <= D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define ITER 3000

static int d, D;
static double t_end;
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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
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

/* ---------------------------------------------------------------- group state */

static int gM, gK, gR;
static int *rp;           /* rp[b] = r^b mod m, b < k */
static int *vis, *qu;
static int stampv = 0;
static int Nn, dd;       /* current group order and degree */
static int *S, *Si;      /* connection set and its inverses */

static void set_group(int m, int k, int r) {
    gM = m; gK = k; gR = r;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

/* (a,b)(c,e) = (a + r^b c, b + e), element coded as a*k + b. */
static int gmul(int x, int y) {
    int a = x / gK, b = x % gK, c = y / gK, e = y % gK;
    return (int)(((long)a + (long)rp[b] * c) % gM) * gK + (b + e) % gK;
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(int x) {
    int a = x / gK, b = x % gK;
    int nb = (gK - b) % gK;
    long c = ((long)rp[nb] * a) % gM;
    c = (gM - c) % gM;
    return (int)c * gK + nb;
}

static int in_set(int v, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == v) return 1;
    return 0;
}

/* ---------------------------------------------------------------- evaluation */

/* BFS from src up to depth D on the bi-Cayley graph. Vertices 0..Nn-1 are A, Nn..2Nn-1 are B.
 * Returns the number of reached vertices; *cb = number of reached B vertices. */
static int bfs(int src, int *cb) {
    stampv++;
    int head = 0, tail = 0, level = 0;
    vis[src] = stampv;
    qu[tail++] = src;
    while (head < tail && level < D) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            if (v < Nn) {
                for (int i = 0; i < dd; i++) {
                    int u = Nn + gmul(v, S[i]);
                    if (vis[u] != stampv) { vis[u] = stampv; qu[tail++] = u; }
                }
            } else {
                int y = v - Nn;
                for (int i = 0; i < dd; i++) {
                    int u = gmul(y, Si[i]);
                    if (vis[u] != stampv) { vis[u] = stampv; qu[tail++] = u; }
                }
            }
        }
        level++;
    }
    int c = 0;
    for (int i = 0; i < tail; i++)
        if (qu[i] >= Nn) c++;
    *cb = c;
    return tail;
}

/* Zero iff the bi-Cayley graph has diameter <= D.
 * Left multiplication is transitive on each side, so two sources suffice:
 * every A-vertex must be within D of A-identity, and every B-vertex within D of B-identity. */
static long evalbad(void) {
    int cbA, cbB;
    int ta = bfs(0, &cbA);
    (void)cbA;
    bfs(Nn, &cbB);
    return (long)(2 * Nn - ta) + (long)(Nn - cbB);
}

/* ---------------------------------------------------------------- group choice */

static int divisors(int N, int *divs) {
    int nd = 0;
    for (int i = 1; (long)i * i <= N; i++)
        if (N % i == 0) {
            divs[nd++] = i;
            if (i != N / i) divs[nd++] = N / i;
        }
    return nd;
}

static void pick_group(int N, const int *divs, int nd, int *m, int *k, int *r) {
    for (int t = 0; t < 400; t++) {
        int mm = divs[rndint(nd)];
        int kk = N / mm;
        int rr = rndint(mm);
        if (gcd_i(rr, mm) != 1) continue;
        if (powmod_l(rr, kk, mm) != 1 % mm) continue;
        *m = mm; *k = kk; *r = rr;
        return;
    }
    *m = N; *k = 1; *r = 1 % N; /* cyclic fallback */
}

/* ---------------------------------------------------------------- search */

static int bestN, bestm, bestk, bestr;
static int *bestS;

/* Try to find a bi-Cayley graph on 2N vertices with diameter <= D. */
static int attempt(int N, double until) {
    static int divs[512];
    int nd = divisors(N, divs);
    while (now() < until) {
        int m, k, r;
        pick_group(N, divs, nd, &m, &k, &r);
        set_group(m, k, r);
        for (int i = 0; i < dd; i++) {
            int v;
            do { v = rndint(N); } while (in_set(v, i));
            S[i] = v;
            Si[i] = ginv(v);
        }
        long cur = evalbad();
        double T = 1.5;
        for (int it = 0; it < ITER && cur > 0; it++) {
            if ((it & 31) == 0 && now() > until) return 0;
            int i = rndint(dd);
            int old = S[i], oldi = Si[i];
            int nv;
            do { nv = rndint(N); } while (in_set(nv, dd));
            S[i] = nv;
            Si[i] = ginv(nv);
            long nb = evalbad();
            if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
                cur = nb;
            } else {
                S[i] = old;
                Si[i] = oldi;
            }
            T *= 0.999;
            if (T < 0.3) T = 0.3;
        }
        if (cur == 0) {
            bestN = N; bestm = m; bestk = k; bestr = r;
            memcpy(bestS, S, sizeof(int) * dd);
            return 1;
        }
    }
    return 0;
}

static void print_best(void) {
    int N = bestN;
    set_group(bestm, bestk, bestr);
    printf("%d %ld\n", 2 * N, (long)N * dd);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < dd; i++)
            printf("%d %d\n", x, N + gmul(x, bestS[i]));
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
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (d < 1) { printf("1 0\n"); return 0; }
    dd = d;

    long mb = moore_bound();
    long maxN = mb / 2;
    if (maxN > 1000000) maxN = 1000000;
    if (maxN < d) maxN = d;
    vis = calloc((size_t)(2 * maxN + 2), sizeof(int));
    qu = malloc(sizeof(int) * (size_t)(2 * maxN + 2));
    rp = malloc(sizeof(int) * (size_t)(maxN + 2));
    S = malloc(sizeof(int) * (size_t)d);
    Si = malloc(sizeof(int) * (size_t)d);
    bestS = malloc(sizeof(int) * (size_t)d);
    if (!vis || !qu || !rp || !S || !Si || !bestS) { printf("1 0\n"); return 0; }

    /* Safe start: K_{d,d} = bi-Cayley graph of Z_d with S = Z_d. */
    bestN = d; bestm = 1; bestk = d; bestr = 0;
    for (int i = 0; i < d; i++) bestS[i] = i;
    Nn = d;

    if (D >= 2 && d >= 2) {
        while (now() < t_end) {
            int target = bestN + 1;
            if (target > maxN) break;
            Nn = target;
            if (!attempt(target, t_end)) break;
            Nn = bestN;
        }
    }
    Nn = bestN;
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    # K_{d,d} is always valid for D >= 2 and is the safe fallback.
    best = start if start is not None else lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    if d >= 2 and D >= 2 and best[0] < lib.moore_bound(d, D):
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 5)
                out = lib.parse_graph_text(text)
                if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                    best = out
            except Exception:
                pass  # keep the valid fallback
    return best
