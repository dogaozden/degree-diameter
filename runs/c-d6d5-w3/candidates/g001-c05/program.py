"""Cayley-Haar search: bipartite graphs a_x ~ b_{x*s} over small groups G (semidirect products
Z_m x| Z_k), with simulated annealing over the connection set S (|S| = d). The graph is
vertex-transitive on each side, so diameter <= D reduces to two depth-D balls, from a_0 and b_0.
Python keeps a valid fallback and only accepts the C output if lib.is_valid confirms it.
"""
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

#define MAXG 1200
#define MAXD 16
#define MAXV (2 * MAXG)
#define MAXCAND 40000

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
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

/* ---------------------------------------------------------------- groups */

/* Z_m x|_r Z_k, element (a,b) coded a*k+b, identity 0. */
static int Gm, Gk, Gr, N;
static int rp[MAXG];
static short MT[MAXG][MAXG];
static int invv[MAXG];

static int gmul_direct(int x, int y) {
    int a = x / Gk, b = x % Gk, c = y / Gk, e = y % Gk;
    return (int)(((long)a + (long)rp[b] * c) % Gm) * Gk + (b + e) % Gk;
}

static void set_group(int m, int k, int r) {
    Gm = m; Gk = k; Gr = r; N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[x][y] = (short)gmul_direct(x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { invv[x] = y; break; }
}

static int cm[MAXCAND], ck[MAXCAND], cr[MAXCAND];

/* All groups of order n: cyclic (m = 1 or r = 1) and semidirect products. Always >= 1. */
static int enum_groups(int n) {
    int cnt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (cnt < MAXCAND) { cm[cnt] = 1; ck[cnt] = k; cr[cnt] = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXCAND) { cm[cnt] = m; ck[cnt] = k; cr[cnt] = r; cnt++; }
        }
    }
    return cnt;
}

/* ---------------------------------------------------------------- Haar cost */

static int S[MAXD];
static int mark[MAXV];
static int stampv = 0;
static int qu[MAXV];
static int dep[MAXV];

static int in_S(int v, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == v) return 1;
    return 0;
}

/* Vertices a_x = x (0..N-1), b_y = N + y. a_x ~ b_{x*s}; b_y ~ a_{y*s^-1}.
 * Returns the number of vertices within distance D of src. */
static int ball(int src) {
    int head = 0, tail = 0;
    stampv++;
    qu[tail++] = src;
    mark[src] = stampv;
    dep[src] = 0;
    while (head < tail) {
        int v = qu[head++];
        if (dep[v] >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + MT[v][S[i]];
                if (mark[u] != stampv) {
                    mark[u] = stampv;
                    dep[u] = dep[v] + 1;
                    qu[tail++] = u;
                }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = MT[y][invv[S[i]]];
                if (mark[u] != stampv) {
                    mark[u] = stampv;
                    dep[u] = dep[v] + 1;
                    qu[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Zero iff the Haar graph has diameter <= D (by vertex-transitivity on each side). */
static int cost(void) {
    return (2 * N - ball(0)) + (2 * N - ball(N));
}

static void random_S(void) {
    for (int i = 0; i < d;) {
        int v = rndint(N);
        if (!in_S(v, i)) S[i++] = v;
    }
}

static int anneal(int steps) {
    int cur = cost();
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / steps) + 0.15;
        int i = rndint(d);
        int nv = rndint(N);
        if (in_S(nv, d)) continue;
        int old = S[i];
        S[i] = nv;
        int c = cost();
        if (c <= cur || rnd01() < exp((double)(cur - c) / T)) cur = c;
        else S[i] = old;
    }
    return cur == 0;
}

/* ---------------------------------------------------------------- main */

static int best_N = 0, best_m, best_k, best_r;
static int best_S[MAXD];

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
    t_end = t0 + limit * 0.9 - 0.1;
    rng ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng) rng = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long Nmax = moore / 2;
    if (Nmax > MAXG) Nmax = MAXG;

    while (now() < t_end) {
        int target = best_N == 0 ? d : best_N + 1 + rndint(3);
        if (target < d) target = d;
        if (target > Nmax) {
            if (best_N + 1 > Nmax) break;
            target = (int)Nmax;
        }
        if (target < d) break;

        int ng = enum_groups(target);
        int gi = rndint(ng);
        set_group(cm[gi], ck[gi], cr[gi]);
        random_S();
        if (anneal(12000)) {
            best_N = N;
            best_m = Gm;
            best_k = Gk;
            best_r = Gr;
            memcpy(best_S, S, sizeof(int) * (size_t)d);
        }
    }

    if (best_N == 0) {
        printf("0 0\n");
        return 0;
    }
    set_group(best_m, best_k, best_r);
    long m_edges = (long)N * d;
    printf("%d %ld\n", 2 * N, m_edges);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + MT[x][best_S[i]]);
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


def _fallback(d, D):
    """Always-valid simple graph: K_{d,d} when D >= 2, else a single edge."""
    if D >= 2 and d >= 1:
        g = lib.haar_graph(d, range(d))
        if lib.is_valid(g[0], g[1], d, D):
            return g
    if lib.is_valid(2, [(0, 1)], d, D):
        return (2, [(0, 1)])
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = _fallback(d, D)
    start = known_start(d, D)
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine
    if budget > 0.3:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
