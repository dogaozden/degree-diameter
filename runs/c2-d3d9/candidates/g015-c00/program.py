"""Multi-base voltage lifts searched by simulated annealing (new in this variant).

Construction: take a base bipartite multigraph with K vertices on side A and K on
side B, d-regular, with darts (a_i, b_i, g_i), g_i in a finite group G of order N.
The lift has parts A_{a,x}, B_{b,y} (x, y in G) and edges A_{a,x} ~ B_{b, x g_i}
for each dart i. Order 2KN, max degree d.

Left multiplication by G is an automorphism, so the diameter is exact if every
BFS from the 2K representatives A_{a,1}, B_{b,1} reaches all 2KN vertices within D.
The C engine anneals over dart voltages and B-endpoints, minimising the total
number of unreached (source, vertex) pairs. K = 1 is the bi-Cayley graph of the
parent; K > 1 gives richer base graphs at the same order cost. For each K it
climbs a ladder of group orders N, starting at the first N with 2KN >= L (the
current best), so every success beats or matches the start. Successes are
re-verified by a full BFS on the explicit simple graph before being printed.
If nothing is found, the C program prints "0 0" and Python keeps its fallback.
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

#define MAXN 1024
#define MAXV 4096
#define MAXK 8
#define MAXD 16
#define MAXDARTS (MAXK * MAXD)
#define MAXGRP 8192
#define MAXE 40000
#define MAXDEG 16

static int d, DIAM;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* Largest possible order of a bipartite graph with max degree d and diameter DIAM. */
static long moore_bound(void) {
    if (DIAM <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * DIAM;
    long s = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------------------------------------------------------- groups Z_m x| Z_k */

static int MT[MAXN * MAXN];   /* multiplication table of the current group */
static int INV[MAXN];
static int NG;                /* current group order */
static int gm[MAXGRP], gk[MAXGRP], gr[MAXGRP], ngrp;

/* All groups Z_m x|_r Z_k with m*k = N (r = 1 gives the abelian ones). */
static void enum_groups(int N) {
    ngrp = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ngrp < MAXGRP) { gm[ngrp] = 1; gk[ngrp] = k; gr[ngrp] = 0; ngrp++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngrp < MAXGRP) { gm[ngrp] = m; gk[ngrp] = k; gr[ngrp] = r; ngrp++; }
        }
    }
}

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_group(int idx) {
    int m = gm[idx], k = gk[idx], r = gr[idx];
    int n = m * k;
    NG = n;
    static int rp[MAXN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- lift state */

static int K;                 /* base vertices per side */
static int NV;                /* total vertices = 2*K*NG */
static int dB[MAXDARTS];      /* B endpoint of dart i; A endpoint is i / d */
static int dg[MAXDARTS];      /* voltage of dart i */
static int Bl[MAXDARTS];      /* darts incident to B vertex b: Bl[b*d + j] */
static int distv[MAXV], qv[MAXV];

/* Number of vertices reached from src within DIAM steps.
 * A vertex id: a*NG + x. B vertex id: (K + b)*NG + y.
 * A(a,x) ~ B(dB[i], x g_i) for darts i of a, i.e. i/d == a.
 * B(b,y) ~ A(i/d, y g_i^{-1}) for darts i with dB[i] == b. */
static int bfs_reach(int src) {
    int nv = NV;
    for (int i = 0; i < nv; i++) distv[i] = -1;
    int h = 0, t = 0;
    int An = K * NG;
    distv[src] = 0;
    qv[t++] = src;
    while (h < t) {
        int v = qv[h++];
        int dv = distv[v];
        if (dv >= DIAM) continue;
        if (v < An) {
            int a = v / NG, x = v % NG;
            const int *row = MT + x * NG;
            for (int j = 0; j < d; j++) {
                int i = a * d + j;
                int u = (K + dB[i]) * NG + row[dg[i]];
                if (distv[u] < 0) { distv[u] = dv + 1; qv[t++] = u; }
            }
        } else {
            int w = v - An;
            int b = w / NG, y = w % NG;
            const int *row = MT + y * NG;
            for (int j = 0; j < d; j++) {
                int i = Bl[b * d + j];
                int u = (i / d) * NG + row[INV[dg[i]]];
                if (distv[u] < 0) { distv[u] = dv + 1; qv[t++] = u; }
            }
        }
    }
    return t;
}

static void build_bl(void) {
    int cnt[MAXK];
    for (int b = 0; b < K; b++) cnt[b] = 0;
    for (int i = 0; i < K * d; i++) {
        int b = dB[i];
        Bl[b * d + cnt[b]++] = i;
    }
}

/* Sum over the 2K representative sources of unreached vertices. Zero iff diameter <= DIAM. */
static int cost_fn(void) {
    build_bl();
    int tot = 0;
    for (int s = 0; s < 2 * K; s++) tot += NV - bfs_reach(s * NG);
    return tot;
}

/* Simulated annealing from a random lift. Returns 1 when cost reaches 0 before until. */
static int anneal(double until) {
    int nd = K * d;
    static int init[MAXDARTS];
    for (int i = 0; i < nd; i++) init[i] = i / d;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = init[i]; init[i] = init[j]; init[j] = t;
    }
    for (int i = 0; i < nd; i++) {
        dB[i] = init[i];
        dg[i] = rndint(NG);
    }
    int cur = cost_fn();
    const double T0 = 5.0, Tmin = 0.3, cool = 0.99993;
    double T = T0;
    unsigned long steps = 0;
    for (;;) {
        if (cur == 0) return 1;
        if ((steps & 63) == 0 && now() >= until) return 0;
        steps++;
        int i = rndint(nd);
        if (K > 1 && rndint(10) < 4) {
            int j = rndint(nd);
            if (dB[j] == dB[i]) continue;
            int t = dB[i]; dB[i] = dB[j]; dB[j] = t;
            int nc = cost_fn();
            int delta = nc - cur;
            if (delta <= 0 || urand() < exp(-delta / T)) cur = nc;
            else { t = dB[i]; dB[i] = dB[j]; dB[j] = t; }
        } else {
            if (NG < 2) return 0;
            int old = dg[i];
            int g = rndint(NG - 1);
            if (g >= old) g++;
            dg[i] = g;
            int nc = cost_fn();
            int delta = nc - cur;
            if (delta <= 0 || urand() < exp(-delta / T)) cur = nc;
            else dg[i] = old;
        }
        T *= cool;
        if (T < Tmin) T = T0;
    }
}

/* ---------------------------------------------------------- explicit output */

static long long ecodes[MAXE], ucodes[MAXE], best_codes[MAXE];
static int adjE[MAXV][MAXDEG];
static int degE[MAXV];
static int distE[MAXV], qE[MAXV];
static int best_nv = 0, best_m = 0;

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

/* Build the simple explicit graph of the current lift, verify it by full BFS,
 * and keep it if it is the largest so far. */
static void record_if_valid(void) {
    int Vn = NV;
    int m = 0;
    for (int a = 0; a < K; a++)
        for (int x = 0; x < NG; x++)
            for (int j = 0; j < d; j++) {
                int i = a * d + j;
                int u = a * NG + x;
                int v = (K + dB[i]) * NG + MT[x * NG + dg[i]];
                if (u == v) return;
                int lo = u < v ? u : v, hi = u < v ? v : u;
                if (m >= MAXE) return;
                ecodes[m++] = (long long)lo * Vn + hi;
            }
    qsort(ecodes, (size_t)m, sizeof(long long), cmp_ll);
    int mu = 0;
    for (int e = 0; e < m; e++)
        if (e == 0 || ecodes[e] != ecodes[e - 1]) ucodes[mu++] = ecodes[e];

    for (int v = 0; v < Vn; v++) degE[v] = 0;
    for (int e = 0; e < mu; e++) {
        int u = (int)(ucodes[e] / Vn), v = (int)(ucodes[e] % Vn);
        if (degE[u] >= d || degE[v] >= d) return;
        adjE[u][degE[u]++] = v;
        adjE[v][degE[v]++] = u;
    }
    for (int s = 0; s < Vn; s++) {
        for (int v = 0; v < Vn; v++) distE[v] = -1;
        int h = 0, t = 0;
        distE[s] = 0;
        qE[t++] = s;
        while (h < t) {
            int v = qE[h++];
            if (distE[v] >= DIAM) continue;
            for (int j = 0; j < degE[v]; j++) {
                int u = adjE[v][j];
                if (distE[u] < 0) { distE[u] = distE[v] + 1; qE[t++] = u; }
            }
        }
        if (t != Vn) return;
    }
    if (Vn > best_nv) {
        best_nv = Vn;
        best_m = mu;
        memcpy(best_codes, ucodes, sizeof(long long) * (size_t)mu);
    }
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget L\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    long L = atol(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || DIAM < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;
    long moore = moore_bound();

    const int ks[] = {1, 2, 3, 4, 5, 6, 8};
    const int nk = 7;
    long Ncur[7];
    int act[7];
    for (int idx = 0; idx < nk; idx++) {
        long k = ks[idx];
        long N = (L + 2 * k - 1) / (2 * k);   /* smallest N with 2kN >= L */
        if (N < d + 1) N = d + 1;
        Ncur[idx] = N;
        act[idx] = 1;
    }

    double slice = budget / (nk * 3.0);
    if (slice < 0.5) slice = 0.5;
    if (slice > 6.0) slice = 6.0;

    while (now() < t_end) {
        int any = 0;
        for (int idx = 0; idx < nk && now() < t_end; idx++) {
            if (!act[idx]) continue;
            int k = ks[idx];
            long N = Ncur[idx];
            long V = 2L * k * N;
            if (V > moore || V > MAXV || N > MAXN) { act[idx] = 0; continue; }
            enum_groups((int)N);
            if (ngrp == 0) { act[idx] = 0; continue; }
            K = k;
            build_group(rndint(ngrp));
            NV = 2 * K * NG;
            any = 1;
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (anneal(until)) {
                record_if_valid();
                Ncur[idx] = N + 1;
            }
        }
        if (!any) break;
    }

    if (best_nv > 0) {
        printf("%d %d\n", best_nv, best_m);
        for (int e = 0; e < best_m; e++) {
            int u = (int)(best_codes[e] / best_nv);
            int v = (int)(best_codes[e] % best_nv);
            printf("%d %d\n", u, v);
        }
    } else {
        printf("0 0\n");
    }
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
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
