"""Bold variant: voltage lifts over metacyclic groups with a multi-vertex base.

Instead of a single-orbit bi-Cayley graph (two base vertices), this builds a
d-regular bipartite lift of a base graph with 2t vertices (t per side). The base
is the union of d random permutations from side A to side B, and each dart
carries a voltage in a metacyclic group G = Z_m x| Z_k of order M, so the
lift has order 2tM.

Left multiplication by G is an automorphism of every lift, so the diameter is
at most D iff every vertex is within distance D of one base vertex per fiber.
That gives 2t BFS runs per evaluation. Voltages are improved by simulated
annealing on the number of (fiber base, vertex) pairs at distance > D.

The target order T increases from a lower bound in steps of 2. Each T gets a
time slice, and the largest T that succeeds is kept. The output is re-verified
by full BFS from every vertex. If nothing is found, Python falls back to the
known start (or K_{d,d}), and every returned graph is checked with lib.is_valid.
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

#define MAXM 1024
#define MAXV 2048
#define MAXD 16
#define MAXT 8
#define MAXGRP 2048
#define ITER 8000

typedef struct { int m, k, r; } Grp;

static int d, D;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

static Grp garr[MAXGRP];
static int ngrp;

static void enum_groups(int M) {
    ngrp = 0;
    for (int m = 1; m <= M; m++) {
        if (M % m) continue;
        int k = M / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngrp < MAXGRP) {
                garr[ngrp].m = m;
                garr[ngrp].k = k;
                garr[ngrp].r = r;
                ngrp++;
            }
        }
    }
}

static int MT[MAXM * MAXM];
static int INVG[MAXM];
static int rp[MAXM];
static int Mg;
static Grp curG;

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_group(Grp G) {
    int m = G.m, k = G.k, M = m * k;
    Mg = M;
    curG = G;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < M; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < M; y++) {
            int c = y / k, e = y % k;
            MT[x * M + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < M; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int ina = (m - (int)((long)rp[nb] * a % m)) % m;
        INVG[x] = ina * k + nb;
    }
}

/* ---------------------------------------------------------- voltage lift state */

static int T_t;                       /* t: base has t vertices per side */
static int sig[MAXD][MAXT];           /* sig[c][i] = j : dart c from A_i to B_j */
static int isig[MAXD][MAXT];         /* isig[c][j] = i */
static int volt[MAXT][MAXD];          /* voltage of dart (i, c) */
static int adjv[MAXV][MAXD];
static int distv[MAXV], qv[MAXV];

/* A vertex i*M+g, B vertex (t+j)*M+h. A_{i,g} ~ B_{sig[c][i], g*v}. */
static void build_adj(void) {
    int t = T_t, M = Mg;
    for (int i = 0; i < t; i++)
        for (int g = 0; g < M; g++) {
            int u = i * M + g;
            for (int c = 0; c < d; c++) {
                int j = sig[c][i];
                adjv[u][c] = (t + j) * M + MT[g * M + volt[i][c]];
            }
        }
    for (int j = 0; j < t; j++)
        for (int h = 0; h < M; h++) {
            int v = (t + j) * M + h;
            for (int c = 0; c < d; c++) {
                int i = isig[c][j];
                adjv[v][c] = i * M + MT[h * M + INVG[volt[i][c]]];
            }
        }
}

/* Number of (fiber base, vertex) pairs not within distance D. 0 means diameter <= D. */
static long cost_eval(void) {
    int t = T_t, M = Mg, V = 2 * t * M;
    build_adj();
    long unreached = 0;
    for (int f = 0; f < 2 * t; f++) {
        int src = f * M;
        for (int v = 0; v < V; v++) distv[v] = -1;
        int head = 0, tail = 0;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            for (int c = 0; c < d; c++) {
                int u = adjv[v][c];
                if (distv[u] < 0) {
                    distv[u] = dv + 1;
                    qv[tail++] = u;
                }
            }
        }
        unreached += V - tail;
    }
    return unreached;
}

/* Row i has no two darts with the same (target, voltage). */
static int row_ok(int i) {
    for (int c1 = 0; c1 < d; c1++)
        for (int c2 = c1 + 1; c2 < d; c2++)
            if (sig[c1][i] == sig[c2][i] && volt[i][c1] == volt[i][c2]) return 0;
    return 1;
}

static void random_perms(void) {
    int t = T_t;
    for (int c = 0; c < d; c++) {
        int p[MAXT];
        for (int i = 0; i < t; i++) p[i] = i;
        for (int i = t - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i];
            p[i] = p[j];
            p[j] = tmp;
        }
        for (int i = 0; i < t; i++) {
            sig[c][i] = p[i];
            isig[c][p[i]] = i;
        }
    }
}

static int init_state(void) {
    int M = Mg;
    for (int i = 0; i < T_t; i++) {
        int ok = 0;
        for (int tries = 0; tries < 5000 && !ok; tries++) {
            for (int c = 0; c < d; c++) volt[i][c] = rndint(M);
            ok = row_ok(i);
        }
        if (!ok) return 0;
    }
    return 1;
}

/* Simulated annealing on voltages. Returns 1 on success (state left in place). */
static int anneal(double until) {
    int t = T_t, M = Mg;
    long cur = cost_eval();
    if (cur == 0) return 1;
    for (int it = 0; it < ITER; it++) {
        if ((it & 63) == 0 && now() >= until) return 0;
        int i = rndint(t), c = rndint(d);
        int old = volt[i][c];
        int nv = rndint(M);
        if (nv == old) continue;
        volt[i][c] = nv;
        if (!row_ok(i)) { volt[i][c] = old; continue; }
        long nc = cost_eval();
        if (nc == 0) return 1;
        double temp = 2.0 * pow(0.03, (double)it / ITER);
        if (nc <= cur || rndu() < exp(-(double)(nc - cur) / temp)) cur = nc;
        else volt[i][c] = old;
    }
    return 0;
}

/* ---------------------------------------------------------- best solution */

static int have_best = 0;
static int bT_t;
static Grp bG;
static int bsig[MAXD][MAXT];
static int bvolt[MAXT][MAXD];

static void save_best(void) {
    have_best = 1;
    bT_t = T_t;
    bG = curG;
    for (int c = 0; c < d; c++)
        for (int i = 0; i < T_t; i++) bsig[c][i] = sig[c][i];
    for (int i = 0; i < T_t; i++)
        for (int c = 0; c < d; c++) bvolt[i][c] = volt[i][c];
}

/* Full verification by BFS from every vertex and structural checks. */
static int verify_best(void) {
    int t = bT_t;
    build_group(bG);
    T_t = t;
    for (int c = 0; c < d; c++)
        for (int i = 0; i < t; i++) {
            sig[c][i] = bsig[c][i];
            isig[c][bsig[c][i]] = i;
        }
    for (int i = 0; i < t; i++)
        for (int c = 0; c < d; c++) volt[i][c] = bvolt[i][c];
    int M = Mg, V = 2 * t * M;
    build_adj();
    for (int u = 0; u < V; u++) {
        for (int c = 0; c < d; c++) {
            int v = adjv[u][c];
            if (v < 0 || v >= V || v == u) return 0;
            if ((u < t * M) == (v < t * M)) return 0;
            for (int c2 = 0; c2 < c; c2++)
                if (adjv[u][c2] == v) return 0;
            int back = 0;
            for (int c2 = 0; c2 < d; c2++)
                if (adjv[v][c2] == u) back = 1;
            if (!back) return 0;
        }
    }
    for (int src = 0; src < V; src++) {
        for (int v = 0; v < V; v++) distv[v] = -1;
        int head = 0, tail = 0;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            for (int c = 0; c < d; c++) {
                int u = adjv[v][c];
                if (distv[u] < 0) {
                    distv[u] = dv + 1;
                    qv[tail++] = u;
                }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void print_best(void) {
    int t = bT_t, M = Mg;
    int V = 2 * t * M, A = t * M;
    printf("%d %d\n", V, A * d);
    for (int u = 0; u < A; u++)
        for (int c = 0; c < d; c++)
            printf("%d %d\n", u, adjv[u][c]);
}

/* ---------------------------------------------------------- search over T */

static int attempt(int T, double until) {
    int fe[MAXT], nf = 0;
    for (int t = 1; t <= MAXT; t++) {
        if (T % (2 * t)) continue;
        int M = T / (2 * t);
        if (M >= 1 && (long)t * M >= d) fe[nf++] = t;
    }
    if (!nf) return 0;
    while (now() < until) {
        int t = fe[rndint(nf)];
        int M = T / (2 * t);
        enum_groups(M);
        if (!ngrp) continue;
        Grp G = garr[rndint(ngrp)];
        build_group(G);
        T_t = t;
        random_perms();
        if (!init_state()) continue;
        if (anneal(until)) {
            save_best();
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget tmin\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int tmin = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now();
    double t_end = t0 + budget * 0.92;

    long mb = moore_bound();
    long Tmax = mb < MAXV ? mb : MAXV;
    Tmax -= Tmax % 2;
    int T = tmin < 2 ? 2 : tmin;
    if (T % 2) T++;

    double slice = budget / 25.0;
    if (slice < 0.8) slice = 0.8;
    if (slice > 4.0) slice = 4.0;

    for (; T <= Tmax && now() < t_end; T += 2) {
        double until = now() + slice;
        if (until > t_end) until = t_end;
        attempt(T, until);
    }

    if (have_best && verify_best()) {
        print_best();
        return 0;
    }
    printf("0 0\n");
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
    """A valid graph that always works: K_{d,d}, then K_2, then a single vertex."""
    cands = []
    if D >= 2 and d >= 1:
        cands.append(lib.haar_graph(d, range(d)))      # K_{d,d}
    if D >= 1 and d >= 1:
        cands.append((2, [(0, 1)]))
    cands.append((1, []))
    for c in cands:
        if lib.is_valid(c[0], c[1], d, D):
            return c
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = _fallback(d, D)
    best = start

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    # Start the scan at about 0.45 of the Moore bound (or just above the known graph).
    tmin = max(best[0] + 2, int(0.45 * moore))
    if tmin % 2:
        tmin += 1
    if tmin > moore:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), tmin],
                         stdin_graph=None, timeout=budget + 5.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
