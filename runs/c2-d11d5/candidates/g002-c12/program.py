"""Bi-Cayley (Haar graph) search, replacing the earlier voltage-lift annealing.

Construction: the Haar graph H(G, S) of a finite group G with |S| = d has vertices A = G and
B = G (2|G| total), with a in A adjacent to b in B iff a^{-1} b is in S. It is bipartite and
d-regular. G acts by left multiplication on each side, so the diameter is at most D iff every
vertex is within D of A_e and of B_e. Each check is therefore two bounded BFS runs.

Phase C (C engine): grow the group order N, keeping the largest N whose Haar graph has
diameter <= D. Each step anneals the connection set S (cost = unreached pairs). Groups are
semidirect products Z_m x| Z_k (cyclic included). Bisection handles failures.

Python builds the exact cases (d = 2, D = 3 projective planes) and the K_{d,d} fallback, runs the
C engine, and returns only graphs that pass lib.is_valid.
"""
import time

import lib


C_SOURCE = r'''
/* Haar-graph annealing with growing group order.
 * Usage: prog d D seed time_limit   (stdin ignored)
 * stdout: "n m" + edges of the largest valid Haar graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 3700
#define MAXD 32

static int d, D;
static int N, GM, GK, GR;
static int rp[MAXG];
static int16_t rmul_store[MAXG * MAXG];
static int16_t *rmul = rmul_store;   /* rmul[g*N + x] = x*g */
static int invv[MAXG];
static int S[MAXD];
static int adj[2 * MAXG * MAXD];     /* adj[v*d + j] */
static int vis[2 * MAXG];
static int qu[2 * MAXG];
static int stamp = 0;

static int sol_N, sol_m, sol_k, sol_r, sol_S[MAXD];

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
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* Semidirect product Z_GM x| Z_GK, element a*GK + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long t = (long)a + (long)rp[b] * c;
    return (int)(t % GM) * GK + (b + e) % GK;
}

static void build_group(int m, int k, int r, int n) {
    GM = m; GK = k; GR = r; N = n;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int g = 0; g < N; g++)
        for (int x = 0; x < N; x++)
            rmul[(long)g * N + x] = (int16_t)gmul(x, g);
    for (int g = 0; g < N; g++) {
        invv[g] = 0;
        for (int x = 0; x < N; x++)
            if (rmul[(long)g * N + x] == 0) { invv[g] = x; break; }
    }
}

static int choose_group(int n, int *om, int *ok, int *orr) {
    if (rnd01() < 0.4) { *om = n; *ok = 1; *orr = 1; return 1; }
    long cnt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { *om = m; *ok = k; *orr = r; }
        }
    }
    return cnt > 0;
}

/* Set connection element j to g: A x -> B (x*g), B y -> A (y*g^{-1}). */
static void setcol(int j, int g) {
    S[j] = g;
    const int16_t *row = rmul + (long)g * N;
    const int16_t *rowi = rmul + (long)invv[g] * N;
    for (int x = 0; x < N; x++) {
        adj[(long)x * d + j] = N + row[x];
        adj[(long)(N + x) * d + j] = rowi[x];
    }
}

static int bfs_reach(int src) {
    stamp++;
    int head = 0, tail = 0, depth = 0;
    qu[tail++] = src;
    vis[src] = stamp;
    while (head < tail && depth < D) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            const int *a = adj + (long)v * d;
            for (int j = 0; j < d; j++) {
                int u = a[j];
                if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
            }
        }
        depth++;
    }
    return tail;
}

/* Unreached vertices from A_e and from B_e (both sources suffice by group symmetry). */
static int evalc(void) {
    int tot = 2 * N;
    return (tot - bfs_reach(0)) + (tot - bfs_reach(N));
}

static int attempt(int n, double until) {
    int m, k, r;
    if (!choose_group(n, &m, &k, &r)) return 0;
    build_group(m, k, r, n);
    for (int j = 0; j < d; j++) {
        int g, ok;
        do {
            g = rndint(N);
            ok = 1;
            for (int i = 0; i < j; i++) if (S[i] == g) ok = 0;
        } while (!ok);
        S[j] = g;
    }
    for (int j = 0; j < d; j++) setcol(j, S[j]);
    int cost = evalc();
    double start = now();
    double span = until - start;
    if (span <= 0) span = 1e-3;
    double T0 = cost / 8.0 > 1.0 ? cost / 8.0 : 1.0;
    double T = 1.0;
    for (long it = 0; cost > 0; it++) {
        if ((it & 31) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            T = 0.15 + T0 * (1 - f) * (1 - f);
        }
        int j = rndint(d), g = rndint(N);
        int dup = 0;
        for (int i = 0; i < d; i++) if (S[i] == g) { dup = 1; break; }
        if (dup) continue;
        int old = S[j];
        setcol(j, g);
        int c2 = evalc();
        if (c2 <= cost || rnd01() < exp(-(c2 - cost) / T)) cost = c2;
        else setcol(j, old);
    }
    return cost == 0;
}

static void print_solution(void) {
    build_group(sol_m, sol_k, sol_r, sol_N);
    for (int j = 0; j < d; j++) S[j] = sol_S[j];
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", x, N + (int)rmul[(long)S[j] * N + x]);
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
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    double t0 = now();
    double t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Fallback: K_{d,d} = Haar graph of Z_d with S = all of Z_d. */
    sol_N = d; sol_m = d; sol_k = 1; sol_r = 1;
    for (int j = 0; j < d; j++) sol_S[j] = j;

    int best_N = d, fail_N = MAXG + 1;
    for (;;) {
        double rem = t_end - now();
        if (rem < 0.2 || best_N >= MAXG) break;
        int target;
        if (fail_N > MAXG) {
            int step = best_N / 30;
            if (step < 1) step = 1;
            target = best_N + step;
        } else if (fail_N - best_N > 1) {
            target = (best_N + fail_N) / 2;
        } else {
            target = fail_N;
        }
        if (target > MAXG) target = MAXG;
        double slice = rem * 0.3;
        if (slice > rem) slice = rem;
        if (attempt(target, now() + slice)) {
            best_N = target;
            sol_N = target; sol_m = GM; sol_k = GK; sol_r = GR;
            for (int j = 0; j < d; j++) sol_S[j] = S[j];
            if (fail_N <= target) fail_N = MAXG + 1;
        } else {
            if (fail_N > MAXG || target < fail_N) fail_N = target;
        }
    }
    print_solution();
    return 0;
}
'''


def _cycle(n):
    """Cycle C_n with n even: bipartite, 2-regular, diameter n/2."""
    return n, [(i, (i + 1) % n) for i in range(n)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        return _cycle(2 * D)

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    # Exact Moore graph for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        cand = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(cand[0], cand[1], d, D):
            return cand

    if d > 30 or time_limit < 8:
        return best

    elapsed = time.monotonic() - t0
    budget = min(44.0, 0.75 * time_limit - 3.0 - elapsed)
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 20)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
