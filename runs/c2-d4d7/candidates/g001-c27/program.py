"""Bi-Cayley search for bipartite degree-diameter graphs (a different construction from the voltage lifts).

For a finite group G of order N and a connection set S = {s_1..s_d}, the bi-Cayley graph has
parts A = {a_x} and B = {b_y}, with edges a_x ~ b_{x s}. Left translation is an automorphism,
so the diameter equals the larger of two BFS eccentricities (from a_e and from b_e). Each
candidate costs O(N d). The C engine anneals over connection sets for many groups
(Z_m x| Z_k) and orders N, then returns the largest valid graph (2N vertices) it finds.
Python keeps a valid fallback, so any failure falls back to the best valid graph so far.
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

#define MAXG 2048
#define MAXD 16
#define MAXGROUPS 8192
#define ITERS 40000
#define SLICE 1.5

typedef struct { int m, k, r; } Grp;

static int d, D;
static long moore;
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

/* Element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int N;
static Grp cur;
static int MUL[MAXG * MAXG];
static int INV[MAXG];

static void set_group(Grp g) {
    static int rp[MAXG];
    int m = g.m, k = g.k, r = g.r;
    cur = g;
    N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int *row = MUL + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            row[y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
        int nb = (k - b) % k;
        int ia = (int)((m - ((long)rp[nb] * a) % m) % m);
        INV[x] = ia * k + nb;
    }
}

/* All (m, k, r) with m*k = Nn, gcd(r, m) = 1 and r^k = 1 mod m. Returns the count. */
static int enum_groups(int Nn, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= Nn; m++) {
        if (Nn % m) continue;
        int k = Nn / m;
        if (m == 1) {
            if (cnt < MAXGROUPS) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXGROUPS) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

/* ------------------------------------------------------------ bi-Cayley evaluation */

static int S[MAXD], Sinv[MAXD];
static unsigned char inS[MAXG];
static int dist[2 * MAXG];
static int qu[2 * MAXG];

/* BFS from node st (A node x = x, B node y = N + y) up to depth D.
 * Afterwards dist[v] >= 0 exactly for nodes within distance D of st. Returns the reached count. */
static int bfs(int st) {
    for (int v = 0; v < 2 * N; v++) dist[v] = -1;
    int h = 0, t = 0, reached = 1;
    qu[t++] = st;
    dist[st] = 0;
    while (h < t) {
        int v = qu[h++];
        if (dist[v] >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + MUL[v * N + S[i]];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; reached++; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = MUL[y * N + Sinv[i]];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; reached++; }
            }
        }
    }
    return reached;
}

/* Number of violations: vertices not within D of a_e, plus B vertices not within D of b_e.
 * Zero means valid: left translations cover every pair of vertices. */
static int cost(void) {
    for (int i = 0; i < d; i++) Sinv[i] = INV[S[i]];
    int ra = bfs(0);
    int cA = 2 * N - ra;
    bfs(N);
    int cB = 0;
    for (int v = N; v < 2 * N; v++)
        if (dist[v] < 0) cB++;
    return cA + cB;
}

/* Simulated annealing over d-subsets of the current group. Returns 1 if cost reaches 0;
 * on success S holds the connection set. */
static int sa_run(int iters, double until) {
    if (N <= d) return 0;
    for (int i = 0; i < d; i++) {
        int t;
        do t = rndint(N); while (inS[t]);
        S[i] = t;
        inS[t] = 1;
    }
    int c = cost();
    double T = 1.0;
    int ok = (c == 0);
    for (int it = 0; it < iters && !ok; it++) {
        if ((it & 127) == 0 && now() > until) break;
        int i = rndint(d);
        int old = S[i];
        int t;
        do t = rndint(N); while (inS[t]);
        S[i] = t;
        int nc = cost();
        if (nc <= c || rnd01() < exp(-(double)(nc - c) / T)) {
            inS[old] = 0;
            inS[t] = 1;
            c = nc;
            if (c == 0) ok = 1;
        } else {
            S[i] = old;
        }
        T *= 0.9995;
        if (T < 0.15) T = 1.0;
    }
    for (int i = 0; i < d; i++) inS[S[i]] = 0;
    return ok;
}

/* ------------------------------------------------------------ best graph */

static int bestN;
static Grp bestG;
static int bestS[MAXD];

/* Try groups of order Nn, annealing connection sets, until a valid one is found or time runs out. */
static int try_order(int Nn, double until) {
    static Grp gs[MAXGROUPS];
    int ng = enum_groups(Nn, gs);
    if (ng == 0) return 0;
    while (now() < until) {
        Grp g = gs[rndint(ng)];
        set_group(g);
        if (sa_run(ITERS, until)) {
            bestN = Nn;
            bestG = g;
            for (int i = 0; i < d; i++) bestS[i] = S[i];
            return 1;
        }
    }
    return 0;
}

/* Print the best graph (2N vertices, N*d edges). Re-checks it, else prints K_{d,d}. */
static void emit(void) {
    set_group(bestG);
    for (int i = 0; i < d; i++) S[i] = bestS[i];
    if (cost() != 0) {
        bestN = d;
        bestG.m = 1; bestG.k = d; bestG.r = 0;
        for (int i = 0; i < d; i++) bestS[i] = i;
        set_group(bestG);
        for (int i = 0; i < d; i++) S[i] = i;
    }
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + MUL[x * N + S[i]]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    if (t_end < t0 + 0.05) t_end = t0 + 0.05;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("2 1\n0 1\n");   /* K_{1,1}: valid for any d >= 1, D >= 1 */
        return 0;
    }

    moore = moore_bound();
    /* K_{d,d} = bi-Cayley graph of Z_d with S = all of Z_d: always valid for D >= 2. */
    bestN = d;
    bestG.m = 1; bestG.k = d; bestG.r = 0;
    for (int i = 0; i < d; i++) bestS[i] = i;

    if (2L * d < moore) {
        int lo = bestN + 1, miss = 1;
        while (now() < t_end && 2L * lo <= moore && lo <= MAXG) {
            int Nn = lo + rndint(miss);
            if (2L * Nn > moore || Nn > MAXG) Nn = lo;
            double until = now() + SLICE;
            if (until > t_end) until = t_end;
            if (try_order(Nn, until)) {
                lo = Nn + 1;
                miss = 1;
            } else if (miss < 12) {
                miss++;
            }
        }
    }
    emit();
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


def _valid(g, d, D):
    try:
        return lib.is_valid(g[0], g[1], d, D)
    except Exception:
        return False


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    # Safe fallback chain: K_{d,d} (D >= 2), else K_{1,1}, else a single vertex.
    best = None
    for cand in (lib.haar_graph(d, range(d)) if D >= 2 else None,
                 (2, [(0, 1)]),
                 (1, [])):
        if cand is not None and _valid(cand, d, D):
            best = cand
            break

    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and _valid(start, d, D) and start[0] > best[0]:
        best = start

    if best[0] >= lib.moore_bound(d, D) or D < 2:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and _valid(out, d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
