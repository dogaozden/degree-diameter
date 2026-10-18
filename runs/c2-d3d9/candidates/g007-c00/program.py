"""Exhaustive normalised Cayley search for bipartite degree-diameter graphs.

Replaces the random-sampling Cayley phase with a systematic search.

Construction: vertices A_x and B_y for x, y in a group G of order N, with edges
A_x -- B_{x s} for s in S, |S| = d. Left multiplication is transitive on each side,
so the diameter test is two BFS runs (from A_e and B_e).

C search, in order:
  A. Cyclic groups Z_N with normalised connection sets S = {0, 1, b_2, ..., b_{d-1}}
     (scaling and translation reduce S to this form when some difference is a unit).
     Scans N downward from the Moore limit and stops at the first success.
  B. For N above the Phase A result: all metacyclic groups Z_m x| Z_k of order N,
     with exhaustive enumeration of connection sets {0} u (d-1 others). Each group gets
     a time cap, so the search stays diverse.

build() keeps a valid fallback (known start or K_{d,d}) and only accepts a C result
that is larger and passes lib.is_valid, so a weak search cannot lower the score.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1100
#define MAXD 16
#define MAXG 256
#define GROUP_CAP 2.0

static int d, D;
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int mt[MAXN * MAXN];
static int inv_[MAXN];
static int GN, GM, GK, GR;

static void build_group(int m, int k, int r) {
    int N = m * k;
    int rp[MAXN];
    GN = N; GM = m; GK = k; GR = r;
    for (int b = 0; b < k; b++) rp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mt[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        inv_[x] = -1;
        for (int y = 0; y < N; y++)
            if (mt[x * N + y] == 0) { inv_[x] = y; break; }
    }
}

/* ------------------------------------------------------------ diameter test */

static int dist_buf[2 * MAXN], que[2 * MAXN];

/* Check that all 2N vertices are within D of A_e and of B_e (the graph is
 * vertex-transitive on each side, so these two sources decide the diameter). */
static int dist_ok(const int *S, int ns) {
    int N = GN;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < 2 * N; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[s0] = 0;
        que[tail++] = s0;
        while (head < tail) {
            int v = que[head++];
            int dv = dist_buf[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int i = 0; i < ns; i++) {
                    int u = N + mt[v * N + S[i]];
                    if (dist_buf[u] < 0) { dist_buf[u] = dv + 1; que[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < ns; i++) {
                    int u = mt[y * N + inv_[S[i]]];
                    if (dist_buf[u] < 0) { dist_buf[u] = dv + 1; que[tail++] = u; }
                }
            }
        }
        if (tail != 2 * N) return 0;
    }
    return 1;
}

static int test_S(const int *S) { return dist_ok(S, d); }

/* ------------------------------------------------------------ result */

static int found = 0, found_N = 0, found_m = 0, found_k = 0, found_r = 0;
static int found_S[MAXD];

static void record(const int *S) {
    found = 1;
    found_N = GN; found_m = GM; found_k = GK; found_r = GR;
    memcpy(found_S, S, sizeof(int) * d);
}

/* Advance a strictly increasing index tuple of length c with values <= hi. */
static int next_combo(int *idx, int c, int hi) {
    int i = c - 1;
    while (i >= 0 && idx[i] == hi - (c - 1 - i)) i--;
    if (i < 0) return 0;
    idx[i]++;
    for (int j = i + 1; j < c; j++) idx[j] = idx[j - 1] + 1;
    return 1;
}

/* ------------------------------------------------------------ phase A: cyclic, normalised */

static int phaseA(int N) {
    if (N < 2 || N < d) return 0;
    build_group(N, 1, 1);
    int S[MAXD];
    S[0] = 0;
    S[1] = 1;
    int c = d - 2;
    if (c == 0) {
        if (test_S(S)) { record(S); return 1; }
        return 0;
    }
    if (N - 2 < c) return 0;
    int idx[MAXD];
    for (int i = 0; i < c; i++) idx[i] = 2 + i;
    do {
        if (now() > t_end) return 0;
        for (int i = 0; i < c; i++) S[2 + i] = idx[i];
        if (test_S(S)) { record(S); return 1; }
    } while (next_combo(idx, c, N - 1));
    return 0;
}

static void phaseA_all(long Nmax) {
    for (long N = Nmax; N >= d && N >= 2; N--) {
        if (now() > t_end) return;
        if (phaseA((int)N)) return;
    }
}

/* ------------------------------------------------------------ phase B: all groups, exhaustive */

static int phaseB(int N) {
    static int gm[MAXG], gk[MAXG], gr[MAXG];
    int cnt = 0;
    for (int m = 1; m <= N && cnt < MAXG; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            gm[cnt] = 1; gk[cnt] = k; gr[cnt] = 0; cnt++;
            continue;
        }
        for (int r = 1; r < m && cnt < MAXG; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
            gm[cnt] = m; gk[cnt] = k; gr[cnt] = r; cnt++;
        }
    }
    for (int i = cnt - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t;
        t = gm[i]; gm[i] = gm[j]; gm[j] = t;
        t = gk[i]; gk[i] = gk[j]; gk[j] = t;
        t = gr[i]; gr[i] = gr[j]; gr[j] = t;
    }
    int c = d - 1;
    if (N - 1 < c) return 0;
    int S[MAXD], idx[MAXD];
    for (int g = 0; g < cnt; g++) {
        if (now() > t_end) return 0;
        double gu = now() + GROUP_CAP;
        if (gu > t_end) gu = t_end;
        build_group(gm[g], gk[g], gr[g]);
        S[0] = 0;
        for (int i = 0; i < c; i++) idx[i] = 1 + i;
        do {
            if (now() > gu) break;
            for (int i = 0; i < c; i++) S[1 + i] = idx[i];
            if (test_S(S)) { record(S); return 1; }
        } while (next_combo(idx, c, N - 1));
    }
    return 0;
}

static void phaseB_all(long Nmax, long Nlow) {
    for (long N = Nmax; N >= Nlow; N--) {
        if (now() > t_end) return;
        if (phaseB((int)N)) return;
    }
}

/* ------------------------------------------------------------ output */

static void print_found(void) {
    int N = found_N;
    build_group(found_m, found_k, found_r);
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + mt[x * N + found_S[i]]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.9;
    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    long Nmax = moore_bound() / 2;
    if (Nmax > MAXN - 1) Nmax = MAXN - 1;

    phaseA_all(Nmax);
    long low = found ? (long)found_N + 1 : 2;
    if (low < d) low = d;
    if (low <= Nmax) phaseB_all(Nmax, low);

    if (found) print_found();
    else printf("0 0\n");
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
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    if best[0] >= lib.moore_bound(d, D):
        return best
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5 and d >= 2 and D >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
