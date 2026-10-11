"""Bold rewrite: Haar graphs over groups (difference covers) for D >= 3.

Construction: pick a group G of order N and a d-subset S of G with S S^-1 = G and S^-1 S = G.
The bipartite graph with parts {a_x} and {b_y}, where a_x ~ b_{xs} for s in S, is d-regular
on 2N vertices and has diameter <= 3, so it is valid for every D >= 3. Groups are semidirect
products Z_m x| Z_k, with cyclic groups as a special case. The C engine anneals S to a cover
for increasing N. Any failure falls back to a known construction or K_{d,d}.
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

#define MAXG 512
#define MAXD 64

static int d, D;
static int N;                        /* current group order */
static int mul_t[MAXG][MAXG];
static int inv_t[MAXG];
static int rp_[MAXG];
static int S[MAXD];
static int cntL[MAXG], cntR[MAXG];   /* cntL: s t^-1 counts, cntR: s^-1 t counts (ordered pairs) */
static int covL, covR;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

/* Uniformly random group Z_m x|_r Z_k of order n (reservoir sampling over all valid (m,k,r)). */
static int random_group(int n, int *om, int *ok, int *orr) {
    long count = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { *om = 1; *ok = k; *orr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { *om = m; *ok = k; *orr = r; }
        }
    }
    return count > 0;
}

/* Element (a,b) is a*k+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Identity is 0. */
static void build_group(int m, int k, int r) {
    N = m * k;
    rp_[0] = 1 % m;
    for (int b = 1; b < k; b++) rp_[b] = (int)(((long)rp_[b - 1] * r) % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mul_t[x][y] = ((a + rp_[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mul_t[x][y] == 0) { inv_t[x] = y; break; }
}

static void bump(int *cnt, int *cov, int idx, int dl) {
    if (dl > 0) { if (cnt[idx]++ == 0) (*cov)++; }
    else        { if (--cnt[idx] == 0) (*cov)--; }
}

/* Add (dl=+1) or remove (dl=-1) every ordered pair that involves slot i holding value v. */
static void slot_pairs(int i, int v, int dl) {
    int iv = inv_t[v];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int w = S[j], iw = inv_t[w];
        bump(cntL, &covL, mul_t[v][iw], dl);
        bump(cntL, &covL, mul_t[w][iv], dl);
        bump(cntR, &covR, mul_t[iv][w], dl);
        bump(cntR, &covR, mul_t[iw][v], dl);
    }
    bump(cntL, &covL, 0, dl);
    bump(cntR, &covR, 0, dl);
}

static void build_counts(void) {
    memset(cntL, 0, sizeof(int) * N);
    memset(cntR, 0, sizeof(int) * N);
    covL = covR = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            bump(cntL, &covL, mul_t[S[i]][inv_t[S[j]]], 1);
            bump(cntR, &covR, mul_t[inv_t[S[i]]][S[j]], 1);
        }
}

static int in_S(int x, int cnt) {
    for (int j = 0; j < cnt; j++) if (S[j] == x) return 1;
    return 0;
}

/* Anneal S (S[0] = identity, WLOG) until S S^-1 = G and S^-1 S = G. Returns 1 on success. */
static int anneal(double until) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int x;
        do { x = rndint(N); } while (in_S(x, i));
        S[i] = x;
    }
    build_counts();
    int cur = 2 * N - covL - covR;
    double t0 = now(), span = until - t0;
    if (span <= 0) return 0;
    const double T0 = 2.0, T1 = 0.15;
    double T = T0;
    long it = 0;
    while (cur > 0) {
        if ((it & 1023) == 0) {
            double t = now();
            if (t >= until) return 0;
            double f = (t - t0) / span;
            T = T0 * pow(T1 / T0, f);
        }
        it++;
        int i = 1 + rndint(d - 1);
        int u = S[i], x;
        do { x = rndint(N); } while (in_S(x, d));
        slot_pairs(i, u, -1);
        S[i] = x;
        slot_pairs(i, x, +1);
        int nw = 2 * N - covL - covR;
        int delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            cur = nw;
        } else {
            slot_pairs(i, x, -1);
            S[i] = u;
            slot_pairs(i, u, +1);
        }
    }
    return 1;
}

/* Haar graph: a_x (0..n-1) ~ b_{x*s} (n + index) for s in S. Printed as "n m" + edges. */
static void print_graph(int n, const int *Sb) {
    printf("%d %d\n", 2 * n, n * d);
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, n + mul_t[x][Sb[i]]);
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
    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    double deadline = now() + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    int maxN = d * (d - 1) + 1;   /* |S S^-1| <= d(d-1)+1 */
    if (maxN > MAXG - 1) maxN = MAXG - 1;

    int bestN = 0, bm = 0, bk = 0, br = 0;
    int bestS[MAXD];
    int target = d;
    while (target <= maxN && now() < deadline) {
        int m, k, r;
        if (!random_group(target, &m, &k, &r)) { target++; continue; }
        build_group(m, k, r);
        double left = deadline - now();
        double slice = left / 3.0;
        if (slice > 8.0) slice = 8.0;
        if (slice < 1.0) slice = left;
        if (anneal(now() + slice)) {
            bestN = target;
            bm = m; bk = k; br = r;
            memcpy(bestS, S, sizeof(int) * d);
            target++;
        }
    }
    if (bestN == 0) { printf("0 0\n"); return 0; }
    build_group(bm, bk, br);
    print_graph(bestN, bestS);
    return 0;
}
'''


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    # Safe fallback first: a closed-form graph if one applies, else K_{d,d} (valid for D >= 2).
    best = None
    try:
        start = known_start(d, D)
        if start is not None and lib.is_valid(*start, d, D):
            best = start
    except Exception:
        best = None
    if best is None:
        try:
            cand = lib.haar_graph(d, range(d))
            if lib.is_valid(*cand, d, D):
                best = cand
        except Exception:
            best = None
    if best is None:
        best = (2, [(0, 1)])

    # Difference-cover Haar search: diameter 3, so it is valid for every D >= 3.
    if D >= 3 and d >= 2:
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 10)
                out = lib.parse_graph_text(text)
                if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                    best = out
            except Exception:
                pass
    return best
