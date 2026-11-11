"""Haar-graph search over semidirect groups: C simulated annealing on connection sets, with exact fallbacks."""
import time

import lib


C_SOURCE = r'''
/* Haar graph search over groups G = Z_m x|_r Z_k of order N.
 * Haar graph H(G,S): a_g ~ b_{g s} for s in S, |S| = d. Left multiplication is an
 * automorphism, so the diameter is <= D iff BFS from a_e and from b_e reaches all
 * vertices within D. Simulated annealing on S minimises unreached counts.
 * Usage: prog d D seed time_limit nmin     (stdin ignored)
 * stdout: "n m" + edges of the best Haar graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1600
#define MAXD 16

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

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

static int GN, Gm, Gk, Gr;
static int rp[MAXG];
static int ca[MAXG], cb[MAXG];
static int mul[MAXG][MAXG];
static int inv_[MAXG];
static int S[MAXD];
static int bestS[MAXD], bestN = 0, bm, bk, br;
static int qu[2 * MAXG], dist_[2 * MAXG];

static void set_group(int m, int k, int r) {
    GN = m * k; Gm = m; Gk = k; Gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int y = 0; y < GN; y++) { ca[y] = y / k; cb[y] = y % k; }
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = ca[y], e = cb[y];
            mul[x][y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (mul[x][y] == 0) { inv_[x] = y; break; }
}

/* Reservoir-pick a uniform semidirect group Z_m x|_r Z_k of order N with m >= 2. */
static int pick_group(int N, int *pm, int *pk, int *pr) {
    long count = 0;
    for (int m = 2; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { *pm = m; *pk = k; *pr = r; }
        }
    }
    return count > 0;
}

static int unreached(int src) {
    int n2 = 2 * GN;
    for (int v = 0; v < n2; v++) dist_[v] = -1;
    int head = 0, tail = 0;
    qu[tail++] = src;
    dist_[src] = 0;
    while (head < tail) {
        int v = qu[head++];
        if (dist_[v] >= D) continue;
        int dv = dist_[v] + 1;
        if (v < GN) {
            for (int t = 0; t < d; t++) {
                int u = GN + mul[v][S[t]];
                if (dist_[u] < 0) { dist_[u] = dv; qu[tail++] = u; }
            }
        } else {
            int h = v - GN;
            for (int t = 0; t < d; t++) {
                int u = mul[h][inv_[S[t]]];
                if (dist_[u] < 0) { dist_[u] = dv; qu[tail++] = u; }
            }
        }
    }
    return n2 - tail;
}

static int inset(int x, int cnt) {
    for (int t = 0; t < cnt; t++)
        if (S[t] == x) return 1;
    return 0;
}

static int anneal(int iters, double tlim) {
    for (int t = 0; t < d; t++) {
        int x;
        do { x = rndint(GN); } while (inset(x, t));
        S[t] = x;
    }
    int cur = unreached(0) + unreached(GN);
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 511) == 0 && now() > tlim) break;
        int t = rndint(d), old = S[t], x;
        do { x = rndint(GN); } while (inset(x, d));
        S[t] = x;
        int c = unreached(0) + unreached(GN);
        double T = 1.5 * (1.0 - (double)it / iters) + 0.05;
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) cur = c;
        else S[t] = old;
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int nmin = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    if (nmin < d + 2) nmin = d + 2;
    if (nmin >= MAXG - 1) { printf("0 0\n"); return 0; }

    int start = nmin, cur = nmin, window = 60;
    while (now() < t_end) {
        if (cur >= MAXG - 1 || cur > start + window) cur = start;
        if (cur >= MAXG - 1) break;
        int m = 0, k = 0, r = 0;
        if (!pick_group(cur, &m, &k, &r)) { cur++; continue; }
        set_group(m, k, r);
        if (anneal(30000, t_end)) {
            bestN = cur;
            memcpy(bestS, S, sizeof(S));
            bm = m; bk = k; br = r;
            start = cur + 1;
            cur = start;
        } else {
            cur++;
        }
    }

    if (bestN > 0) {
        set_group(bm, bk, br);
        int N = bestN;
        printf("%d %d\n", 2 * N, N * d);
        for (int g = 0; g < N; g++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", g, N + mul[g][bestS[t]]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions (instant).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass

    # Main search: Haar graphs over semidirect groups, annealed in C.
    if D >= 2 and time.monotonic() < end - 1.0:
        moore = lib.moore_bound(d, D)
        nmin = max(d + 2, best[0] // 2 + 1, int(0.2 * moore / 2))
        budget = end - time.monotonic() - 0.5
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nmin],
                                 timeout=budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
