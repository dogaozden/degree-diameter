"""Cyclic Haar-lift search: bipartite graphs a_x ~ b_{x+s} for s in S (|S| = d, Z_m),
searched by simulated annealing in C with bitset-free reach counting. Vertex-transitivity
means checking the ball of a_0 suffices. Exact constructions (PG(2,q), Araujo-Pardo-Lopez)
and K_{d,d} are fallbacks. Every returned graph passes lib.is_valid.
"""
import time

import lib


C_SOURCE = r'''
/* Cyclic Haar-lift search.
 * Usage: prog d D seed time_limit m0
 * Graph: a_x (x in Z_m) joined to b_{(x+s) mod m} for s in S, |S| = d, distinct residues.
 * Diameter <= D iff the ball of a_0 contains all 2m vertices (translations and the
 * side-swapping automorphism make this sufficient).
 * Search: bisection on m with simulated annealing over S minimising unreached vertices.
 * stdout: "n m" + edges of the largest found lift, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 12000
#define MAXDEG 64

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static unsigned char RA[MAXM], RB[MAXM], NA[MAXM], NB[MAXM];
static int S[MAXDEG], Sbest[MAXDEG];

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

/* dst[y] |= src[(y - s) mod m] */
static void or_back(unsigned char *dst, const unsigned char *src, int m, int s) {
    for (int y = s; y < m; y++) dst[y] |= src[y - s];
    for (int y = 0; y < s; y++) dst[y] |= src[y - s + m];
}

/* dst[x] |= src[(x + s) mod m] */
static void or_fwd(unsigned char *dst, const unsigned char *src, int m, int s) {
    for (int x = 0; x < m - s; x++) dst[x] |= src[x + s];
    for (int x = m - s; x < m; x++) dst[x] |= src[x + s - m];
}

/* Number of vertices (of 2m) not within distance D of a_0. */
static int unreached(int m) {
    memset(RA, 0, (size_t)m);
    memset(RB, 0, (size_t)m);
    RA[0] = 1;
    for (int r = 0; r < D; r++) {
        memcpy(NA, RA, (size_t)m);
        memcpy(NB, RB, (size_t)m);
        for (int k = 0; k < d; k++) {
            or_back(NB, RA, m, S[k]);
            or_fwd(NA, RB, m, S[k]);
        }
        memcpy(RA, NA, (size_t)m);
        memcpy(RB, NB, (size_t)m);
    }
    int cnt = 0;
    for (int y = 0; y < m; y++) cnt += (RA[y] == 0) + (RB[y] == 0);
    return cnt;
}

static int taken(int v, int k) {
    for (int j = 0; j < d; j++)
        if (j != k && S[j] == v) return 1;
    return 0;
}

/* Try to find S with zero unreached for modulus m. Returns 1 and fills Sbest on success. */
static int search_m(int m, double until) {
    if (m < d || m > MAXM) return 0;
    for (int k = 0; k < d; k++) S[k] = -1 - k;
    for (int k = 0; k < d; k++) {
        int v;
        do { v = rndint(m); } while (taken(v, k));
        S[k] = v;
    }
    int cost = unreached(m);
    int bestc = cost;
    int Sloc[MAXDEG];
    memcpy(Sloc, S, sizeof(int) * (size_t)d);
    long it = 0;
    while (bestc > 0) {
        it++;
        if ((it & 31) == 0 && now() > until) break;
        int k = rndint(d);
        int old = S[k];
        int nv;
        if (rnd01() < 0.5) {
            int span = m / 20;
            if (span < 1) span = 1;
            int delta = 1 + rndint(span);
            if (rnd() & 1) delta = -delta;
            nv = old + delta;
            if (nv < 0) nv += m;
            if (nv >= m) nv -= m;
        } else {
            nv = rndint(m);
        }
        if (nv == old || taken(nv, k)) continue;
        S[k] = nv;
        int c2 = unreached(m);
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / 0.6)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                memcpy(Sloc, S, sizeof(int) * (size_t)d);
            }
        } else {
            S[k] = old;
        }
    }
    if (bestc == 0) {
        memcpy(Sbest, Sloc, sizeof(int) * (size_t)d);
        return 1;
    }
    return 0;
}

static void emit(int m) {
    printf("%d %d\n", 2 * m, m * d);
    for (int x = 0; x < m; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, m + (x + Sbest[k]) % m);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit m0\n");
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int m0 = atoi(argv[5]);
    double t_end = now() + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXDEG || D < 3) {
        printf("0 0\n");
        return 0;
    }

    int lo = 0, hi = 0, m = m0;
    if (m < d + 1) m = d + 1;
    if (m > MAXM) m = MAXM;
    while (1) {
        double rem = t_end - now();
        if (rem < 0.1) break;
        double slice = rem / 5.0;
        if (slice < 3.0) slice = 3.0;
        if (slice > rem) slice = rem;
        int ok = search_m(m, now() + slice);
        if (ok) lo = m;
        else if (hi == 0 || m < hi) hi = m;

        if (lo && hi) {
            if (hi - lo <= 1) break;
            m = lo + (hi - lo) / 2;
        } else if (!lo) {
            m = (int)(hi * 0.85);
        } else {
            if (lo >= MAXM) break;
            m = (int)(lo * 1.15) + 1;
            if (m > MAXM) m = MAXM;
        }
        if (m <= d) break;
    }
    if (lo) emit(lo);
    else printf("0 0\n");
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 2.0)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Cyclic Haar-lift search in C (only for D >= 3, where the search is meaningful).
    remaining = final - time.monotonic()
    if D >= 3 and d >= 3 and remaining > 1.0:
        m0 = max(d + 1, min(8000, int(0.2 * lib.moore_bound(d, D) / 2)))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), m0],
                             timeout=remaining + 5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
