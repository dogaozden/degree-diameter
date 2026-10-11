"""Difference-cover Haar search for D = 3, with a verified algebraic fallback.

Bold change: instead of growing the Araujo-Pardo/Lopez graph, search for a bipartite
Haar graph H(m, S) on Z_m. Vertices are a_i and b_j, and a_i ~ b_{i+s} for s in S, with
|S| = d. If S - S covers all of Z_m, the graph has diameter 3, so 2m vertices are possible
for any m with the covering property. Moore bound: m <= d^2 - d + 1. C runs simulated
annealing on S to cover every nonzero difference, trying m = m_min, m_min+1, ... where
m_min is half the fallback order plus one.

Python first builds the best algebraic start (projective plane or Araujo-Pardo/Lopez),
checks it with lib.is_valid, and keeps it as the answer. The C result replaces it only if
it is larger and passes lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Difference-cover search for bipartite Haar graphs of diameter 3.
 *
 * Usage:  prog d D seed time_limit m_min
 * Output: "n m" then edges, for the Haar graph H(M, S) with M >= m_min, or "0 0".
 *
 * A bipartite Haar graph H(M, S) with |S| = d on vertices a_i, b_j (i, j in Z_M) has
 * edges a_i - b_{i+s}. If every nonzero residue is a difference s - t (s, t in S), it
 * has diameter 3. Simulated annealing minimises the number of uncovered differences.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64
#define MAXM 4096

static int d;
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

static int M;
static int S[MAXD];
static int cnt[MAXM];   /* cnt[r] = ordered pairs (i != j) with S[i] - S[j] = r mod M */
static int uncovered;   /* number of r in 1..M-1 with cnt[r] == 0 */

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void addpair(int r, int delta) {
    if (r == 0) return;
    if (delta > 0) {
        if (cnt[r] == 0) uncovered--;
        cnt[r]++;
    } else {
        cnt[r]--;
        if (cnt[r] == 0) uncovered++;
    }
}

/* Add or remove all ordered pairs that involve index k. */
static void touch(int k, int delta) {
    for (int j = 0; j < d; j++) {
        if (j == k) continue;
        addpair(md(S[k] - S[j]), delta);
        addpair(md(S[j] - S[k]), delta);
    }
}

/* Is x equal to S[j] for some j != k? */
static int dup(int x, int k) {
    for (int j = 0; j < d; j++)
        if (j != k && S[j] == x) return 1;
    return 0;
}

/* Is x equal to S[j] for some j < i? */
static int dup_upto(int x, int i) {
    for (int j = 0; j < i; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Search for a d-subset S of Z_m (with 0 in S) covering all nonzero differences.
 * Returns 1 with S filled in on success, 0 if the deadline passes first. */
static int search_m(int m, double until) {
    M = m;
    memset(cnt, 0, sizeof(int) * (size_t)m);
    uncovered = m - 1;
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int x;
        do {
            x = rndint(m);
        } while (dup_upto(x, i));
        S[i] = x;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) addpair(md(S[i] - S[j]), 1);

    double T = 1.0;
    long it = 0;
    while (uncovered > 0) {
        if ((++it & 1023) == 0 && now() > until) return 0;
        int k = 1 + rndint(d - 1);
        int x = rndint(m);
        if (dup(x, k)) continue;
        int old = S[k];
        int before = uncovered;
        touch(k, -1);
        S[k] = x;
        touch(k, 1);
        int delta = uncovered - before;
        if (!(delta <= 0 || rnd01() < exp(-(double)delta / T))) {
            touch(k, -1);
            S[k] = old;
            touch(k, 1);
        }
        T *= 0.9995;
        if (T < 0.03) T = 1.0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mmin = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 3 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    int mmax = d * d - d + 1;      /* Moore-type limit for diameter 3 */
    if (mmax > MAXM) mmax = MAXM;
    if (mmin < d) mmin = d;

    static int bestS[MAXD];
    int bestM = 0;
    int m = mmin;
    while (m <= mmax && now() < t_end) {
        if (!search_m(m, t_end)) break;
        bestM = m;
        memcpy(bestS, S, sizeof(int) * (size_t)d);
        m++;
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * bestM, bestM * d);
    for (int i = 0; i < bestM; i++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", i, bestM + (i + bestS[j]) % bestM);
    return 0;
}
'''


def _projective_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (q >= 2)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def known_starts(d, D):
    """Valid algebraic constructions for (d, D) that Python can build directly."""
    out = [lib.haar_graph(d, range(d))]          # K_{d,d}: diameter 2, always valid
    if D == 3 and d >= 3:
        if lib.is_prime_power(d - 1):
            out.append(lib.projective_plane_incidence(d - 1))   # Moore graph
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            out.append(lib.araujo_lopez_graph(d - 2))            # record family 2(q^2+q+5)
        base = _projective_base(d)
        if base is not None:
            out.append(base)
    return out


def _fallback(d, D):
    """Largest algebraic construction that passes lib.is_valid."""
    for n, e in sorted(known_starts(d, D), key=lambda c: -c[0]):
        try:
            if lib.is_valid(n, e, d, D):
                return (n, e)
        except Exception:
            continue
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = _fallback(d, D)

    # Bold branch: difference-cover Haar graphs for D = 3.
    if D == 3 and d >= 4 and best[0] < lib.moore_bound(d, D):
        m_min = best[0] // 2 + 1
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
        if budget > 0.5:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), m_min],
                                 stdin_graph=None, timeout=budget + 5)
                n, e = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except Exception:
                pass   # keep the verified algebraic construction

    return best
