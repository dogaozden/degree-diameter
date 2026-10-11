"""Haar-graph difference-cover search for D = 3, with the conic blow-up as the fallback.

Construction: for d and m, the Haar graph H(m, S) has parts a_i and b_j (i, j in Z_m) with
a_i ~ b_{i+s} for s in S, |S| = d. It is d-regular and bipartite. Its diameter is at most 3
exactly when every nonzero residue of Z_m is a difference s - t with s, t in S (a difference
cover). Order 2m, so m >= d(d-1)/... beats a record of 2m_0 when m > m_0. The C engine
anneals S (with 0 fixed in S) to cover all residues for each m in a range, and reports the
largest m it covers.

Structured starts (projective planes, Araujo-Pardo-Lopez, conic blow-up) remain the fallback.
Every output is checked with lib.is_valid before it is accepted.
"""
import time

import lib

C_SOURCE = r'''
/* Difference-cover search for Haar graphs H(m, S), D = 3.
 * Usage: prog d D seed time_limit mlo
 * Finds, for m = mlo .. d(d-1)+1, a d-set S in Z_m (0 in S) whose differences cover Z_m,
 * by simulated annealing. Prints the Haar graph for the largest m found, or "0 0".
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 40
#define MAXM 1100

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int d, m;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];      /* cnt[x]: ordered pairs (s, t), s != t, with s - t = x */
static int uncovered;      /* residues 1..m-1 with cnt == 0 */

static void apply(int x, int delta) {
    x %= m;
    if (x < 0) x += m;
    if (x == 0) return;
    if (delta > 0) {
        if (cnt[x] == 0) uncovered--;
        cnt[x]++;
    } else {
        cnt[x]--;
        if (cnt[x] == 0) uncovered++;
    }
}

/* Add (sign=+1) or remove (sign=-1) all ordered differences involving element i. */
static void place(int i, int sign) {
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        apply(S[i] - S[j], sign);
        apply(S[j] - S[i], sign);
    }
}

static int anneal(long L, double until) {
    memset(inS, 0, sizeof(int) * (size_t)m);
    memset(cnt, 0, sizeof(int) * (size_t)m);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int w;
        do { w = 1 + rndint(m - 1); } while (inS[w]);
        S[i] = w;
        inS[w] = 1;
    }
    uncovered = m - 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (j != i) apply(S[i] - S[j], +1);

    const double T0 = 1.2, T1 = 0.02;
    const double lg = log(T1 / T0);
    for (long it = 0; it < L; it++) {
        if (uncovered == 0) return 1;
        if ((it & 255) == 0 && now() > until) return 0;
        double T = T0 * exp(lg * ((double)it / (double)L));
        int i = 1 + rndint(d - 1);
        int w = 1 + rndint(m - 1);
        if (inS[w]) continue;
        int v = S[i];
        int before = uncovered;
        place(i, -1);
        S[i] = w;
        place(i, +1);
        int delta = uncovered - before;
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            inS[v] = 0;
            inS[w] = 1;
        } else {
            place(i, -1);
            S[i] = v;
            place(i, +1);
        }
    }
    return uncovered == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit mlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mlo = atoi(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 3 || d > MAXK) { printf("0 0\n"); return 0; }
    double t0 = now();
    double tend = t0 + limit * 0.9;
    int mhi = d * (d - 1) + 1;
    if (mhi > MAXM - 1) mhi = MAXM - 1;
    if (mlo < d + 1) mlo = d + 1;

    int bestm = 0;
    int bestS[MAXK];
    for (int mm = mlo; mm <= mhi; mm++) {
        double left = tend - now();
        if (left <= 0) break;
        int remaining = mhi - mm + 1;
        double until = now() + left / remaining;
        if (until > tend) until = tend;
        m = mm;
        int ok = 0;
        while (!ok && now() < until) ok = anneal(200000L, until);
        if (ok) {
            bestm = mm;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
    }

    if (bestm == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestm, bestm * d);
    for (int i = 0; i < bestm; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, bestm + (i + bestS[k]) % bestm);
    return 0;
}
'''

HAAR_CAP = 45.0   # seconds of C search at most


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def conic_blowup(d, D):
    """Twin-blow-up of PG(2,q) with q = d-3 odd, using a conic and a dual conic.

    Gives 2(q^2+q+1) + 2(q+1) vertices, which is 394 for q = 13 (d = 16).
    """
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def starts(d, D):
    """Candidate structured start graphs (validity is checked by the caller)."""
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    best = None
    for cand in starts(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (best is None or cand[0] > best[0]):
            best = cand
    if best is None:
        best = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2

    if D == 3 and best[0] < lib.moore_bound(d, D):
        left = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
        budget = min(HAAR_CAP, 0.9 * left)
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, budget, best[0] // 2 + 1],
                                 stdin_graph=None, timeout=budget + 8)
                n, edges = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
            except Exception:
                pass   # keep the valid structured fallback
    return best
