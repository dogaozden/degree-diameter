import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over cyclic bi-Cayley (Haar) graphs.
#
# H(Z_m, S) has parts A = {a_i} and B = {b_j}, with a_i ~ b_{i+s} for s in S,
# |S| = DEG. Translations and the side swap a_i -> b_{-i}, b_j -> a_{-j} are
# automorphisms, so the diameter is <= DIAM iff a_0 reaches all of A and all of
# B within DIAM steps. The cost is the number of unreached vertices, found by a
# single BFS from a_0 (O(m * DEG) per evaluation). The program grows m by one
# whenever the cost reaches 0 and keeps the largest valid (m, S).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 4000
#define MAXD 40

static int DEG, DIAM, m;
static int S[MAXD];
static int inS[MAXM];
static int bestM;
static int bestS[MAXD];
static int stamp[2 * MAXM];
static int curStamp = 0;
static int queue_[2 * MAXM];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

/* Number of unreached vertices within DIAM steps of a_0 (0 iff valid). */
static long long eval_cost(void) {
    int reachedA = 1, reachedB = 0;
    int tail = 0;
    curStamp++;
    if (curStamp >= 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        curStamp = 1;
    }
    stamp[0] = curStamp;
    queue_[tail++] = 0;
    int ls = 0, le = 1;
    for (int r = 0; r < DIAM && ls < le; r++) {
        for (int qi = ls; qi < le; qi++) {
            int x = queue_[qi];
            if (x < m) {
                for (int t = 0; t < DEG; t++) {
                    int j = x + S[t];
                    if (j >= m) j -= m;
                    int y = m + j;
                    if (stamp[y] != curStamp) {
                        stamp[y] = curStamp;
                        queue_[tail++] = y;
                        reachedB++;
                    }
                }
            } else {
                int j = x - m;
                for (int t = 0; t < DEG; t++) {
                    int i = j - S[t];
                    if (i < 0) i += m;
                    if (stamp[i] != curStamp) {
                        stamp[i] = curStamp;
                        queue_[tail++] = i;
                        reachedA++;
                    }
                }
            }
        }
        ls = le;
        le = tail;
    }
    return (long long)(2 * m - reachedA - reachedB);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (DEG < 1 || DEG > MAXD || DIAM < 2 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    /* Start from K_{DEG,DEG}: m = DEG, S = all residues. */
    m = DEG;
    memset(inS, 0, sizeof inS);
    for (int t = 0; t < DEG; t++) {
        S[t] = t;
        inS[t] = 1;
    }
    bestM = m;
    for (int t = 0; t < DEG; t++) bestS[t] = S[t];

    long long cur = eval_cost();
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long long stall = 0, bestAtM = -1;

    while (1) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
        if (frac >= 1.0) break;

        if (cur == 0) {
            bestM = m;
            for (int t = 0; t < DEG; t++) bestS[t] = S[t];
            if (m + 1 >= MAXM) break;
            m++;
            cur = eval_cost();
            stall = 0;
            bestAtM = -1;
            continue;
        }
        if (m <= DEG) break;

        double T = 0.25 + 1.0 * (1.0 - frac);
        int t = rnd(DEG);
        int x;
        do {
            x = rnd(m);
        } while (inS[x]);
        int old = S[t];
        inS[old] = 0;
        S[t] = x;
        inS[x] = 1;
        long long c2 = eval_cost();
        long long dl = c2 - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur = c2;
        } else {
            inS[x] = 0;
            S[t] = old;
            inS[old] = 1;
        }

        if (bestAtM < 0 || cur < bestAtM) {
            bestAtM = cur;
            stall = 0;
        } else {
            stall++;
            long long lim = 2000 + 10LL * m;
            if (stall > lim) {
                for (int k = 0; k < 2; k++) {
                    int tt = rnd(DEG);
                    int xx;
                    do {
                        xx = rnd(m);
                    } while (inS[xx]);
                    inS[S[tt]] = 0;
                    S[tt] = xx;
                    inS[xx] = 1;
                }
                cur = eval_cost();
                stall = 0;
                bestAtM = -1;
            }
        }
    }

    int n = 2 * bestM;
    long long e = (long long)bestM * DEG;
    printf("%d %lld\n", n, e);
    for (int i = 0; i < bestM; i++) {
        for (int t = 0; t < DEG; t++) {
            int j = (i + bestS[t]) % bestM;
            printf("%d %d\n", i, bestM + j);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _haar_run(d, D, seed, budget):
    """Run the C Haar-graph annealer for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], timeout=budget + 6.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)

    # Trivial cases.
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d} (a Haar graph with m = d), valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3: projective planes and the Araujo-Pardo/Lopez extension when they apply.
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            consider(*lib.projective_plane_incidence(q))
        if d >= 5 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass

    # D >= 4 with small degree: generalized quadrangle W(q) as a cheap second candidate.
    if D >= 4 and d <= 11:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: cyclic bi-Cayley (Haar) graphs grown by annealing the connection set.
    remaining = 0.85 * tl - 2.0 - (time.monotonic() - start)
    if remaining >= 1.0:
        try:
            consider(*_haar_run(d, D, seed, remaining))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
