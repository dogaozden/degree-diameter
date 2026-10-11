"""Cyclic bi-Cayley (Haar) search for diameter 3, with an arc-extended PG(2,q) fallback.

New construction: the Haar graph H(Z_m, S) has parts a_i and b_j, with a_i adjacent to
b_{i+s} for s in S. It is |S|-regular and bipartite. It has diameter <= 3 exactly when
  (A) every nonzero residue is a difference s - t (s != t in S), and
  (B) every residue is in S or of the form s - t + u (s, t, u in S).
Both conditions are checked by the C annealer, which searches S for the largest m that works.
For d = 3 this gives the Heawood graph (m = 7, n = 14). For d = 16 the upper bound is m <= 241.

Fallback: the arc-extended PG(2,q) construction for D >= 3, then K_{d,d}. The C search covers
D = 3 only. D >= 4 falls back to the arc construction, which is weaker than the older generalized
quadrangle path.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXM 8192
#define MAXK 128

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int K, M;
static int S[MAXK];
static unsigned char mark[MAXM];
static unsigned char covA[MAXM], covB[MAXM];

/* Number of uncovered residues for conditions (A) and (B). Zero means diameter <= 3. */
static int cost(void) {
    int i, j, a, b, c, ua = 0, ub = 0;
    for (i = 0; i < M; i++) { covA[i] = 0; covB[i] = 0; }
    for (i = 0; i < K; i++)
        for (j = 0; j < K; j++)
            if (i != j) {
                int x = (S[i] - S[j]) % M;
                if (x < 0) x += M;
                covA[x] = 1;
            }
    for (i = 1; i < M; i++) if (!covA[i]) ua++;
    for (i = 0; i < K; i++) covB[S[i]] = 1;
    for (a = 0; a < K; a++)
        for (b = 0; b < K; b++)
            for (c = 0; c < K; c++) {
                int x = (S[a] - S[b] + S[c]) % M;
                if (x < 0) x += M;
                covB[x] = 1;
            }
    for (i = 0; i < M; i++) if (!covB[i]) ub++;
    return ua + ub;
}

/* Simulated annealing on S (S[0] = 0 fixed, WLOG by translation) within a time slice. */
static int anneal(int m, double slice, int *out) {
    int i;
    M = m;
    double start = now(), end = start + slice;
    for (i = 0; i < M; i++) mark[i] = 0;
    S[0] = 0;
    mark[0] = 1;
    for (i = 1; i < K; i++) {
        int r;
        do { r = rndint(M); } while (mark[r]);
        S[i] = r;
        mark[r] = 1;
    }
    int cur = cost();
    double T = 1.0;
    long it = 0;
    while (cur > 0) {
        if ((it & 127) == 0) {
            double t = now();
            if (t >= end) break;
            double frac = (t - start) / slice;
            T = 0.15 + (1.0 - frac);
        }
        it++;
        int idx = 1 + rndint(K - 1);
        int old = S[idx], nv;
        do { nv = rndint(M); } while (mark[nv]);
        S[idx] = nv;
        mark[old] = 0;
        mark[nv] = 1;
        int nc = cost();
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            mark[nv] = 0;
            mark[old] = 1;
            S[idx] = old;
        }
    }
    if (cur == 0) {
        for (i = 0; i < K; i++) out[i] = S[i];
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    unsigned long long seed = (unsigned long long)atoll(argv[3]);
    double tl = atof(argv[4]);
    K = d;
    if (K < 3 || K > MAXK) { printf("0 0\n"); return 0; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    double t0 = now();
    long bound = (long)K * (K - 1) + 1;
    long mm = (long)(0.8 * (double)bound);
    if (mm < K + 1) mm = K + 1;
    if (mm > MAXM - 1) mm = MAXM - 1;
    int m = (int)mm;

    int bestM = 0;
    int bestS[MAXK];
    int work[MAXK];
    int fails = 0;
    while (1) {
        double rem = tl - (now() - t0);
        if (rem < 0.1) break;
        if (m < K + 1 || m > MAXM - 1) break;
        double slice = rem * 0.15;
        if (slice > rem) slice = rem;
        if (slice < 0.05) slice = 0.05;
        int ok = anneal(m, slice, work);
        if (ok) {
            bestM = m;
            memcpy(bestS, work, sizeof(int) * (size_t)K);
            fails = 0;
            m++;
        } else {
            fails++;
            if (bestM == 0) {
                m--;               /* still descending to the first feasible m */
            } else if (fails >= 2) {
                break;             /* two failures in a row above the best: stop */
            }
        }
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    long edges = (long)bestM * K;
    printf("%d %ld\n", 2 * bestM, edges);
    for (int i = 0; i < bestM; i++)
        for (int k = 0; k < K; k++) {
            int s = bestS[k];
            printf("%d %d\n", i, bestM + (i + s) % bestM);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane fallback (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit by <= s of them."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


def _fallback(d, D, deadline, seed):
    """Best of the arc-extended PG graphs that fit the deadline, or K_{d,d}."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                break
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _haar_search(d, D, budget, seed):
    """Run the C difference-set annealer; return (n, edges) of the best Haar graph it found."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=None, timeout=budget + 3.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d, D, t0 + 0.1 * time_limit, seed)
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    if D == 3 and d >= 3:
        remaining = time_limit - (time.monotonic() - t0)
        budget = max(0.5, min(0.85 * remaining - 1.0, remaining - 4.0))
        try:
            n2, e2 = _haar_search(d, D, budget, seed)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
