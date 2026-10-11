import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D = 3: cyclic Haar graphs from difference covers.
#
# H(Z_m, S) with |S| = d has parts A = {a_i}, B = {b_j}, and a_i ~ b_j iff
# j - i is in S. It is bipartite and d-regular. Its diameter is at most 3
# exactly when S - S covers every residue of Z_m: a-a and b-b pairs need a
# difference in S - S at distance 2, and a-b pairs are then within 3 because
# S - S + S = Z_m. So the search is: find the largest m for which a d-subset of
# Z_m covers all nonzero differences. The order is 2m, and m can exceed the
# projective-plane based record.
#
# The C engine is simulated annealing on S. The cost is the number of uncovered
# nonzero residues, and each move costs O(d).
# ----------------------------------------------------------------------------

C_COVER = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 4096

static int m, k;
static int S[MAXK];
static unsigned char inS[MAXM];
static int cnt[MAXM];
static int uncov;
static uint64_t rs = 0x2545F4914F6CDD1DULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static inline int dif(int a, int b) { int r = a - b; return r < 0 ? r + m : r; }

static inline void addc(int r) { if (cnt[r] == 0) uncov--; cnt[r]++; }
static inline void subc(int r) { cnt[r]--; if (cnt[r] == 0) uncov++; }

/* add (sign > 0) or remove (sign < 0) all ordered differences between x and S[t], t != skip */
static void apply_pairs(int x, int skip, int sign) {
    for (int t = 0; t < k; t++) {
        if (t == skip) continue;
        int y = S[t];
        if (sign > 0) { addc(dif(x, y)); addc(dif(y, x)); }
        else { subc(dif(x, y)); subc(dif(y, x)); }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    k = atoi(argv[1]);
    m = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    if (k < 1 || k > MAXK || m <= k || m > MAXM - 1) { printf("FAIL\n"); return 0; }

    memset(inS, 0, sizeof(inS));
    for (int i = 0; i < k; i++) {
        int x;
        do x = rndi(m); while (inS[x]);
        inS[x] = 1;
        S[i] = x;
    }
    memset(cnt, 0, sizeof(int) * (size_t)m);
    uncov = m - 1;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            if (i != j) addc(dif(S[i], S[j]));

    clock_t t0 = clock();
    const double T0 = 1.5, T1 = 0.05;
    const long P = 300000;
    long it = 0;
    int found = 0;
    while (1) {
        if (uncov == 0) { found = 1; break; }
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        double frac = (double)(it % P) / (double)P;
        double T = T0 * pow(T1 / T0, frac);
        int i = rndi(k);
        int x;
        do x = rndi(m); while (inS[x]);
        int s = S[i];
        int before = uncov;
        apply_pairs(s, i, -1);
        S[i] = x;
        apply_pairs(x, i, +1);
        int delta = uncov - before;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            inS[s] = 0;
            inS[x] = 1;
        } else {
            apply_pairs(x, i, -1);
            S[i] = s;
            apply_pairs(s, i, +1);
        }
    }

    if (found) {
        printf("OK %d\n", m);
        for (int i = 0; i < k; i++) printf("%d ", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


def _c_cover(k, m, seed, budget):
    """Run the covering search for (k, m); return the set S or None."""
    try:
        out = lib.run_c(C_COVER, [k, m, seed, round(budget, 2)],
                        stdin_graph=None, timeout=budget + 6.0)
    except Exception:
        return None
    toks = out.split()
    if len(toks) < 2 + k or toks[0] != "OK":
        return None
    try:
        S = [int(x) for x in toks[2:2 + k]]
    except ValueError:
        return None
    if len(set(S)) != k or any(not (0 <= x < m) for x in S):
        return None
    return S


def _haar_search(k, seed, deadline):
    """Largest m found (scanning upward from a start guess) with a k-set covering Z_m differences."""
    if k < 2:
        return None
    m = max(k + 1, int(0.7 * k * k))
    best = None
    fails = 0
    tries = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        budget = min(remaining - 0.2, max(1.0, 0.35 * remaining))
        tries += 1
        S = _c_cover(k, m, seed * 1000003 + tries, budget)
        if S is None:
            fails += 1
            if fails >= 2:
                break
            continue
        fails = 0
        best = (m, S)
        m += 1
    if best is None:
        return None
    return lib.haar_graph(best[0], best[1])


# ----------------------------------------------------------------------------
# Projective-plane arc extension (earlier D = 3 construction, kept as a second
# candidate so the result never falls below the previous record path).
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
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit at most s times."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
    """Return (n, edges) candidates from PG(2, q) plus arc-extension vertices, q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
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
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: best valid of (difference-cover Haar graph, arc-extended PG graph).
#   otherwise: K_{d,d} (diameter 2), which is valid for any D >= 2.
# Every candidate is checked with lib.is_valid, and K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, always valid for D >= 2

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        try:
            for g in _arc_extensions(d, start + 0.2 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        except Exception:
            pass
        try:
            consider(_haar_search(d, seed, start + 0.85 * time_limit))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
