import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold new construction: cyclic Haar graphs from difference covers.
#
# H(Z_m, S) has parts A = {a_i} and B = {b_j}, with a_i ~ b_{i+s} for s in S.
# If |S| = d then every vertex has degree d. If S - S = Z_m (a difference cover),
# then:
#   A to A and B to B: a_i - b_{i+s} - a_{i+s-t} reaches any difference in S - S, so distance <= 2;
#   A to B: S - S + S contains S - S + s for any fixed s, which is all of Z_m, so distance <= 3.
# Hence diameter 3 with order 2m. A perfect difference set would give m = d^2 - d + 1,
# which is the Moore-type ceiling. The C engine searches for the largest m by simulated
# annealing on the number of uncovered nonzero residues.
#
# Fallbacks: K_{d,d} (diameter 2) and the Araujo-style arc-extended PG(2,q) graphs
# (diameter 3). Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXK 64
#define MAXM 4096

static uint64_t rs = 88172645463325252ULL;

static uint64_t xr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(xr() % (uint64_t)n); }

static double urand(void) {
    return (double)(xr() >> 11) * (1.0 / 9007199254740992.0);
}

static double cpu_now(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int K, M;
static int S[MAXK];
static unsigned char inS[MAXM];
static int cnt[MAXM];
static int uncovered;   /* number of x in 1..M-1 with cnt[x] == 0 */

/* Add delta (+1 or -1) for the unordered pair {a, b}, a != b mod M.
   Both a-b and b-a are counted. */
static void pair_update(int a, int b, int delta) {
    int x = a - b;
    if (x < 0) x += M;
    int y = M - x;
    if (delta > 0) {
        if (cnt[x]++ == 0) uncovered--;
        if (cnt[y]++ == 0) uncovered--;
    } else {
        if (--cnt[x] == 0) uncovered++;
        if (--cnt[y] == 0) uncovered++;
    }
}

static void remove_elem(int i) {
    for (int j = 0; j < K; j++)
        if (j != i) pair_update(S[i], S[j], -1);
}

static void add_elem(int i) {
    for (int j = 0; j < K; j++)
        if (j != i) pair_update(S[i], S[j], 1);
}

/* Search for a K-subset of Z_m whose difference set covers all nonzero residues. */
static int try_m(int m, int k, double seconds, int *outS) {
    M = m;
    K = k;
    memset(cnt, 0, sizeof(int) * (size_t)m);
    memset(inS, 0, (size_t)m);
    uncovered = m - 1;
    for (int i = 0; i < k; i++) {
        int v;
        do {
            v = rint_(m);
        } while (inS[v]);
        S[i] = v;
        inS[v] = 1;
    }
    for (int i = 0; i < k; i++)
        for (int j = i + 1; j < k; j++)
            pair_update(S[i], S[j], 1);

    double tstart = cpu_now();
    double T = 1.0;
    long long it = 0;
    while (uncovered > 0) {
        if ((it & 4095LL) == 0 && cpu_now() - tstart > seconds) return 0;
        it++;
        if (it % 3000000LL == 0) T = 1.0;
        T *= 0.999999;
        if (T < 0.12) T = 0.12;

        int i = rint_(K);
        int v = rint_(M);
        if (inS[v]) continue;
        int old = S[i];
        int before = uncovered;
        remove_elem(i);
        inS[old] = 0;
        S[i] = v;
        inS[v] = 1;
        add_elem(i);
        int delta = uncovered - before;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) continue;
        /* reject: revert the move */
        remove_elem(i);
        inS[v] = 0;
        S[i] = old;
        inS[old] = 1;
        add_elem(i);
    }
    memcpy(outS, S, sizeof(int) * (size_t)K);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) xr();

    if (d < 1 || d > MAXK || D < 3) {
        printf("0 0\n");
        return 0;
    }
    double start = cpu_now();
    int k = d;
    int maxm = k * (k - 1) + 1;
    int best_m = 0;
    int bestS[MAXK];
    int tmpS[MAXK];
    int target = k;
    while (target <= maxm && target < MAXM) {
        double remain = tl - (cpu_now() - start);
        if (remain < 0.05) break;
        double slice = remain < 5.0 ? remain : 5.0;
        if (try_m(target, k, slice, tmpS)) {
            best_m = target;
            memcpy(bestS, tmpS, sizeof(int) * (size_t)k);
            target++;
        }
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    int m = best_m;
    printf("%d %d\n", 2 * m, m * k);
    for (int a = 0; a < m; a++)
        for (int t = 0; t < k; t++)
            printf("%d %d\n", a, m + (a + bestS[t]) % m);
    return 0;
}
"""


def _haar_candidate(d, D, seed, budget):
    """Run the C difference-cover search. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=None,
                        timeout=budget + 1.5)
        n, edges = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n < 2 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3), kept as a fallback.
# ----------------------------------------------------------------------------

def _pg(q):
    """Incidence data for PG(2, q): points and lines are indexed 0..m-1 by the same vectors."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a set of point indices."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus a new A-vertex per P in S (joined to lines through P) and a
    new B-vertex per j in S (joined to points on line j)."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        for L in point_lines[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in line_points[j]:
            E.append((Q, 2 * m + k + t))
    return 2 * m + 2 * k, E


def _arc_candidates(d, deadline, rng):
    """List of (n, edges) arc-extended graphs, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        if cand is None:
            return
        n, e = cand
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        end = t0 + 0.8 * time_limit - 0.5
        rng = random.Random(seed * 7919 + d)
        for cand in _arc_candidates(d, t0 + 0.2 * time_limit, rng):
            consider(cand)
        budget = max(0.2, end - time.monotonic() - 1.0)
        consider(_haar_candidate(d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
