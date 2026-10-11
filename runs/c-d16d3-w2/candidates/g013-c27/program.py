import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: a different family for D >= 3.
#
# Cyclic Haar graph H(m, S) with |S| = d: vertices a_i, b_i (i in Z_m), and a_i
# is joined to b_{i+s} for s in S. It is d-regular and bipartite. If every
# nonzero residue is a difference s - s' (S - S = Z_m), then:
#   same side : a_i and a_j are at distance 2,
#   opposite  : offset j - i = s - s' + s'' for any s'' in S, so distance <= 3.
# So the diameter is at most 3 and the order is 2m. The problem becomes finding
# a d-subset of Z_m whose difference set covers Z_m, with m as large as possible.
# The Moore-type ceiling for this family is m <= d(d-1)+1.
#
# The C engine runs simulated annealing on S. The cost is the number of
# uncovered nonzero residues. It climbs m upward and keeps the largest m that
# succeeds. Python checks the output with lib.is_valid and keeps fallbacks.
# ----------------------------------------------------------------------------

DC_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 2048
#define ITERS 300000L

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int uncovered;
static double deadline;

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }
static int md(int x) { x %= M; if (x < 0) x += M; return x; }
static void inc_r(int r) { if (r == 0) return; if (cnt[r]++ == 0) uncovered--; }
static void dec_r(int r) { if (r == 0) return; if (--cnt[r] == 0) uncovered++; }

/* Replace S[i] by y (y must not be in S). Keeps cnt[] = ordered differences. */
static void replace_at(int i, int y) {
    int x = S[i];
    for (int j = 0; j < K; j++) if (j != i) { dec_r(md(x - S[j])); dec_r(md(S[j] - x)); }
    inS[x] = 0;
    S[i] = y; inS[y] = 1;
    for (int j = 0; j < K; j++) if (j != i) { inc_r(md(y - S[j])); inc_r(md(S[j] - y)); }
}

static int try_m(int mm) {
    M = mm;
    memset(inS, 0, sizeof(inS));
    memset(cnt, 0, sizeof(cnt));
    uncovered = M - 1;
    int c = 0;
    while (c < K) {
        int y = rndi(M);
        if (!inS[y]) { inS[y] = 1; S[c++] = y; }
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) inc_r(md(S[i] - S[j]));
    for (long it = 0; it < ITERS; it++) {
        if (uncovered == 0) return 1;
        if ((it & 4095) == 0 && now() > deadline) return 0;
        double T = pow(0.1, (double)it / (double)ITERS);   /* 1.0 -> 0.1 */
        int i = rndi(K);
        int y;
        do { y = rndi(M); } while (inS[y]);
        int x = S[i];
        int old = uncovered;
        replace_at(i, y);
        int delta = uncovered - old;
        if (delta <= 0 || rndu() < exp(-delta / T)) continue;
        replace_at(i, x);
    }
    return uncovered == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    int mlo = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    if (K < 2 || K > MAXK) { printf("0 0\n"); return 0; }
    if (mlo < K + 1) mlo = K + 1;
    int mcap = K * (K - 1) + 1;
    if (mcap > MAXM - 1) mcap = MAXM - 1;
    deadline = budget;

    int bestM = 0;
    int bestS[MAXK];
    for (int mm = mlo; mm <= mcap; mm++) {
        int ok = 0;
        while (now() < deadline) {
            if (try_m(mm)) { ok = 1; break; }
        }
        if (!ok) break;
        bestM = mm;
        memcpy(bestS, S, sizeof(int) * K);
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    int n = 2 * bestM;
    long m = (long)bestM * K;
    printf("%d %ld\n", n, m);
    for (int i = 0; i < bestM; i++)
        for (int j = 0; j < K; j++)
            printf("%d %d\n", i, bestM + (i + bestS[j]) % bestM);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions kept from the parent as alternative starts.
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


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   Every case: K_{d,d} (diameter 2) is the always-valid fallback.
#   D == 3   : arc-extended projective plane graph (parent construction).
#   D == 4   : generalized quadrangle W(q).
#   D >= 3   : cyclic Haar graph H(m, S) found by the C difference-cover search,
#              which has diameter <= 3 and is valid for any D >= 3.
# Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    def elapsed():
        return time.monotonic() - start

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        try:
            n, e = g
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    try:
        if D == 3:
            for g in _arc_extensions(d, start + 0.10 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    # Main new search: difference-covering Haar graph, C engine.
    budget = 0.85 * time_limit - elapsed() - 1.5
    if D >= 3 and budget >= 1.0:
        try:
            out = lib.run_c(DC_SOURCE, [d, d + 1, seed, round(budget, 2)],
                            timeout=budget + 8.0)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
