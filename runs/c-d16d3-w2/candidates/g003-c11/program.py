import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic / Z2 x Z_k "difference cover" search for Haar graphs.
#
# Haar graph H(G, S): a_x ~ b_{x+s} for s in S, |S| = d, G abelian of order M.
# If S - S = G then every two a-vertices (and every two b-vertices) are at
# distance <= 2, and every a_x, b_y are at distance <= 3 (y - x = (s1 - s2) + s3).
# So H(G, S) is bipartite, d-regular, diameter 3, with 2M vertices, and needs
# M <= d(d-1)+1. The search anneals S (0 fixed, WLOG) to minimise the number of
# uncovered nonzero group elements.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXM 2048

static int d, m1, m2, M;
static int S[MAXD];
static int inS[MAXM];
static int cnt[MAXM];
static int unc;
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 32);
}

static double urand(void) { return rnd() / 4294967296.0; }

static double elapsed_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int gadd(int x, int y) {
    int a = x / m2 + y / m2;
    if (a >= m1) a -= m1;
    int b = x % m2 + y % m2;
    if (b >= m2) b -= m2;
    return a * m2 + b;
}

static int gneg(int x) {
    int a = x / m2, b = x % m2;
    return ((m1 - a) % m1) * m2 + ((m2 - b) % m2);
}

static int gsub(int x, int y) { return gadd(x, gneg(y)); }

static void dec_(int g) { if (--cnt[g] == 0) unc++; }
static void inc_(int g) { if (cnt[g]++ == 0) unc--; }

static void replace_(int i, int x) {
    int s = S[i];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        dec_(gsub(s, S[j]));
        dec_(gsub(S[j], s));
    }
    inS[s] = 0;
    S[i] = x;
    inS[x] = 1;
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        inc_(gsub(x, S[j]));
        inc_(gsub(S[j], x));
    }
}

static void init_random(void) {
    for (int g = 0; g < M; g++) { inS[g] = 0; cnt[g] = 0; }
    unc = M - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int x;
        do { x = (int)(rnd() % (uint32_t)M); } while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) inc_(gsub(S[i], S[j]));
}

/* Returns 1 with S a full difference cover, 0 if the time end is reached. */
static int anneal(double end) {
    while (elapsed_s() < end) {
        init_random();
        const long RUN = 200000;
        double T = 1.0;
        for (long it = 0; it < RUN; it++) {
            if ((it & 511) == 0) {
                if (elapsed_s() >= end) return 0;
                double frac = (double)it / (double)RUN;
                T = 1.5 * pow(0.02 / 1.5, frac);
            }
            int i = 1 + (int)(rnd() % (uint32_t)(d - 1));
            int x = (int)(rnd() % (uint32_t)M);
            if (inS[x]) continue;
            int old = S[i];
            int before = unc;
            replace_(i, x);
            int delta = unc - before;
            if (delta <= 0 || urand() < exp(-(double)delta / T)) {
                if (unc == 0) return 1;
            } else {
                replace_(i, old);
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int mlo = atoi(argv[5]), mhi = atoi(argv[6]);
    if (d < 2 || d > MAXD || D < 3 || mlo < 2 || mhi < mlo) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int k = 0; k < 10; k++) rnd();

    double end = elapsed_s() + budget;
    int nm = mhi - mlo + 1;
    int found = 0, fm1 = 0, fm2 = 0, fM = 0;
    int fS[MAXD];

    for (int m = mlo; m <= mhi && elapsed_s() < end; m++) {
        if (m <= d || m >= MAXM) continue;
        int shapes = (m % 2 == 0 && m / 2 >= 2) ? 2 : 1;
        for (int sh = 0; sh < shapes; sh++) {
            if (sh == 0) { m1 = m; m2 = 1; }
            else { m1 = m / 2; m2 = 2; }
            M = m;
            double slice_end = elapsed_s() + budget / (double)nm / (double)shapes;
            if (slice_end > end) slice_end = end;
            if (anneal(slice_end)) {
                found = 1;
                fm1 = m1; fm2 = m2; fM = M;
                memcpy(fS, S, sizeof(int) * (size_t)d);
                break;
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    m1 = fm1; m2 = fm2; M = fM;
    memcpy(S, fS, sizeof(int) * (size_t)d);
    printf("%d %d\n", 2 * M, M * d);
    for (int x = 0; x < M; x++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", x, M + gadd(x, S[j]));
    return 0;
}
"""


def _haar_search(d, D, seed, budget, mlo, mhi):
    """Run the difference-cover search; return (n, edges) of a valid Haar graph or None."""
    if mhi < mlo or d < 3 or D < 3 or budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mlo, mhi],
                        stdin_graph=None, timeout=budget + 10.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 2:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. Each old vertex has degree q+1, spare s = d-q-1.
# New A-vertices sit on sets of points SA (each line holds <= s points of SA),
# new B-vertices on sets of lines SB (each point lies on <= s lines of SB).
# For s = 2 the optimum is a conic (an arc), giving 2(q^2+2q+2) for d = q+3.
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
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   0.00-0.12  arc-extended PG graphs (conic sets for spare degree >= 2)
#   0.12-0.20  generalized quadrangle baseline (D >= 4 only)
#   0.20-0.85  difference-cover Haar search for orders above the current best
# Every candidate passes lib.is_valid before it replaces the incumbent.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def elapsed():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is bipartite with diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.12 * time_limit, random.Random(seed * 7919 + d))
        for g in sorted(arcs, key=lambda t: -t[0]):
            consider(g)

    if D >= 4 and elapsed() < 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if D >= 3:
        mlo = best[0] // 2 + 1          # Haar graph of order 2M beats the incumbent iff M > n/2
        mhi = d * (d - 1) + 1           # Moore-type limit for difference covers
        rem = 0.85 * time_limit - elapsed()
        if rem > 1.0:
            consider(_haar_search(d, D, seed, rem, mlo, mhi))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
