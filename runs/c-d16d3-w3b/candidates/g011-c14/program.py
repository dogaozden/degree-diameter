import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar graphs (bi-Cayley graphs over Z_N).
#
# Vertices a_i = i and b_j = N + j, with a_i ~ b_{i+s} for every shift s in S,
# |S| = d. Z_N acts transitively on each side, so checking the distances from
# a_0 and b_0 is enough to decide whether the diameter is <= D. For D = 3 this
# reduces to S - S = Z_N.
#
# The engine searches for a shift set S that reaches all vertices within D,
# and grows N by one each time it succeeds, carrying S over to the next N.
# It prints the largest valid Haar graph it found ("0 0" if none).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXN 2000

static int d, D, N;
static int S[MAXD];
static int bestS[MAXD];
static int bestN = 0;
static uint64_t rs = 1;
static int dist[2 * MAXN];
static int que[2 * MAXN];

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int in_prefix(int x, int cnt) {
    for (int k = 0; k < cnt; k++) if (S[k] == x) return 1;
    return 0;
}

/* Number of vertices (both sides) at distance > D from src. */
static int bad_from(int src) {
    int total = 2 * N;
    for (int v = 0; v < total; v++) dist[v] = -1;
    int qh = 0, qt = 0, reached = 1;
    dist[src] = 0;
    que[qt++] = src;
    while (qh < qt) {
        int u = que[qh++];
        int du = dist[u];
        if (du >= D) continue;
        if (u < N) {
            for (int k = 0; k < d; k++) {
                int v = N + (u + S[k]) % N;
                if (dist[v] < 0) { dist[v] = du + 1; que[qt++] = v; reached++; }
            }
        } else {
            int j = u - N;
            for (int k = 0; k < d; k++) {
                int v = (j + N - S[k]) % N;
                if (dist[v] < 0) { dist[v] = du + 1; que[qt++] = v; reached++; }
            }
        }
    }
    return total - reached;
}

static int cost_of(void) { return bad_from(0) + bad_from(N); }

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int startN = atoi(argv[5]);
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    if (startN <= d) startN = d + 1;          /* need N > d so moves exist */
    if (startN > MAXN - 2) startN = MAXN - 2;
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;
    clock_t t0 = clock();

    N = startN;
    for (int k = 0; k < d; k++) {
        int x;
        do { x = rint_(N); } while (in_prefix(x, k));
        S[k] = x;
    }

    int cost = cost_of();
    long it = 0, since = 0;
    for (;;) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > budget) break;
        }
        it++;

        if (cost == 0) {
            bestN = N;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            if (N + 1 >= MAXN - 1) break;
            N++;
            since = 0;
            cost = cost_of();
            continue;
        }

        since++;
        double phase = (double)(since % 200000) / 200000.0;
        double T = 0.2 + 0.8 * (1.0 - phase) * (1.0 - phase);

        int k = rint_(d);
        int old = S[k];
        int nw;
        do { nw = rint_(N); } while (in_prefix(nw, d));
        S[k] = nw;
        int c2 = cost_of();
        int delta = c2 - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            S[k] = old;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestN, bestN * d);
    for (int i = 0; i < bestN; i++) {
        for (int k = 0; k < d; k++) {
            printf("%d %d\n", i, bestN + (i + bestS[k]) % bestN);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane based candidates (kept as a safe fallback).
# Start from PG(2, q) incidence and add A/B vertices on arcs in PG(2, q).
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


def _swap_improve(S, s, m, point_lines, line_points, rng, deadline, iters):
    """Ejection-based local search growing an arc set S; returns the best set seen."""
    cur = list(S)
    inS = set(cur)
    best = list(cur)
    pl_set = [set(point_lines[X]) for X in range(m)]
    lp_set = [set(line_points[X]) for X in range(m)]
    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if P in inS:
            continue
        cl = [0] * m
        cp = [0] * m
        for X in cur:
            for L in point_lines[X]:
                cl[L] += 1
            for Q in line_points[X]:
                cp[Q] += 1
        Lfull = {L for L in point_lines[P] if cl[L] >= s}
        Qfull = {Q for Q in line_points[P] if cp[Q] >= s}
        block = [X for X in cur if (pl_set[X] & Lfull) or (lp_set[X] & Qfull)]
        if len(block) > 2:
            continue
        if not block and rng.random() > 0.5:
            continue
        bset = set(block)
        new = [X for X in cur if X not in bset] + [P]
        if not _loads_ok(new, s, m, point_lines, line_points):
            continue
        if len(new) >= len(cur) or rng.random() < 0.1:
            cur = new
            inS = set(cur)
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
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
        m, edges, point_lines, line_points, index, _pts = _pg_data(q)
        cands = []
        if s >= 1:
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _swap_improve(g, s, m, point_lines, line_points, rng,
                              min(deadline, time.monotonic() + 2.0), iters=6000)
            cands.append(g)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cs = _swap_improve(cs, s, m, point_lines, line_points, rng,
                                   min(deadline, time.monotonic() + 1.0), iters=3000)
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

_MAX_START_N = 1000


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    end = t0 + max(0.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed * 7919 + d)

    # Projective-plane candidate for D = 3, given a short slice of the budget.
    if D == 3 and time.monotonic() < end:
        arc_deadline = time.monotonic() + 0.2 * (end - time.monotonic())
        try:
            for g in sorted(_arc_extensions(d, arc_deadline, rng), key=lambda t: -t[0]):
                consider(g)
        except Exception:
            pass

    # Generalized quadrangle candidate for D >= 4.
    if D >= 4 and time.monotonic() < end:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)
        except Exception:
            pass

    # Main search: cyclic Haar graphs with d shifts, grown by the C engine.
    avail = end - time.monotonic()
    if avail >= 0.5:
        moore = lib.moore_bound(d, D)
        start = max(d + 1, min(_MAX_START_N, moore // 4))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(avail, 2), start],
                            timeout=avail + 2.5)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
