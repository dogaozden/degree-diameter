import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic Haar graphs with diameter 3 (new main search for D >= 3).
#
# Haar graph H(Z_m, S): a_i ~ b_{i+s} for s in S, |S| = d, so it is d-regular and
# bipartite with 2m vertices. It has diameter <= 3 iff
#   (1) S - S covers Z_m                      (a-a pairs at distance 2), and
#   (2) S union (S - S + S) covers Z_m        (a-b pairs at distance 1 or 3).
# The graph is symmetric under translations and under the side swap
# a_i <-> b_{-i}, so checking distances from a_0 suffices.
# The C engine does simulated annealing over the set S for each m, starting
# just below the Moore limit m = d^2 - d + 1 and searching upward in m.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1000
#define MAXD 64

static int d_, m_;
static int S_[MAXD];
static int inS[MAXM];
static unsigned char A2[MAXM], Bc[MAXM];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

/* Number of uncovered residues: A2 (a-side at distance <= 2) and Bc (b-side at distance <= 3). */
static int cost_of(void) {
    int m = m_, d = d_;
    memset(A2, 0, (size_t)m);
    memset(Bc, 0, (size_t)m);
    for (int i = 0; i < d; i++) Bc[S_[i]] = 1;
    for (int i = 0; i < d; i++) {
        for (int j = 0; j < d; j++) {
            int x = S_[i] - S_[j];
            if (x < 0) x += m;
            A2[x] = 1;
            for (int k = 0; k < d; k++) {
                int y = x + S_[k];
                if (y >= m) y -= m;
                Bc[y] = 1;
            }
        }
    }
    int c = 0;
    for (int x = 0; x < m; x++) c += (!A2[x]) + (!Bc[x]);
    return c;
}

/* Simulated annealing for a fixed m. Returns 1 with S_ filled in if cost reaches 0. */
static int anneal(int m, double deadline, int iters) {
    m_ = m;
    while (now() < deadline) {
        for (int i = 0; i < m; i++) inS[i] = 0;
        for (int i = 0; i < d_; i++) {
            int v;
            do { v = rint_(m); } while (inS[v]);
            S_[i] = v;
            inS[v] = 1;
        }
        int cost = cost_of();
        for (int it = 0; it < iters; it++) {
            if (cost == 0) return 1;
            if ((it & 511) == 0 && now() > deadline) return 0;
            double T = 0.8 * (1.0 - (double)it / iters) + 0.03;
            int idx = rint_(d_);
            int old = S_[idx];
            int v;
            do { v = rint_(m); } while (inS[v]);
            S_[idx] = v;
            int c2 = cost_of();
            int delta = c2 - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                inS[old] = 0;
                inS[v] = 1;
                cost = c2;
            } else {
                S_[idx] = old;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    d_ = atoi(argv[1]);
    uint64_t seed = (uint64_t)strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    if (d_ < 2 || d_ > MAXD) { printf("0 0\n"); return 0; }

    long mhi_l = (long)d_ * d_ - d_ + 1;   /* Moore bound 2(d^2-d+1) on 2m vertices */
    int m_hi = mhi_l > MAXM - 1 ? MAXM - 1 : (int)mhi_l;
    int m_start = (int)(0.55 * m_hi);
    if (m_start < d_ + 1) m_start = d_ + 1;

    int best_m = 0;
    int bestS[MAXD];
    int fails = 0;
    for (int m = m_start; m <= m_hi; m++) {
        double remain = tl - now();
        if (remain <= 0.2) break;
        double cap = 0.2 * remain;
        if (cap < 0.5) cap = 0.5;
        double dl = now() + cap;
        if (dl > tl) dl = tl;
        if (anneal(m, dl, 30000)) {
            best_m = m;
            memcpy(bestS, S_, sizeof(int) * (size_t)d_);
            fails = 0;
        } else {
            if (++fails >= 6) break;
        }
    }

    if (best_m == 0) { printf("0 0\n"); return 0; }
    int m = best_m, d = d_;
    printf("%d %d\n", 2 * m, m * d);
    for (int i = 0; i < m; i++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", i, m + (i + bestS[j]) % m);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. With d >= q+1 each vertex has spare capacity
# s = d - q - 1. Pick a point set S with every line holding <= s points of S and
# every point lying on <= s lines indexed by S. Add an A-vertex joined to the
# q+1 lines through each P in S, and a B-vertex joined to the q+1 points on each
# line j in S. Every candidate is re-checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _swap_improve(S, s, m, pl, lp, rng, deadline, iters):
    """Ejection-based local search growing the arc set S. Returns the best set seen."""
    cur = list(S)
    inS = set(cur)
    best = list(cur)
    pl_set = [set(pl[X]) for X in range(m)]
    lp_set = [set(lp[X]) for X in range(m)]
    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if P in inS:
            continue
        cl = [0] * m
        cp = [0] * m
        for X in cur:
            for L in pl[X]:
                cl[L] += 1
            for Q in lp[X]:
                cp[Q] += 1
        Lfull = {L for L in pl[P] if cl[L] >= s}
        Qfull = {Q for Q in lp[P] if cp[Q] >= s}
        block = [X for X in cur if (pl_set[X] & Lfull) or (lp_set[X] & Qfull)]
        if len(block) > 2:
            continue
        if not block and rng.random() > 0.5:
            continue
        bset = set(block)
        new = [X for X in cur if X not in bset] + [P]
        if not _loads_ok(new, s, m, pl, lp):
            continue
        if len(new) >= len(cur) or rng.random() < 0.1:
            cur = new
            inS = set(cur)
            if len(cur) > len(best):
                best = list(cur)
    return best


def _arc_graph(m, edges, pl, lp, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """Arc-extended candidates for the three largest prime powers q with q + 1 < d."""
    out = []
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp = _pg_data(q)
        S = _greedy_arc(m, s, pl, lp, rng, 20, deadline)
        S = _swap_improve(S, s, m, pl, lp, rng,
                          min(deadline, time.monotonic() + 2.0), iters=4000)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
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

def _haar_search(d, seed, budget):
    """Run the C cyclic-Haar search; return (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, seed, budget], stdin_graph=None, timeout=budget + 5)
        return lib.parse_graph_text(out)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit - 1.0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    rng = random.Random(seed * 7919 + d)

    # Arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3 and d >= 2:
        for g in sorted(_arc_candidates(d, t0 + 0.2 * time_limit, rng), key=lambda t: -t[0]):
            consider(g)

    # Generalized quadrangle (diameter 4, valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Main new search: cyclic Haar graph H(Z_m, S) with diameter 3, valid for D >= 3.
    if D >= 3 and d >= 2:
        budget = end - time.monotonic()
        if budget > 2.0:
            res = _haar_search(d, seed, round(budget, 2))
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
