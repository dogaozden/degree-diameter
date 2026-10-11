"""Diameter-3 bipartite search with two constructions.

1. Difference-cover Haar graphs (new). For an abelian group G of order m and a set S of size d,
   the Haar graph with parts G and G, a_i ~ b_{i+s} (s in S), is d-regular with 2m vertices. It has
   diameter <= 3 when S-S = G (same-side pairs at distance 2) and S+S-S = G (opposite-side pairs
   at distance 1 or 3). The C engine searches for such S by simulated annealing over groups
   Z_a x Z_b, for m increasing from the current record half-order upward. The upper bound
   m <= d^2-d+1 is forced by the difference-cover counting argument.
2. Arc-extended projective plane (previous parent). It is kept as a valid start and as a
   second candidate, and the better of the two is returned.

Every candidate is checked with lib.is_valid. K_{d,d} is the fallback.
"""
import itertools
import random
import time

import lib

C_DIFF = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MG 256
#define MK 64

static int M, A, B, K;
static int SUB[MG][MG];
static int cnt[MG];
static int zeros;
static int S[MK];
static int inS[MG];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* Group Z_a x Z_b, element x = x1*b + x2. */
static void build_group(int a, int b) {
    A = a; B = b; M = a * b;
    for (int x = 0; x < M; x++)
        for (int y = 0; y < M; y++) {
            int x1 = x / b, x2 = x % b, y1 = y / b, y2 = y % b;
            SUB[x][y] = ((x1 - y1 + a) % a) * b + (x2 - y2 + b) % b;
        }
}

static void bump(int t, int dir) {
    if (t == 0) return;
    if (dir > 0) {
        if (cnt[t] == 0) zeros--;
        cnt[t]++;
    } else {
        cnt[t]--;
        if (cnt[t] == 0) zeros++;
    }
}

/* Replace S[idx] by v (idx >= 1; S[0] = 0 is fixed by translation invariance). */
static void set_elem(int idx, int v) {
    int old = S[idx];
    for (int j = 0; j < K; j++) {
        if (j == idx) continue;
        bump(SUB[old][S[j]], -1);
        bump(SUB[S[j]][old], -1);
    }
    for (int j = 0; j < K; j++) {
        if (j == idx) continue;
        bump(SUB[v][S[j]], 1);
        bump(SUB[S[j]][v], 1);
    }
    S[idx] = v;
}

static void restart(void) {
    memset(cnt, 0, sizeof(cnt));
    memset(inS, 0, sizeof(inS));
    zeros = M - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int k = 1; k < K; k++) {
        int v;
        do v = rndint(M); while (inS[v]);
        S[k] = v;
        inS[v] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) bump(SUB[S[i]][S[j]], 1);
}

/* Simulated annealing until S-S covers the whole group, or the deadline passes. */
static int anneal(double deadline) {
    const long ITER = 300000;
    while (now() < deadline) {
        restart();
        if (zeros == 0) return 1;
        for (long it = 0; it < ITER; it++) {
            double T = 1.2 * pow(0.03 / 1.2, (double)it / (double)ITER);
            int idx = 1 + rndint(K - 1);
            int v = rndint(M);
            if (inS[v]) continue;
            int old = S[idx];
            int oz = zeros;
            set_elem(idx, v);
            int delta = zeros - oz;
            if (delta <= 0 || rnd01() < exp(-delta / T)) {
                inS[old] = 0;
                inS[v] = 1;
                if (zeros == 0) return 1;
            } else {
                set_elem(idx, old);
            }
        }
        if (now() >= deadline) break;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("NONE\n"); return 0; }
    K = atoi(argv[1]);
    int hi = atoi(argv[2]);
    int lo = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    if (K < 2 || K > MK) { printf("NONE\n"); return 0; }
    if (hi > MG - 1) hi = MG - 1;
    if (lo < K) lo = K;

    double t_end = now() + budget;
    int bestA = 0, bestB = 0, bestS[MK];
    int found = 0;
    for (int m = lo; m <= hi; m++) {
        double rem = t_end - now();
        if (rem <= 0.0) break;
        double mslice = rem / (double)(hi - m + 1);
        int dv[MK], nd = 0;
        for (int a = 1; a <= m; a++)
            if (m % a == 0 && nd < MK) dv[nd++] = a;
        for (int t = 0; t < nd; t++) {
            double r2 = t_end - now();
            if (r2 <= 0.0) break;
            double sl = mslice / (double)nd;
            if (sl > r2) sl = r2;
            build_group(dv[t], m / dv[t]);
            if (anneal(now() + sl)) {
                found = 1;
                bestA = A;
                bestB = B;
                memcpy(bestS, S, sizeof(int) * K);
                break;
            }
        }
    }
    if (!found) { printf("NONE\n"); return 0; }
    printf("OK %d %d %d", bestA, bestB, K);
    for (int i = 0; i < K; i++) printf(" %d", bestS[i]);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Difference-cover Haar graphs.
# ----------------------------------------------------------------------------

def _diff_search(d, lo, hi, seed, budget):
    """Run the C annealer; return (n, edges) of a d-regular Haar graph, or None."""
    text = lib.run_c(C_DIFF, [d, hi, lo, seed, f"{budget:.2f}"],
                     timeout=budget + 3.0)
    tok = text.split()
    if len(tok) < 4 or tok[0] != "OK":
        return None
    a, b, k = int(tok[1]), int(tok[2]), int(tok[3])
    S = [int(x) for x in tok[4:4 + k]]
    if len(S) != k or a * b != 0 and a * b < k:
        return None
    m = a * b

    def add(x, y):
        return ((x // b + y // b) % a) * b + (x % b + y % b) % b

    edges = []
    for i in range(m):
        for s in S:
            edges.append((i, m + add(i, s)))
    return 2 * m, edges


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), previous parent.
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else (1, [])

    # Arc-extended / generalized quadrangle start (valid by construction, checked anyway).
    par = None
    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.12 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.12 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if starts:
        par = max(starts, key=lambda g: g[0])
        if par[0] > best[0]:
            best = par

    # New construction: d-regular Haar graph from a difference cover of an abelian group.
    # Aim for m = half-order strictly above the current best; m <= d^2 - d + 1 is forced.
    if D >= 3 and d >= 3:
        hi = min(255, d * d - d + 1)
        lo = max(d, best[0] // 2 + 1)
        rem = hard_end - time.monotonic()
        if hi >= lo and rem > 3.0:
            try:
                res = _diff_search(d, lo, hi, seed, 0.6 * rem)
            except Exception:
                res = None
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res

    # Try to extend the arc/GQ start with leftover time (it has spare capacity if d > q+1).
    if par is not None:
        rem = hard_end - time.monotonic()
        if rem > 2.0:
            # Greedy vertex additions are not needed for the record case; keep the start.
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
