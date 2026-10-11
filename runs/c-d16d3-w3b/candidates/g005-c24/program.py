import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D = 3: Haar graphs over groups (difference bases).
#
# For a group G of order N and a d-subset S of G, the Haar graph H(G, S) has
# A-vertices g and B-vertices h (2N in total), with g ~ h iff g^{-1} h is in S.
# It is d-regular and bipartite. A-A pairs are at distance 2 exactly when
# S S^{-1} = G, and B-B pairs when S^{-1} S = G. Those two conditions give
# diameter 3 (A-B distances are then at most 3 automatically). The C engine
# searches for such S by simulated annealing for every group in a list of
# cyclic and semidirect groups of orders near the Moore-type ceiling
# d(d-1)+1, and prints the largest Haar graph it finds. Python re-checks it.
#
# Fallbacks: arc-extended projective plane graphs (D = 3), a generalized
# quadrangle (D >= 4), the cycle C_{2D} (d = 2), and K_{d,d} (always valid).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 512
#define MAXD 64

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int N;
static int mulT[MAXN][MAXN];
static int invT[MAXN];
static int c1[MAXN], c2[MAXN], inS[MAXN];

/* Semidirect product Z_a x| Z_k with r^k = 1 mod a; element (x1, x2) is coded x1*k + x2.
   Cyclic group: k = 1, r = 1. Identity is code 0. */
static void build_group(int a, int k, int r) {
    int pw[MAXN];
    N = a * k;
    pw[0] = 1 % a;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % a);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int a2 = y / k, b2 = y % k;
            mulT[x][y] = (int)((((long)a1 + (long)pw[b1] * a2) % a) * k + (b1 + b2) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        int nb = (k - b1) % k;
        int t = (int)((long)pw[nb] * a1 % a);
        int na = (a - t) % a;
        invT[x] = na * k + nb;
    }
}

/* Number of uncovered non-identity elements in S S^{-1} plus in S^{-1} S. Zero is valid. */
static int cost_of(const int *S, int d) {
    memset(c1, 0, sizeof(int) * (size_t)N);
    memset(c2, 0, sizeof(int) * (size_t)N);
    for (int i = 0; i < d; i++) {
        for (int j = 0; j < d; j++) {
            if (i == j) continue;
            c1[mulT[S[i]][invT[S[j]]]]++;
            c2[mulT[invT[S[i]]][S[j]]]++;
        }
    }
    int z = 0;
    for (int x = 1; x < N; x++) {
        if (!c1[x]) z++;
        if (!c2[x]) z++;
    }
    return z;
}

static int search(int d, double secs, int *S) {
    clock_t t_end = clock() + (clock_t)(secs * CLOCKS_PER_SEC);
    memset(inS, 0, sizeof(int) * (size_t)N);
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rint_(N); } while (inS[x]);
        inS[x] = 1;
        S[i] = x;
    }
    int cur = cost_of(S, d);
    const long period = 300000;
    for (long it = 1; ; it++) {
        if (cur == 0) return 1;
        if ((it & 1023) == 0 && clock() > t_end) break;
        double phase = (double)(it % period) / (double)period;
        double T = 0.10 + 0.9 * (1.0 - phase) * (1.0 - phase);
        int i = rint_(d);
        int x;
        do { x = rint_(N); } while (inS[x]);
        int old = S[i];
        S[i] = x;
        int c = cost_of(S, d);
        int delta = c - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[x] = 1;
            cur = c;
        } else {
            S[i] = old;
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    unsigned long long seed = strtoull(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    int G = atoi(argv[4]);
    if (d < 1 || d > MAXD || G < 0 || argc < 5 + 3 * G) { printf("0 0\n"); return 0; }
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 0x1234567ULL);
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    clock_t t0 = clock();
    int bestN = 0, bestA = 0, bestK = 0, bestR = 0;
    int bestS[MAXD];
    for (int g = 0; g < G; g++) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        double rem = budget - el;
        if (rem <= 0.05) break;
        int a = atoi(argv[5 + 3 * g]);
        int k = atoi(argv[6 + 3 * g]);
        int r = atoi(argv[7 + 3 * g]);
        if (a < 1 || k < 1 || a * k > MAXN - 1 || a * k <= d) continue;
        double slice = rem / (double)(G - g);
        build_group(a, k, r);
        int S[MAXD];
        if (search(d, slice, S)) {
            if (N > bestN) {
                bestN = N; bestA = a; bestK = k; bestR = r;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
    }
    if (bestN == 0) { printf("0 0\n"); return 0; }

    build_group(bestA, bestK, bestR);
    printf("%d %d\n", 2 * bestN, bestN * d);
    for (int x = 0; x < bestN; x++) {
        for (int i = 0; i < d; i++) {
            printf("%d %d\n", x, bestN + mulT[x][bestS[i]]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Group list for the Haar search (D = 3)
# ----------------------------------------------------------------------------

def _groups(d):
    """Orders N in [lo, hi] with hi = d(d-1)+1 (the difference-set bound), each as (a, k, r).

    Each N gets the cyclic group and, when it exists, one nonabelian semidirect product.
    """
    hi = min(d * (d - 1) + 1, 500)
    lo = max(d + 2, int(0.82 * hi))
    out = []
    for N in range(lo, hi + 1):
        out.append((N, 1, 1))
        for k in range(2, N // 2 + 1):
            if N % k:
                continue
            a = N // k
            if a < 2:
                continue
            r = next((r for r in range(2, a)
                      if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a), None)
            if r is not None:
                out.append((a, k, r))
                break
    return out


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (D = 3 fallback).
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
    """Conic (plus nucleus for even q) as a point-index set."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates for each prime power q with q + 1 <= d. Always valid for D = 3."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if _loads_ok(S, s, m, point_lines, line_points):
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

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit - 2.0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, list(e0))

    def consider(g):
        nonlocal best
        try:
            if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = (g[0], list(g[1]))
        except Exception:
            pass

    # For d = 2 the cycle C_{2D} has diameter D.
    if d == 2 and D >= 2:
        n = 2 * D
        consider((n, [(i, (i + 1) % n) for i in range(n)]))

    if D == 2:
        return best[0], list(best[1])

    if D == 3:
        rng = random.Random(seed * 7919 + d)
        for g in _arc_candidates(d, t0 + 0.12 * time_limit, rng):
            consider(g)

        groups = _groups(d)
        budget = end - time.monotonic() - 2.0
        if groups and budget > 3.0:
            args = [d, int(seed), round(budget, 2), len(groups)]
            for a, k, r in groups:
                args += [a, k, r]
            try:
                out = lib.run_c(C_SOURCE, args, stdin_graph=None, timeout=budget + 15)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    elif D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        n, e = lib.haar_graph(d, range(d))
        best = (n, list(e))
    return best[0], list(best[1])
