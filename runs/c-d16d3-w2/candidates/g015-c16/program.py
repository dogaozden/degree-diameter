import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic difference-cover Haar graphs (diameter 3).
#
# For S subset of Z_G with |S| = d, the bipartite graph on A_i, B_j (i, j in Z_G)
# with A_i ~ B_{i+s} for s in S is d-regular. Two A's share a neighbour iff their
# difference lies in S - S, so every A-A pair is at distance <= 2 when S - S = Z_G.
# A-B pairs are at distance <= 3 because S - S + S = Z_G whenever S - S = Z_G.
# So the graph has diameter 3 exactly when S is a difference cover of Z_G.
# The bound G <= d(d-1)+1 comes from counting ordered differences.
#
# The C engine anneals S (containing 0) to minimise the number of uncovered
# nonzero residues, sweeping G upward and keeping the largest success.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 4200
#define MAXK 64

static int G, K;
static int S[MAXK];
static char inS[MAXG];
static int cnt[MAXG];
static int U;
static uint64_t rs = 88172645463325252ULL;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double unif(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int rnd_int(int n) {
    return (int)(nextr() % (uint64_t)n);
}

/* Remove element S[i] from the difference counts (S[i] still holds its value). */
static void remove_el(int i) {
    int a = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int b = S[j];
        int x = a - b; if (x < 0) x += G;
        if (--cnt[x] == 0) U++;
        int y = b - a; if (y < 0) y += G;
        if (--cnt[y] == 0) U++;
    }
}

/* Insert value v at index i and add its differences. */
static void insert_el(int i, int v) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int b = S[j];
        int x = v - b; if (x < 0) x += G;
        if (cnt[x]++ == 0) U--;
        int y = b - v; if (y < 0) y += G;
        if (cnt[y]++ == 0) U--;
    }
    S[i] = v;
}

static void init_state(void) {
    for (int x = 0; x < G; x++) cnt[x] = 0;
    U = G - 1;
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            int x = S[i] - S[j]; if (x < 0) x += G;
            if (cnt[x]++ == 0) U--;
            int y = S[j] - S[i]; if (y < 0) y += G;
            if (cnt[y]++ == 0) U--;
        }
}

/* Anneal for up to secs seconds of CPU time. Returns 1 with S a difference cover, else 0. */
static int anneal(double secs) {
    clock_t end = clock() + (clock_t)(secs * (double)CLOCKS_PER_SEC);
    for (int x = 0; x < G; x++) inS[x] = 0;
    S[0] = 0;
    inS[0] = 1;
    int k = 1;
    while (k < K) {
        int v = 1 + rnd_int(G - 1);
        if (!inS[v]) { S[k++] = v; inS[v] = 1; }
    }
    init_state();
    if (U == 0) return 1;
    if (K < 2) return 0;

    const long CH = 200000;
    const double T0 = 1.2, T1 = 0.05;
    const double f = pow(T1 / T0, 1.0 / (double)CH);
    for (;;) {
        double T = T0;
        for (long s = 0; s < CH; s++, T *= f) {
            if ((s & 1023) == 0 && clock() > end) return 0;
            int i = 1 + rnd_int(K - 1);
            int a = S[i];
            int v;
            if (U > 0 && (nextr() & 1ULL)) {
                /* focused move: create a difference equal to a random uncovered residue */
                int r = rnd_int(U), x = -1;
                for (int y = 1; y < G; y++) {
                    if (cnt[y] == 0) {
                        if (r == 0) { x = y; break; }
                        r--;
                    }
                }
                if (x < 0) continue;
                int j = rnd_int(K);
                v = S[j] + x;
                if (v >= G) v -= G;
            } else {
                v = 1 + rnd_int(G - 1);
            }
            if (inS[v]) continue;
            int oldU = U;
            remove_el(i);
            inS[a] = 0;
            insert_el(i, v);
            inS[v] = 1;
            int delta = U - oldU;
            if (delta <= 0 || unif() < exp(-(double)delta / T)) {
                if (U == 0) return 1;
            } else {
                remove_el(i);
                inS[v] = 0;
                insert_el(i, a);
                inS[a] = 1;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    if (K < 1 || K > MAXK || D != 3) { printf("0 0\n"); return 0; }

    int cap = K * (K - 1) + 1;
    if (cap > MAXG - 1) cap = MAXG - 1;
    int lo = (int)(0.6 * cap);
    if (lo < K) lo = K;
    if (lo < 1) lo = 1;

    int bestG = 0;
    int bestS[MAXK];
    clock_t t0 = clock();
    double total = budget * 0.92;

    for (int g = lo; g <= cap; g++) {
        double el = (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
        double rem = total - el;
        if (rem <= 0.005) break;
        int left = cap - g + 1;
        double sl = rem / (double)left;
        G = g;
        if (anneal(sl)) {
            bestG = g;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    G = bestG;
    printf("%d %d\n", 2 * G, G * K);
    for (int i = 0; i < G; i++)
        for (int t = 0; t < K; t++)
            printf("%d %d\n", i, G + (i + bestS[t]) % G);
    return 0;
}
"""


def _c_cyclic(d, seed, budget):
    """Run the cyclic difference-cover engine; return (n, edges) or None on any failure."""
    if budget < 0.5 or d < 1 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, 3, seed, round(budget, 2)],
                        stdin_graph=None, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 1:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1), degree q+1,
# spare s = d - q - 1. New point-side vertices attach to q+1 lines, and each line
# may take at most s of them. New line-side vertices attach to q+1 points, and each
# point may take at most s of them. Conics give arcs of size q+1 (q odd) for s = 2.
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
    """Randomised greedy choice of elements so that every target is hit at most s times."""
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
        if _loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points):
            out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence (diameter 4), used only for D >= 4.
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
# Driver. For D = 3 the cyclic difference-cover search gets most of the time.
# The arc-extended PG graphs are a second candidate, and K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def elapsed():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit,
                               random.Random(seed * 7919 + d))
        for g in sorted(arcs, key=lambda t: -t[0]):
            consider(g)
        c_budget = 0.86 * time_limit - elapsed() - 1.5
        consider(_c_cyclic(d, seed, c_budget))
    elif D >= 4:
        consider(_best_gq(d))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
