import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: cyclic difference covers instead of greedy insertion.
#
# The Haar graph H(m, S) on Z_m x {A, B} joins a_i to b_j iff j - i is in S.
# Same-side vertices are at distance 2 exactly when S - S covers Z_m, and
# cross pairs are then at distance <= 3. So for D >= 3 a Haar graph with
# |S| = d and S - S = Z_m is valid, with order 2m. Since |S - S| <= d(d-1)+1,
# we get m <= d(d-1)+1, so 2m <= 2(d^2 - d + 1), which is the Moore-type ceiling.
#
# The C engine searches for such S by simulated annealing: cost = number of
# nonzero residues not covered by S - S, updated incrementally. It increases m
# upward and keeps the largest m that succeeds within the time budget.
#
# Fallbacks: K_{d,d} (diameter 2) and the Araujo-style projective-plane
# arc extension (diameter 3), plus W(q) for D >= 4. The largest valid graph wins.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64

static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double urand(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static int M, K;
static int el[MAXK];
static char inS[MAXM];
static int cnt[MAXM];
static int zeros;   /* number of residues x in 1..M-1 with cnt[x] == 0 */

static int dif(int a, int b) {
    int x = a - b;
    return x < 0 ? x + M : x;
}

static void inc(int x) { if (cnt[x]++ == 0) zeros--; }
static void dec(int x) { if (--cnt[x] == 0) zeros++; }

static void remove_slot(int idx) {
    int s = el[idx];
    for (int j = 0; j < K; j++) if (j != idx) {
        int t = el[j];
        dec(dif(s, t));
        dec(dif(t, s));
    }
    inS[s] = 0;
}

static void place_slot(int idx, int v) {
    for (int j = 0; j < K; j++) if (j != idx) {
        int t = el[j];
        inc(dif(v, t));
        inc(dif(t, v));
    }
    el[idx] = v;
    inS[v] = 1;
}

static void random_init(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(inS, 0, (size_t)M);
    zeros = M - 1;
    for (int i = 0; i < K; i++) {
        int v;
        do { v = (int)(rnd() % (uint32_t)M); } while (inS[v]);
        for (int j = 0; j < i; j++) {
            int t = el[j];
            inc(dif(v, t));
            inc(dif(t, v));
        }
        el[i] = v;
        inS[v] = 1;
    }
}

static void anneal(long iters) {
    for (long it = 0; it < iters && zeros > 0; it++) {
        double T = 1.5 * pow(0.03 / 1.5, (double)it / (double)iters);
        int i = (int)(rnd() % (uint32_t)K);
        int v = (int)(rnd() % (uint32_t)M);
        if (inS[v]) continue;
        int old = zeros;
        int s = el[i];
        remove_slot(i);
        place_slot(i, v);
        int delta = zeros - old;
        if (delta > 0 && urand() >= exp(-delta / T)) {
            remove_slot(i);
            place_slot(i, s);
        }
    }
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXK - 1 || D < 3) { printf("0 0\n"); return 0; }

    clock_t t0 = clock();
    K = d;
    int bestM = 0;
    int bestS[MAXK];

    int mmax = d * (d - 1) + 1;
    if (mmax > MAXM - 1) mmax = MAXM - 1;

    for (int mm = d + 1; mm <= mmax; mm++) {
        if (elapsed(t0) > budget) break;
        M = mm;
        int found = 0;
        for (int rep = 0; rep < 6 && !found; rep++) {
            if (elapsed(t0) > budget) break;
            random_init();
            anneal(300000L);
            if (zeros == 0) {
                found = 1;
                bestM = mm;
                memcpy(bestS, el, sizeof(int) * (size_t)K);
            }
        }
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestM, K);
    for (int i = 0; i < K; i++)
        printf("%d%c", bestS[i], i + 1 < K ? ' ' : '\n');
    return 0;
}
"""


def _run_difference_search(d, D, seed, budget):
    """Run the C cover search; return (m, S) with S - S = Z_m, or None."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=None, timeout=budget + 5.0)
    except Exception:
        return None
    nums = out.split()
    if len(nums) < 2:
        return None
    try:
        m, k = int(nums[0]), int(nums[1])
        if m < 1 or k < 1 or len(nums) < 2 + k:
            return None
        S = [int(x) for x in nums[2:2 + k]]
    except ValueError:
        return None
    return m, S


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), kept as a
# second candidate family.
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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
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
# Generalized quadrangle W(q) (diameter 4), for D >= 4 only.
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def elapsed():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D == 3 and d >= 2:
        # Arc-extended PG(2, q) candidates (a strong fallback family).
        try:
            arcs = _arc_extensions(d, start + 0.15 * time_limit,
                                   random.Random(seed * 7919 + d))
            for g in sorted(arcs, key=lambda t: -t[0]):
                consider(g)
        except Exception:
            pass

    if D >= 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Main bold candidate: Haar graph from a difference cover (valid for D >= 3).
    if D >= 3 and d >= 2:
        budget = 0.80 * time_limit - elapsed() - 1.5
        res = _run_difference_search(d, D, seed, budget)
        if res is not None:
            m, S = res
            try:
                consider(lib.haar_graph(m, S))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
