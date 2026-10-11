"""Diameter-3 search by Haar graphs of difference covers, after structured starts.

Main new idea: a bipartite Haar graph H(G, S) on two copies of a group G, with a_g ~ b_{gs} for s in S,
|S| = d. It is d-regular with 2|G| vertices and has diameter <= 3 exactly when
S S^{-1} = G and S^{-1} S = G (a "difference cover"). The C engine anneals over subsets S of a
group G (cyclic Z_m or semidirect Z_a x| Z_b) to find such covers. Orders are tried upward from
the current best, so every success is a larger valid graph.

Starts (validated with lib.is_valid): the arc-extended PG(2,q) incidence graphs, conic blow-up,
Araujo-Pardo/Lopez, projective planes, W(q) for D >= 4, and K_{d,d} as the always-valid fallback.
Every candidate is checked with lib.is_valid before it can replace the best graph.
"""
import itertools
import math
import random
import time

import lib

C_DIFF = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 300
#define MAXK 64

static int order_;
static int MUL[MAXM][MAXM];
static int INV[MAXM];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void build_group(int type, int a, int b, int r) {
    if (type == 0) {
        order_ = a;
        for (int x = 0; x < a; x++)
            for (int y = 0; y < a; y++) MUL[x][y] = (x + y) % a;
    } else {
        order_ = a * b;
        int pw[MAXM];
        pw[0] = 1 % a;
        for (int j = 1; j < b; j++) pw[j] = (int)((long)pw[j - 1] * r % a);
        for (int x = 0; x < order_; x++) {
            int x1 = x / b, x2 = x % b;
            for (int y = 0; y < order_; y++) {
                int y1 = y / b, y2 = y % b;
                int t = (int)(((long)x1 + (long)pw[x2] * y1) % a);
                MUL[x][y] = t * b + (x2 + y2) % b;
            }
        }
    }
    for (int x = 0; x < order_; x++)
        for (int y = 0; y < order_; y++)
            if (MUL[x][y] == 0) { INV[x] = y; break; }
}

/* Number of group elements g not in S S^{-1} plus not in S^{-1} S. Zero means a difference cover. */
static int cost(const int *S, int k) {
    static int cl[MAXM], cr[MAXM];
    memset(cl, 0, sizeof(int) * order_);
    memset(cr, 0, sizeof(int) * order_);
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) {
            cl[MUL[S[i]][INV[S[j]]]]++;
            cr[MUL[INV[S[i]]][S[j]]]++;
        }
    int bad = 0;
    for (int g = 0; g < order_; g++) {
        if (!cl[g]) bad++;
        if (!cr[g]) bad++;
    }
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: type a b r k budget seed\n");
        return 2;
    }
    int type = atoi(argv[1]), a = atoi(argv[2]), b = atoi(argv[3]);
    int r = atoi(argv[4]), k = atoi(argv[5]);
    double budget = atof(argv[6]);
    unsigned long seed = strtoul(argv[7], NULL, 10);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (type == 0) {
        if (a < 1 || a > MAXM) { printf("NONE\n"); return 0; }
        build_group(0, a, 1, 1);
    } else {
        if (a < 1 || b < 1 || a * b > MAXM) { printf("NONE\n"); return 0; }
        build_group(1, a, b, r);
    }
    if (k < 1 || k > order_ || k > MAXK) { printf("NONE\n"); return 0; }

    double t_end = now() + budget;
    int S[MAXK];
    static char inS[MAXM];
    int found = 0, c = 0;
    while (!found && now() < t_end) {
        memset(inS, 0, sizeof inS);
        for (int i = 0; i < k; i++) {
            int x;
            do { x = rndint(order_); } while (inS[x]);
            inS[x] = 1;
            S[i] = x;
        }
        c = cost(S, k);
        double T = 1.0;
        for (long it = 0; it < 300000; it++) {
            if (c == 0) break;
            if ((it & 1023) == 0 && now() >= t_end) break;
            int i = rndint(k), x = rndint(order_);
            if (inS[x]) continue;
            int old = S[i];
            S[i] = x;
            int c2 = cost(S, k);
            int dl = c2 - c;
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                inS[old] = 0;
                inS[x] = 1;
                c = c2;
            } else {
                S[i] = old;
            }
            T *= 0.99997;
            if (T < 0.2) T = 0.2;
        }
        if (c == 0) found = 1;
    }
    if (found) {
        printf("FOUND");
        for (int i = 0; i < k; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("NONE\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured starts (unchanged from the parent).
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Best directly constructible graph for D = 3: projective plane or Araujo-Pardo/Lopez."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[], _greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2 and q >= 3:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def _gq_w(q):
    """Incidence graph of W(q), the generalized quadrangle (diameter 4)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def starts(d, D, deadline, rng):
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    if D >= 3:
        out.extend(_arc_extensions(d, deadline, rng))
    if D >= 4 and d - 1 <= 6:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# Difference-cover Haar graphs.
# ----------------------------------------------------------------------------

def _groups_of_order(m, rng):
    """Candidate groups of order m as ("c", m, 1, 1) or ("s", a, b, r) for Z_a x| Z_b."""
    cyc = ("c", m, 1, 1)
    others = []
    for b in range(2, m):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
        if not rs:
            continue
        for r in rng.sample(rs, min(2, len(rs))):
            others.append(("s", a, b, r))
    rng.shuffle(others)
    return [cyc] + others[:5]


def _diff_try(grp, k, budget, seed):
    """Run the C annealer for a difference cover S of size k in grp. Returns list or None."""
    kind, a, b, r = grp
    typ = 0 if kind == "c" else 1
    text = lib.run_c(C_DIFF, [typ, a, b, r, k, f"{budget:.3f}", seed],
                     timeout=budget + 5.0)
    toks = text.split()
    if not toks or toks[0] != "FOUND":
        return None
    S = [int(x) for x in toks[1:1 + k]]
    if len(S) != k:
        return None
    return S


def _haar_from(grp, S):
    """Haar graph H(G, S): a_g ~ b_{g s}. Returns (n, edges)."""
    kind, a, b, r = grp
    if kind == "c":
        order = a
        mul = lib.cyclic_group(a)[1]
    else:
        order = a * b
        mul = lib.semidirect_group(a, b, r)[1]
    edges = [(g, order + mul(g, s)) for g in range(order) for s in S]
    return 2 * order, edges


def _difference_phase(d, D, best, deadline, seed):
    """Try Haar graphs of increasing group order; keep the largest valid one found."""
    moore = lib.moore_bound(d, D)
    lo = max(best[0] // 2 + 1, d)
    hi = moore // 2
    if lo > hi:
        return best
    rng = random.Random(seed * 1000003 + d)
    for m in range(lo, hi + 1):
        left = deadline - time.monotonic()
        if left < 0.2:
            break
        per_m = left / (hi - m + 1)
        groups = _groups_of_order(m, rng)
        for gi, grp in enumerate(groups):
            left = deadline - time.monotonic()
            if left < 0.05:
                break
            share = per_m * (0.4 if gi == 0 else 0.6 / max(1, len(groups) - 1))
            budget = min(max(0.05, share), left - 0.05)
            try:
                S = _diff_try(grp, d, budget, seed * 131 + m * 7 + gi)
                if S is None:
                    continue
                n, edges = _haar_from(grp, S)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    break  # largest order at this m is found; move on
            except Exception:
                continue
    return best


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 88% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    for g in starts(d, D, t0 + 0.12 * time_limit, rng):
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass
    if lib.is_valid(fallback[0], fallback[1], d, D):
        cands.append(fallback)
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    if D >= 3 and d >= 2:
        try:
            best = _difference_phase(d, D, best, t0 + 0.88 * time_limit, seed)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
