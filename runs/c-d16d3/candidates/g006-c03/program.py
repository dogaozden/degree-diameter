"""Diameter-3 bipartite search: Haar-type group lifts plus the arc-extended projective plane fallback.

New construction for D = 3. For a finite group G of order n and a set S of d elements, the
Haar graph has parts A = {A_x} and B = {B_y}, with A_x ~ B_y iff x^-1 y is in S. It is
d-regular with 2n vertices. Left multiplication is an automorphism acting transitively on
each part, so diameter <= 3 holds iff every vertex of A_e and B_e reaches all 2n vertices
within 3 steps. The C engine runs simulated annealing over S to drive that count to zero,
for groups Z_m and semidirect products Z_m x| Z_k. A success at order n gives 2n vertices,
so the search climbs from the current best upward.

The safe fallback is the arc-extended PG(2,q) construction (q the largest prime power with
q + 1 <= d) from the previous version, or K_{d,d}. Every candidate is checked with
lib.is_valid before it is returned. The C augmentation pass of the previous version was
replaced by this search for D = 3. For D >= 4 the program returns the arc or generalized
quadrangle starts.
"""
import itertools
import math
import random
import time

import lib

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXDEG 64
#define EPOCH 30000

static int G, MM, KK, RR, DEG, DIAM;
static int *mulT;
static int invT[MAXG];
static int pw[MAXG];
static int S[MAXDEG];
static int inS[MAXG];
static int stampv[2 * MAXG];
static int distv[2 * MAXG];
static int qv[2 * MAXG];
static int stampc = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* Semidirect product Z_MM x| Z_KK with element a*KK+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / KK, b = x % KK, c = y / KK, d = y % KK;
    int na = (int)((a + (long)pw[b] * c) % MM);
    int nb = (b + d) % KK;
    return na * KK + nb;
}

/* Number of vertices NOT within DIAM steps of src in the Haar graph. */
static int unreached(int src) {
    int head = 0, tail = 0;
    int tot = 2 * G;
    stampc++;
    qv[tail++] = src;
    stampv[src] = stampc;
    distv[src] = 0;
    while (head < tail) {
        int u = qv[head++];
        int du = distv[u];
        if (du >= DIAM) continue;
        if (u < G) {
            const int *row = mulT + (size_t)u * G;
            for (int k = 0; k < DEG; k++) {
                int v = G + row[S[k]];
                if (stampv[v] != stampc) {
                    stampv[v] = stampc;
                    distv[v] = du + 1;
                    qv[tail++] = v;
                }
            }
        } else {
            const int *row = mulT + (size_t)(u - G) * G;
            for (int k = 0; k < DEG; k++) {
                int v = row[invT[S[k]]];
                if (stampv[v] != stampc) {
                    stampv[v] = stampc;
                    distv[v] = du + 1;
                    qv[tail++] = v;
                }
            }
        }
    }
    return tot - tail;
}

static int obj(void) { return unreached(0) + unreached(G); }

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    G = atoi(argv[1]);
    MM = atoi(argv[2]);
    KK = atoi(argv[3]);
    RR = atoi(argv[4]);
    DEG = atoi(argv[5]);
    DIAM = atoi(argv[6]);
    unsigned long seed = strtoul(argv[7], NULL, 10);
    double budget = atof(argv[8]);
    if (G < 1 || G > MAXG || MM < 1 || KK < 1 || MM * KK != G ||
        DEG < 1 || DEG > MAXDEG || DEG >= G || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;

    mulT = (int *)malloc(sizeof(int) * (size_t)G * (size_t)G);
    if (!mulT) { printf("0 0\n"); return 0; }
    pw[0] = 1 % MM;
    for (int b = 1; b < KK; b++) pw[b] = (int)((long)pw[b - 1] * RR % MM);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        invT[x] = -1;
        for (int y = 0; y < G; y++)
            if (mulT[x * G + y] == 0) { invT[x] = y; break; }
        if (invT[x] < 0) { printf("0 0\n"); return 0; }
    }

    int best_obj = 1 << 30;
    int bestS[MAXDEG];
    int found = 0;
    double t_end = cpu() + budget;

    while (!found && cpu() < t_end) {
        memset(inS, 0, sizeof(int) * G);
        for (int k = 0; k < DEG; k++) {
            int g;
            do g = rndint(G); while (inS[g]);
            S[k] = g;
            inS[g] = 1;
        }
        int cur = obj();
        if (cur < best_obj) {
            best_obj = cur;
            memcpy(bestS, S, sizeof(int) * DEG);
        }
        if (cur == 0) { found = 1; break; }
        double temp = 0.2 + 1.3 * urand();
        for (int it = 0; it < EPOCH; it++) {
            if ((it & 255) == 0 && cpu() >= t_end) break;
            int i = rndint(DEG);
            int g;
            do g = rndint(G); while (inS[g]);
            int old = S[i];
            inS[old] = 0;
            S[i] = g;
            inS[g] = 1;
            int f = obj();
            if (f <= cur || urand() < exp(-(double)(f - cur) / temp)) {
                cur = f;
                if (cur < best_obj) {
                    best_obj = cur;
                    memcpy(bestS, S, sizeof(int) * DEG);
                }
                if (cur == 0) { found = 1; break; }
            } else {
                inS[g] = 0;
                S[i] = old;
                inS[old] = 1;
            }
        }
    }

    if (!found || best_obj != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * G, G * DEG);
    for (int x = 0; x < G; x++)
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", x, G + mulT[x * G + bestS[k]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Group candidates for the Haar search.
# ----------------------------------------------------------------------------

def _groups_of_order(G, rng):
    """Return (m, k, r) triples with m*k = G: cyclic Z_G first, then semidirect Z_m x| Z_k."""
    cyc = [(G, 1, 1)]
    rest = []
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                rest.append((m, k, r))
    rng.shuffle(rest)
    return cyc + rest


def _haar_search(d, D, seed, lo, hi, end):
    """Search Haar graphs of order 2G for G in [lo, hi]; return the best valid (n, edges) or None."""
    best = None
    rng = random.Random(seed * 1000003 + d)
    for G in range(lo, hi + 1):
        cands = _groups_of_order(G, rng)
        for (m, k, r) in cands[:3]:
            remaining = end - time.monotonic()
            if remaining < 1.5:
                return best
            budget = min(4.0, remaining - 1.0)
            try:
                text = lib.run_c(HAAR_C, [G, m, k, r, d, D, seed + G * 13 + k, f"{budget:.2f}"],
                                 timeout=budget + 5.0)
                n, edges = lib.parse_graph_text(text)
            except (RuntimeError, ValueError):
                continue
            if n > 0 and lib.is_valid(n, edges, d, D):
                if best is None or n > best[0]:
                    best = (n, edges)
                break  # success at this G: move on to larger orders
    return best


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), kept as the fallback.
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 90% of time_limit."""
    t0 = time.monotonic()
    end = t0 + 0.9 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.15 * time_limit, rng))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    valid = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        valid.append(fallback)
    if not valid:
        return 1, []
    best = max(valid, key=lambda g: g[0])

    # New construction for D = 3: Haar graphs of order 2G with G above the current best half.
    if D == 3 and d >= 3:
        lo = best[0] // 2 + 1
        hi = lib.moore_bound(d, D) // 2
        if lo <= hi:
            found = _haar_search(d, D, seed, lo, hi, end)
            if found is not None and found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                best = found

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
