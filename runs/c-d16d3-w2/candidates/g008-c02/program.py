import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine for D = 3: bi-Cayley graphs over abelian groups Z_m1 x Z_m2.
#
# Take S with |S| = d in G. The graph has vertices a_x and b_x (x in G) and
# edges a_x -- b_{x+s} for s in S. It is d-regular and bipartite. Every pair
# of vertices is within distance 3 exactly when every nonzero g in G is a
# difference s - t of two elements of S. So the C search looks for a difference
# cover of G of size d by simulated annealing. Cost = number of uncovered g.
# ----------------------------------------------------------------------------

C_DIFF = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 400
#define MAXD 64

static int G, m1, m2, d;
static int subt[MAXG][MAXG];
static int addt[MAXG][MAXG];
static int negt[MAXG];
static int cnt[MAXG];
static int S[MAXD];
static int inS[MAXG];
static int uncovered;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static inline void inc(int g) { if (cnt[g]++ == 0) uncovered--; }
static inline void dec(int g) { if (--cnt[g] == 0) uncovered++; }

static void remove_slot(int i) {
    int x = S[i];
    for (int j = 0; j < d; j++) {
        if (j != i) {
            int t = S[j];
            dec(subt[x][t]);
            dec(subt[t][x]);
        }
    }
}

static void add_slot(int i, int y) {
    for (int j = 0; j < d; j++) {
        if (j != i) {
            int t = S[j];
            inc(subt[y][t]);
            inc(subt[t][y]);
        }
    }
    S[i] = y;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    d = atoi(argv[1]);
    uint64_t seed = (uint64_t)strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    m1 = atoi(argv[4]);
    m2 = atoi(argv[5]);
    G = m1 * m2;
    if (d < 2 || d > MAXD || m1 < 1 || m2 < 1 || G < 3 || G > MAXG || d >= G) {
        printf("FAIL\n");
        return 0;
    }
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;

    for (int e = 0; e < G; e++) {
        int a = e / m2, b = e % m2;
        negt[e] = ((m1 - a) % m1) * m2 + (m2 - b) % m2;
    }
    for (int x = 0; x < G; x++) {
        int ax = x / m2, bx = x % m2;
        for (int y = 0; y < G; y++) {
            int ay = y / m2, by = y % m2;
            addt[x][y] = ((ax + ay) % m1) * m2 + (bx + by) % m2;
        }
    }
    for (int x = 0; x < G; x++)
        for (int t = 0; t < G; t++)
            subt[x][t] = addt[x][negt[t]];

    for (int j = 0; j < d; j++) {
        int e;
        do { e = rint_(G); } while (inS[e]);
        inS[e] = 1;
        S[j] = e;
    }
    uncovered = G - 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) inc(subt[S[i]][S[j]]);

    clock_t t0 = clock();
    long it = 0;
    const long L = 300000;
    while (uncovered > 0) {
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        it++;
        double phase = (double)(it % L) / (double)L;
        double T = pow(0.04, phase);
        int i = rint_(d);
        int x = S[i];
        int y;
        if (rdbl() < 0.6) {
            int cand[MAXG];
            int nc = 0;
            for (int g = 1; g < G; g++) if (cnt[g] == 0) cand[nc++] = g;
            int g = cand[rint_(nc)];
            int j = (i + 1 + rint_(d - 1)) % d;
            y = addt[S[j]][g];
        } else {
            do { y = rint_(G); } while (inS[y]);
        }
        if (inS[y]) continue;
        int old = uncovered;
        remove_slot(i);
        add_slot(i, y);
        int delta = uncovered - old;
        if (delta <= 0 || rdbl() < exp((double)(-delta) / T)) {
            inS[x] = 0;
            inS[y] = 1;
        } else {
            remove_slot(i);
            add_slot(i, x);
        }
    }

    if (uncovered == 0) {
        printf("OK");
        for (int j = 0; j < d; j++) printf(" %d", S[j]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3, fast baseline).
#
# Start from the incidence graph of PG(2, q). With d >= q+1 each vertex has
# spare capacity s = d - q - 1. Choose S so that every line holds <= s points
# of S and every point lies on <= s lines indexed by S. Add an A-vertex joined
# to the q+1 lines through each P in S, and a B-vertex joined to the q+1 points
# on each line j in S.
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley difference-cover search (diameter 3).
# ----------------------------------------------------------------------------

def _groups(G):
    """Abelian groups of order G as (m1, m2) with element code a*m2 + b; cyclic first."""
    out = [(1, G)]
    for a in range(2, math.isqrt(G) + 1):
        if G % a == 0:
            out.append((a, G // a))
    return out


def _bicayley(G, m1, m2, S):
    """Bi-Cayley graph: a_x -- b_{x+s} for s in S, x in G. Returns (2G, edges)."""
    def add(x, y):
        return ((x // m2 + y // m2) % m1) * m2 + (x % m2 + y % m2) % m2
    edges = [(x, G + add(x, s)) for x in range(G) for s in S]
    return 2 * G, edges


def _diff_cover_search(d, seed, end, best):
    """Increase the order of a bi-Cayley diameter-3 graph while a difference cover is found."""
    upper = d * (d - 1) + 1
    G = best[0] // 2 + 1
    while G <= upper and G > d:
        remaining = end - time.monotonic()
        if remaining < 1.0:
            break
        found = None
        for m1, m2 in _groups(G)[:3]:
            remaining = end - time.monotonic()
            if remaining < 1.0:
                break
            budget = max(0.5, min(10.0, 0.35 * remaining))
            try:
                out = lib.run_c(C_DIFF, [d, seed * 1000 + G, budget, m1, m2],
                                timeout=budget + 4)
            except Exception:
                continue
            tok = out.split()
            if len(tok) == 1 + d and tok[0] == "OK":
                found = (m1, m2, [int(x) for x in tok[1:]])
                break
        if found is None:
            break
        m1, m2, S = found
        n, edges = _bicayley(G, m1, m2, S)
        if n > best[0] and lib.is_valid(n, edges, d, 3):
            best = (n, edges)
        G += 1
    return best


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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    # Arc-extended projective plane graphs (valid for D >= 3), fast baseline.
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Bold change for D = 3: bi-Cayley graphs over abelian groups found by a
    # difference-cover search, replacing the old annealing repair.
    if D == 3 and d >= 3 and time.monotonic() < end:
        try:
            best = _diff_cover_search(d, seed, end, best)
        except Exception:
            pass

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Voltage-lift annealing for D >= 4.
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
