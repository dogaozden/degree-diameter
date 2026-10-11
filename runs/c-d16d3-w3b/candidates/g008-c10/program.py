import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference-cover search for cyclic Haar graphs (diameter 3).
#
# Take S, a set of d residues in Z_m, and the bipartite graph a_i -- b_{i+s}
# (s in S). Each vertex is joined to exactly d others. The graph has diameter
# at most 3 whenever S - S covers all of Z_m: A-A distances come from S - S,
# and every A-B distance is within S - S + S, which then covers Z_m as well.
# So the order is 2m. The engine searches for the largest m it can cover with
# simulated annealing on the number of uncovered nonzero residues.
# Output: "n m" then edges, or "0 0" if nothing was found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXM 4096

static int d, D, m;
static int S[MAXD];
static int inS[MAXM];
static int cnt[MAXM];
static int uncov;
static uint64_t rs = 1;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int md(int x) {
    x %= m;
    if (x < 0) x += m;
    return x;
}

static void dec(int x) {
    cnt[x]--;
    if (cnt[x] == 0) uncov++;
}
static void inc(int x) {
    if (cnt[x] == 0) uncov--;
    cnt[x]++;
}

/* Remove the element at index i (its ordered differences with the others). */
static void rem_at(int i) {
    int v = S[i];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        dec(md(v - S[j]));
        dec(md(S[j] - v));
    }
    inS[v] = 0;
}

/* Put value v at index i and add its ordered differences. */
static void add_at(int i, int v) {
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        inc(md(v - S[j]));
        inc(md(S[j] - v));
    }
    S[i] = v;
    inS[v] = 1;
}

static void recompute(void) {
    for (int x = 0; x < m; x++) { cnt[x] = 0; inS[x] = 0; }
    for (int i = 0; i < d; i++) inS[S[i]] = 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    uncov = 0;
    for (int x = 1; x < m; x++) if (cnt[x] == 0) uncov++;
}

static int out_of_time(clock_t t0, double tl) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC > tl;
}

/* Anneal until S - S covers Z_m (returns 1) or time runs out (returns 0). */
static int anneal_m(clock_t t0, double tl) {
    const long L = 400000;
    for (;;) {
        S[0] = 0;  /* translation invariance: fix one element */
        for (int i = 1; i < d; i++) {
            int y, ok;
            do {
                y = 1 + rint_(m - 1);
                ok = 1;
                for (int k = 0; k < i; k++) if (S[k] == y) { ok = 0; break; }
            } while (!ok);
            S[i] = y;
        }
        recompute();
        for (long it = 0; it < L && uncov > 0; it++) {
            if ((it & 4095) == 0 && out_of_time(t0, tl)) return 0;
            double T = 1.5 * pow(0.03, (double)it / (double)L);
            int i = 1 + rint_(d - 1);
            int y = rint_(m);
            if (inS[y]) continue;
            int old = S[i];
            int u0 = uncov;
            rem_at(i);
            add_at(i, y);
            int delta = uncov - u0;
            if (delta > 0 && rdbl() >= exp(-(double)delta / T)) {
                rem_at(i);
                add_at(i, old);
            }
        }
        if (uncov == 0) return 1;
        if (out_of_time(t0, tl)) return 0;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int mstart = (argc > 5) ? atoi(argv[5]) : d;
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int k = 0; k < 8; k++) rnd();
    (void)D;
    clock_t t0 = clock();
    if (d < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    if (mstart < d) mstart = d;
    int maxm = d * (d - 1) + 1;
    if (maxm > MAXM - 1) maxm = MAXM - 1;

    int bestm = 0;
    int bestS[MAXD];
    for (int mm = mstart; mm <= maxm; mm++) {
        m = mm;
        if (!anneal_m(t0, tl)) break;
        bestm = mm;
        memcpy(bestS, S, sizeof(int) * (size_t)d);
        if (out_of_time(t0, tl)) break;
    }
    if (bestm == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestm, bestm * d);
    for (int i = 0; i < bestm; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, bestm + (i + bestS[k]) % bestm);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

def _largest_pp(x):
    """Largest prime power c with 2 <= c <= x, or None."""
    for c in range(x, 1, -1):
        if lib.is_prime_power(c):
            return c
    return None


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
    """Randomized greedy arc with all loads <= s; returns the largest found."""
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
    """Grow the arc S by ejection moves; returns the best set seen."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG(2,q) incidence plus a new A and a new B vertex per element of S."""
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


def _arc_candidate(d, deadline, rng):
    """Arc-extended PG(2, q) for the largest prime power q <= d-2 (spare degree s = d-q-1 >= 1)."""
    q = _largest_pp(d - 2)
    if q is None:
        return None
    s = d - q - 1
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    best_set = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
    best_set = _swap_improve(best_set, s, m, point_lines, line_points, rng,
                             min(deadline, time.monotonic() + 2.0), 6000)
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if _loads_ok(cs, s, m, point_lines, line_points):
            cs = _swap_improve(cs, s, m, point_lines, line_points, rng,
                               min(deadline, time.monotonic() + 1.0), 3000)
            if len(cs) > len(best_set):
                best_set = cs
    if not _loads_ok(best_set, s, m, point_lines, line_points):
        return None
    return _arc_graph(m, edges, point_lines, line_points, best_set)


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
# Difference-cover search (diameter 3, and valid for any D >= 3).
# ----------------------------------------------------------------------------

def _difference_cover(d, D, seed, budget):
    """Run the C search for a cyclic Haar graph; returns (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), d],
                    stdin_graph=None, timeout=budget + 10)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit - 1.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, edges = g
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, list(edges))

    if D >= 3:
        # Projective plane incidence graph: degree q+1 <= d, diameter 3.
        q = _largest_pp(d - 1)
        if q is not None:
            try:
                consider(lib.projective_plane_incidence(q))
            except Exception:
                pass
        # Arc-extended projective plane (the parent's construction).
        if time.monotonic() < end:
            try:
                consider(_arc_candidate(d, min(end, time.monotonic() + 3.0), rng))
            except Exception:
                pass

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Main bold search: cyclic difference covers, using the rest of the budget.
    if D >= 3 and d >= 2:
        budget = end - time.monotonic() - 2.0
        if budget > 1.0:
            try:
                consider(_difference_cover(d, D, seed, budget))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
