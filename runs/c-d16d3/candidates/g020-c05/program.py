"""Diameter-3 bipartite search via cyclic Haar graphs with covering connection sets.

For D = 3, the Haar graph H(Z_n, B) with |B| = d (point x is joined to line g iff x - g is in B)
has diameter 3 when B - B covers Z_n \\ {0} (same-side pairs share a neighbour) and
B - B + B covers Z_n (opposite-side pairs are within distance 3). Such graphs have order 2n,
with n <= d(d-1)+1, so the Moore-type ceiling is 2(d^2-d+1). The C engine runs simulated
annealing on B for n = d+1, d+2, ... and keeps the largest n it reaches. Every candidate is
re-checked with lib.is_valid. Fallbacks are the arc-extended PG(2,q) graphs (D >= 3),
the generalized quadrangle W(q) (D >= 4), and K_{d,d} (diameter 2).
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 512

static int n, k;
static int B[MAXK];
static int inB[MAXM];
static int cnt[MAXM];
static int mark[MAXM];
static int cost;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int md(int x) {
    x %= n;
    if (x < 0) x += n;
    return x;
}

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* cost = number of nonzero residues d with no ordered pair (b, b') in B^2, b - b' = d */
static void dec(int d) {
    if (--cnt[d] == 0 && d != 0) cost++;
}

static void inc(int d) {
    if (cnt[d]++ == 0 && d != 0) cost--;
}

static void remove_at(int i) {
    int x = B[i];
    for (int j = 0; j < k; j++) {
        if (j != i) {
            dec(md(x - B[j]));
            dec(md(B[j] - x));
        }
    }
    inB[x] = 0;
}

static void insert_at(int i, int y) {
    for (int j = 0; j < k; j++) {
        if (j != i) {
            inc(md(y - B[j]));
            inc(md(B[j] - y));
        }
    }
    B[i] = y;
    inB[y] = 1;
}

static void rebuild(void) {
    memset(cnt, 0, sizeof(cnt));
    cost = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            if (i != j) cnt[md(B[i] - B[j])]++;
    for (int d = 1; d < n; d++)
        if (cnt[d] == 0) cost++;
}

/* Check that B - B + B covers all of Z_n (opposite-side pairs at distance <= 3). */
static int triple_ok(void) {
    memset(mark, 0, sizeof(mark));
    for (int a = 0; a < k; a++)
        for (int b = 0; b < k; b++)
            for (int c = 0; c < k; c++)
                mark[md(B[a] - B[b] + B[c])] = 1;
    for (int t = 0; t < n; t++)
        if (!mark[t]) return 0;
    return 1;
}

/* Simulated annealing for a valid B in Z_n, with restarts, until the deadline. */
static int search_n(double deadline) {
    const long L = 400000;
    while (now() < deadline) {
        memset(inB, 0, sizeof(inB));
        for (int i = 0; i < k; i++) {
            int y;
            do {
                y = (int)(rnd() % (uint64_t)n);
            } while (inB[y]);
            B[i] = y;
            inB[y] = 1;
        }
        rebuild();
        for (long it = 0; it < L; it++) {
            if (cost == 0 && triple_ok()) return 1;
            if ((it & 1023) == 0 && now() >= deadline) return 0;
            double T = 0.8 * pow(0.05 / 0.8, (double)it / (double)L);
            int i = (int)(rnd() % (uint64_t)k);
            int c;
            do {
                c = (int)(rnd() % (uint64_t)n);
            } while (inB[c]);
            int x = B[i];
            int old = cost;
            remove_at(i);
            insert_at(i, c);
            int delta = cost - old;
            if (!(delta <= 0 || urand() < exp(-(double)delta / T))) {
                remove_at(i);
                insert_at(i, x);
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    k = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    if (k < 2 || k > MAXK) {
        printf("0 0\n");
        return 0;
    }
    int maxn = k * (k - 1) + 1;
    if (maxn > MAXM - 1) maxn = MAXM - 1;

    double t_end = now() + budget;
    int best_n = 0;
    int best_B[MAXK];
    for (n = k + 1; n <= maxn; n++) {
        double rem = t_end - now();
        if (rem < 0.05) break;
        double cap = rem > 4.0 ? 0.5 * rem : rem;
        if (search_n(now() + cap)) {
            best_n = n;
            memcpy(best_B, B, sizeof(int) * k);
        } else {
            break;
        }
    }
    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, k);
    for (int i = 0; i < k; i++) printf("%d%c", best_B[i], i + 1 < k ? ' ' : '\n');
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3, Python only).
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
# Generalized quadrangle W(q) incidence graph (diameter 4), for D >= 4.
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
# Cyclic Haar-graph search (D = 3).
# ----------------------------------------------------------------------------

def _haar_candidate(d, seed, budget):
    """Run the C covering-set annealer; return the Haar graph H(Z_n, B) or None."""
    text = lib.run_c(C_SOURCE, [d, seed, f"{budget:.2f}"], stdin_graph=None,
                     timeout=budget + 10.0)
    nums = text.split()
    if len(nums) < 2:
        return None
    n, k = int(nums[0]), int(nums[1])
    S = [int(x) for x in nums[2:2 + k]]
    if n <= 0 or k != d or len(S) != k:
        return None
    return lib.haar_graph(n, S)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    rng = random.Random(seed * 7919 + d)

    def consider(g):
        nonlocal best
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    if D == 3:
        for g in _arc_extensions(d, t0 + 0.10 * time_limit, rng):
            consider(g)
        budget = 0.80 * time_limit - (time.monotonic() - t0) - 3.0
        if budget >= 1.0:
            try:
                consider(_haar_candidate(d, seed, budget))
            except Exception:
                pass
    elif D >= 4:
        for g in _arc_extensions(d, t0 + 0.10 * time_limit, rng):
            consider(g)
        consider(_best_gq(d))

    return best
