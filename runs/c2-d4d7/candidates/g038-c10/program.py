"""Cyclic Haar-graph search with local-search shift sets, for the weakest target (d=4, D=7).

Change from the parent: the non-metacyclic voltage-lift search and grow-by-two annealing are replaced
by a different construction. Bipartite Haar graphs H(m,S) on Z_m have vertices A_i and B_i, with
A_i adjacent to B_{i+s} for s in S, |S| = d. Each side is transitive under the shift automorphism,
so the all-pairs diameter test reduces to two BFS runs, from A_0 and from B_0. A hill-climb over the
shift set S minimises the number of vertices not reached within D from those two sources. The search
increases m past the current best order. The best known start (the incidence graph of the split
Cayley hexagon H(3), order 728, diameter 6, valid for D = 7) sets the lower bound on m.

Every returned graph is checked with lib.is_valid. The fallback is the best known start or K_{d,d}.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4800
#define MAXD 16

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int dist[MAXV], que[MAXV];

/* Haar graph H(m,S): vertices 0..m-1 are A_i, m..2m-1 are B_j.
 * A_i ~ B_{i+s}, equivalently B_j ~ A_{j-s}, for s in S. */
static int reached(int m, const int *S, int src) {
    int nv = 2 * m, h = 0, t = 0;
    for (int i = 0; i < nv; i++) dist[i] = -1;
    dist[src] = 0;
    que[t++] = src;
    while (h < t) {
        int v = que[h++];
        if (dist[v] >= D) continue;
        for (int k = 0; k < d; k++) {
            int u;
            if (v < m) u = m + (v + S[k]) % m;
            else u = ((v - m) - S[k] + m) % m;
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                que[t++] = u;
            }
        }
    }
    return t;
}

/* Vertices not reached within D from A_0 or from B_0. Zero means the graph is valid. */
static int unreached(int m, const int *S) {
    return 4 * m - reached(m, S, 0) - reached(m, S, m);
}

/* Shift sets are normalised to contain 0; translating S is an isomorphism. */
static void random_set(int m, int *S) {
    S[0] = 0;
    for (int k = 1; k < d; k++) {
        for (;;) {
            int x = rndint(m), ok = 1;
            for (int j = 0; j < k; j++)
                if (S[j] == x) { ok = 0; break; }
            if (ok) { S[k] = x; break; }
        }
    }
}

static int climb(int m, int *S, double until, long iters) {
    if (m <= d) return 0;
    int cur = unreached(m, S);
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int k = 1 + rndint(d - 1);
        int old = S[k];
        int x;
        for (;;) {
            int ok = 1;
            x = rndint(m);
            for (int j = 0; j < d; j++)
                if (S[j] == x) { ok = 0; break; }
            if (ok) break;
        }
        S[k] = x;
        int nc = unreached(m, S);
        if (nc <= cur || rnd01() < 0.01) cur = nc;
        else S[k] = old;
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mmin = atoi(argv[5]), mmax = atoi(argv[6]);
    double until = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    if (mmin < d + 1) mmin = d + 1;
    if (mmax > MAXV / 2) mmax = MAXV / 2;

    int bestm = 0, bestS[MAXD];
    int m = mmin;
    while (m <= mmax && now() < until) {
        int S[MAXD];
        random_set(m, S);
        if (climb(m, S, until, 4000)) {
            bestm = m;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            m++;
        }
    }

    if (bestm == 0) {
        printf("0 0\n");
        return 0;
    }
    long ne = (long)bestm * d;
    printf("%d %ld\n", 2 * bestm, ne);
    for (int i = 0; i < bestm; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, bestm + (i + bestS[k]) % bestm);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention yields a graph that passes lib.is_valid with diameter 6.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates that may be valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best

    mmin = max(d + 1, best[0] // 2 + 1)
    mmax = min(lib.moore_bound(d, D) // 2, 1100)
    if mmin > mmax:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mmin, mmax],
                         timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
