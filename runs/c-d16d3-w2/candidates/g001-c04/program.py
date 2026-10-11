import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference covers for cyclic Haar graphs (diameter 3).
#
# For a set S of k residues mod m, the Haar graph H(m, S) has a_i ~ b_{i+s}
# for s in S. It is k-regular, bipartite, and has diameter <= 3 exactly when
# S - S covers all of Z_m (then S - S + s = Z_m for every s, which handles
# the odd distances). The C program searches for such S with simulated
# annealing, for m = m_lo, m_lo+1, ... and prints every m it solves.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static unsigned long long rs = 88172645463325252ULL;

static unsigned long long nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int rnd_int(int n) {
    return (int)(nextr() % (unsigned long long)n);
}

static int K, M;
static int S[64];
static int *cnt;
static char *ins;
static int uncov;
static clock_t T0;

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void dec_r(int r) {
    if (--cnt[r] == 0 && r != 0) uncov++;
}

static void inc_r(int r) {
    if (cnt[r]++ == 0 && r != 0) uncov--;
}

/* Replace element index i (i >= 1) of S by nv, updating difference counts. */
static void replace_elem(int i, int nv) {
    int o = S[i];
    int j;
    for (j = 0; j < K; j++) {
        if (j == i) continue;
        dec_r(md(o - S[j]));
        dec_r(md(S[j] - o));
    }
    for (j = 0; j < K; j++) {
        if (j == i) continue;
        inc_r(md(nv - S[j]));
        inc_r(md(S[j] - nv));
    }
    ins[o] = 0;
    ins[nv] = 1;
    S[i] = nv;
}

static void rebuild(void) {
    int i, j, r;
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(ins, 0, (size_t)M);
    for (i = 0; i < K; i++) ins[S[i]] = 1;
    for (i = 0; i < K; i++)
        for (j = 0; j < K; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    uncov = 0;
    for (r = 1; r < M; r++)
        if (!cnt[r]) uncov++;
}

/* Anneal on the current M until uncov == 0 (returns 1) or the CPU deadline passes (returns 0). */
static int solve(double deadline) {
    const long long iters = 300000;
    for (;;) {
        int i;
        memset(ins, 0, (size_t)M);
        S[0] = 0;
        ins[0] = 1;
        for (i = 1; i < K; i++) {
            int x;
            do {
                x = 1 + rnd_int(M - 1);
            } while (ins[x]);
            S[i] = x;
            ins[x] = 1;
        }
        rebuild();
        if (uncov == 0) return 1;
        {
            long long it;
            for (it = 0; it < iters; it++) {
                double frac, T;
                int idx, nv, o, before, delta;
                if ((it & 4095) == 0) {
                    if ((double)(clock() - T0) / CLOCKS_PER_SEC > deadline) return 0;
                }
                frac = (double)it / (double)iters;
                T = 2.0 * pow(0.05, frac);
                idx = 1 + rnd_int(K - 1);
                nv = 1 + rnd_int(M - 1);
                if (ins[nv]) continue;
                o = S[idx];
                before = uncov;
                replace_elem(idx, nv);
                delta = uncov - before;
                if (delta <= 0 || urand() < exp(-delta / T)) {
                    if (uncov == 0) return 1;
                } else {
                    replace_elem(idx, o);
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    int mlo, mhi, m, i;
    unsigned long long seed;
    double tl;
    if (argc < 6) return 1;
    K = atoi(argv[1]);
    mlo = atoi(argv[2]);
    mhi = atoi(argv[3]);
    seed = strtoull(argv[4], 0, 10);
    tl = atof(argv[5]);
    if (K < 2 || mhi < mlo) return 0;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 1;
    for (i = 0; i < 20; i++) nextr();
    cnt = (int *)malloc(sizeof(int) * (size_t)(mhi + 2));
    ins = (char *)malloc((size_t)(mhi + 2));
    if (!cnt || !ins) return 1;
    T0 = clock();
    for (m = mlo; m <= mhi; m++) {
        double el, remain, slice;
        if (m < K) continue;
        el = (double)(clock() - T0) / CLOCKS_PER_SEC;
        remain = tl - el;
        if (remain < 0.05) break;
        slice = remain * 0.35;
        if (slice < 0.2) slice = remain;
        M = m;
        if (!solve(el + slice)) break;
        printf("%d", m);
        for (i = 0; i < K; i++) printf(" %d", S[i]);
        printf("\n");
        fflush(stdout);
    }
    free(cnt);
    free(ins);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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


def _arc_graph(m, edges, point_lines, S, line_points):
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
        out.append(_arc_graph(m, edges, point_lines, S, line_points))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
# Cyclic Haar graphs from difference covers (diameter 3).
# ----------------------------------------------------------------------------

def _haar_cover(d, budget, seed):
    """Run the C search for S of size d in Z_m with S - S = Z_m; return the largest Haar graph found, or None."""
    k = d
    if k < 2:
        return None
    mlo = max(k, k * (k - 1) // 2 + 1)
    mhi = k * (k - 1) + 1
    if mlo > mhi:
        return None
    try:
        out = lib.run_c(C_SOURCE, [k, mlo, mhi, seed, f"{budget:.2f}"],
                        stdin_graph=None, timeout=budget + 5)
    except RuntimeError:
        return None
    best = None
    for line in out.splitlines():
        parts = line.split()
        if len(parts) != k + 1:
            continue
        try:
            vals = [int(x) for x in parts]
        except ValueError:
            continue
        best = vals  # the C program prints increasing m, so the last line is the largest
    if best is None:
        return None
    m, S = best[0], best[1:]
    return lib.haar_graph(m, S)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Arc-extended projective plane graphs (the conic gives the old record for d = 16).
        arc_deadline = start + 0.2 * time_limit
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

        # Main new construction: cyclic Haar graphs from difference covers.
        elapsed = time.monotonic() - start
        budget = max(1.0, 0.75 * time_limit - elapsed)
        hc = _haar_cover(d, budget, seed)
        if hc is not None:
            consider(hc[0], hc[1])

    if D >= 4 and time.monotonic() - start < 0.9 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
