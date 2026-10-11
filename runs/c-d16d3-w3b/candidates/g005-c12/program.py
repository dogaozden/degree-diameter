import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic Haar graphs with a difference-cover search (diameter 3, bipartite).
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, |S| = d, i in Z_m. It is d-regular
# and bipartite on 2m vertices. It has diameter 3 iff
#   (1) S - S covers every nonzero residue (same-side pairs get a common neighbour),
#   (2) S - S + S covers all of Z_m (a_i to b_j).
# Condition (1) is a difference-cover problem. Here C runs simulated annealing on S
# (with 0 in S, WLOG) for increasing m, minimising the number of uncovered
# differences, and prints the largest m for which a valid S was found.
# This is a different construction from the arc-extended projective planes.
# ----------------------------------------------------------------------------

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXD 40

static int d, D, m;
static int S[MAXD];
static int inS[MAXM];
static int cnt[MAXM];
static unsigned char mark[MAXM];
static int unc;
static uint64_t rs = 1;
static double TL = 0.0;
static clock_t C0;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - C0) / CLOCKS_PER_SEC; }

static int md(int a, int b) { int x = (a - b) % m; return x < 0 ? x + m : x; }

/* cnt[x] = number of ordered pairs (s, t), s != t in the active set, with s - t = x. */
static void bump(int x, int delta) {
    int old = cnt[x];
    cnt[x] = old + delta;
    if (old == 0 && cnt[x] > 0) unc--;
    else if (old > 0 && cnt[x] == 0) unc++;
}

/* Add (delta=+1) or remove (delta=-1) the differences between value v at index i and all j < k, j != i. */
static void contrib(int i, int v, int k, int delta) {
    for (int j = 0; j < k; j++) {
        if (j == i) continue;
        bump(md(v, S[j]), delta);
        bump(md(S[j], v), delta);
    }
}

static void set_value(int i, int nv) {
    contrib(i, S[i], d, -1);
    S[i] = nv;
    contrib(i, nv, d, +1);
}

static void init_random(void) {
    memset(inS, 0, sizeof(int) * (size_t)m);
    memset(cnt, 0, sizeof(int) * (size_t)m);
    unc = m - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int y;
        do { y = rint_(m); } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
        contrib(i, y, i + 1, +1);
    }
}

/* Number of nonzero x in Z_m not of the form s - t + u with s, t, u in S. */
static int triple_uncovered(void) {
    memset(mark, 0, (size_t)m);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            for (int c = 0; c < d; c++) {
                int v = (S[a] - S[b] + S[c]) % m;
                if (v < 0) v += m;
                mark[v] = 1;
            }
    int bad = 0;
    for (int x = 1; x < m; x++) if (!mark[x]) bad++;
    return bad;
}

static int anneal(long iters, double T0, double T1) {
    for (long it = 0; it < iters; it++) {
        if ((it & 65535) == 0 && elapsed() > TL) return 0;
        if (unc == 0 && triple_uncovered() == 0) return 1;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = 1 + rint_(d - 1);
        int y = rint_(m);
        if (inS[y]) continue;
        int x = S[i];
        int old = unc;
        set_value(i, y);
        int delta = unc - old;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            inS[x] = 0;
            inS[y] = 1;
        } else {
            set_value(i, x);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;
    C0 = clock();
    if (D != 3 || d < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    int best_m = 0;
    int bestS[MAXD];
    for (int mm = d + 1; mm < MAXM; mm++) {
        int found = 0;
        for (int att = 0; att < 60 && !found; att++) {
            if (elapsed() > TL) break;
            m = mm;
            init_random();
            found = anneal(1200000L, 1.0, 0.12);
        }
        if (!found) break;
        best_m = mm;
        memcpy(bestS, S, sizeof(int) * (size_t)d);
    }
    if (best_m == 0) { printf("0 0\n"); return 0; }

    long E = (long)best_m * d;
    printf("%d %ld\n", 2 * best_m, E);
    for (int i = 0; i < best_m; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, best_m + (i + bestS[k]) % best_m);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Fallback.
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
    t_start = time.monotonic()
    end = t_start + 0.88 * time_limit - 1.0
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

    if D == 3:
        # Deterministic arc-extended projective plane graphs (fast).
        for g in sorted(_arc_extensions(d, end, random.Random(seed * 7919 + d)), key=lambda t: -t[0]):
            consider(g)
        # New construction: cyclic Haar graphs found by difference-cover annealing.
        remaining = end - time.monotonic()
        if remaining > 2.0:
            try:
                out = lib.run_c(HAAR_C, [d, D, seed, round(remaining, 2)],
                                stdin_graph=None, timeout=remaining + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    if D >= 4:
        if time.monotonic() < end:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
