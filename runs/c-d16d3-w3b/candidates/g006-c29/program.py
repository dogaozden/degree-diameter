import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D = 3: cyclic bi-Cayley (Haar) graphs from difference
# covers.
#
# Let G = Z_m and let S be a d-subset of G with 0 in S (a shift of S gives an
# isomorphic graph, so this is no restriction). The Haar graph on a_x, b_y with
# a_x ~ b_y iff y - x in S is d-regular and bipartite on 2m vertices. Two a's
# are at distance 2 iff their difference lies in S - S. Since 0 is in S, every
# a-b pair is within distance 3 once S - S covers G. So the graph is valid for
# D = 3 exactly when every nonzero residue is a difference of two elements of S.
# The counting bound is m <= d(d-1)+1, which gives 2(d^2-d+1) vertices. Perfect
# difference sets are the extreme case; for d = 16 the question is how far above
# m = 197 (record 394 vertices) a near-perfect cover can be found.
#
# The C engine searches m upward from a low start. For each m it runs simulated
# annealing over the d-1 nonzero elements of S, minimizing the number of
# uncovered nonzero residues. Moves are partly focused: pick an uncovered
# difference x and place an element at S[j] +/- x.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXM 1400

static int d, m;
static int S[MAXD];
static int inS[MAXM];
static int cnt[MAXM];
static int uncov;                 /* number of x in 1..m-1 with cnt[x] == 0 */
static int best_m = 0;
static int bestS[MAXD];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int modm(int x) { x %= m; if (x < 0) x += m; return x; }

static void inc_pair(int x) { if (cnt[x]++ == 0) uncov--; }
static void dec_pair(int x) { if (--cnt[x] == 0) uncov++; }

/* Remove element k (current value S[k]) from the difference counts. */
static void remove_el(int k) {
    for (int j = 0; j < d; j++) {
        if (j == k) continue;
        dec_pair(modm(S[k] - S[j]));
        dec_pair(modm(S[j] - S[k]));
    }
}

/* Put value v into slot k and add its differences. */
static void add_el(int k, int v) {
    S[k] = v;
    for (int j = 0; j < d; j++) {
        if (j == k) continue;
        inc_pair(modm(v - S[j]));
        inc_pair(modm(S[j] - v));
    }
}

static void reset_state(void) {
    memset(cnt, 0, sizeof(int) * (size_t)m);
    memset(inS, 0, sizeof(int) * (size_t)m);
    uncov = m - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int k = 1; k < d; k++) {
        int v;
        do { v = 1 + rint_(m - 1); } while (inS[v]);
        inS[v] = 1;
        S[k] = v;
        for (int j = 0; j < k; j++) {
            inc_pair(modm(v - S[j]));
            inc_pair(modm(S[j] - v));
        }
    }
}

static void propose(int *kp, int *vp) {
    int k = 1 + rint_(d - 1);
    int v = -1;
    if (uncov > 0 && rdbl() < 0.6) {
        int target = -1, nu = 0;
        for (int x = 1; x < m; x++) {
            if (cnt[x] == 0) { nu++; if (rint_(nu) == 0) target = x; }
        }
        int j = rint_(d - 1);
        if (j >= k) j++;                       /* j in 0..d-1, j != k */
        int cand = (rnd() & 1ULL) ? modm(S[j] + target) : modm(S[j] - target);
        if (cand != 0 && !inS[cand]) v = cand;
    }
    if (v < 0) {
        do { v = 1 + rint_(m - 1); } while (inS[v]);
    }
    *kp = k;
    *vp = v;
}

static void apply_move(int k, int v) {
    int old = S[k];
    remove_el(k);
    add_el(k, v);
    inS[old] = 0;
    inS[v] = 1;
}

static void revert_move(int k, int v, int old) {
    remove_el(k);
    add_el(k, old);
    inS[v] = 0;
    inS[old] = 1;
}

static int search_m(int mm, double seconds) {
    m = mm;
    clock_t st = clock();
    const long L = 300000;
    for (;;) {
        reset_state();
        for (long t = 0; t < L && uncov > 0; t++) {
            if ((t & 1023) == 0 &&
                (double)(clock() - st) / CLOCKS_PER_SEC > seconds) return 0;
            double T = 0.9 * (1.0 - (double)t / (double)L) + 0.08;
            int k, v;
            propose(&k, &v);
            int old = S[k];
            int before = uncov;
            apply_move(k, v);
            int delta = uncov - before;
            if (delta > 0 && rdbl() >= exp(-(double)delta / T)) {
                revert_move(k, v, old);
            }
        }
        if (uncov == 0) {
            best_m = m;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            return 1;
        }
        if ((double)(clock() - st) / CLOCKS_PER_SEC > seconds) return 0;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    if (d < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    long mmax_l = (long)d * (d - 1) + 1;
    int mmax = mmax_l < MAXM - 1 ? (int)mmax_l : MAXM - 1;
    int lo = (argc >= 6) ? atoi(argv[5]) : (mmax * 4) / 5;
    if (lo < d + 1) lo = d + 1;

    clock_t t0 = clock();
    for (int mm = lo; mm <= mmax; mm++) {
        double remain = budget - (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (remain <= 0.05) break;
        double slice = remain / 10.0;
        if (slice > 4.0) slice = 4.0;
        if (slice < 0.2) slice = 0.2;
        if (slice > remain) slice = remain;
        search_m(mm, slice);
    }

    if (best_m == 0) { printf("0 0\n"); return 0; }
    int mm = best_m;
    printf("%d %d\n", 2 * mm, mm * d);
    for (int i = 0; i < mm; i++) {
        for (int a = 0; a < d; a++) {
            int j = (i + bestS[a]) % mm;
            printf("%d %d\n", i, mm + j);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Fallback constructions (kept from the parent). Arc-extended projective plane
# graphs give the D = 3 fallback (394 for d = 16). W(q) gives D = 4.
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
    end = t_start + 0.85 * time_limit - 2.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    if D == 3:
        # Arc-extended projective plane graph (the parent's construction, 394 for d = 16).
        arc_end = min(end, t_start + 0.3 * time_limit)
        cands = _arc_extensions(d, arc_end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

        # New main search: cyclic difference covers, i.e. Haar graphs on Z_m
        # with a d-subset S, 0 in S, and S - S = Z_m. Gives 2m vertices.
        cbudget = end - time.monotonic() - 0.5
        mmax = d * (d - 1) + 1
        if d >= 2 and cbudget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget, 2), int(0.8 * mmax)],
                                stdin_graph=None, timeout=cbudget + 15)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
