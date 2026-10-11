"""Bold variant: for D = 3, search cyclic Haar graphs H(m, S) with |S| = d directly.

H(m, S) is bipartite and d-regular on 2m vertices. If every nonzero residue of Z_m is a
difference s - t of two elements of S (a difference cover), then every pair of vertices is within
distance 3, so the diameter is at most 3. C finds such covers by simulated annealing for
increasing m, starting above the current best order. Python keeps the projective-plane and
arc-extended constructions as fallbacks, and checks every result with lib.is_valid.
"""
import random
import time

import lib

C_SOURCE = r'''
/* Difference-cover search for bipartite Haar graphs (D = 3).
 *
 * Usage:   prog d D seed time_limit [m0]
 * Output:  "n m" then edges, for the largest m >= m0 found with a difference cover, or "0 0".
 *
 * Graph: vertices i (side A) and M+j (side B), i ~ M + ((i + s) mod M) for s in S, |S| = d.
 * Every nonzero residue must equal s - t for some s, t in S (S - S = Z_M). Then A-A and B-B
 * distances are at most 2, and A-B distances are at most 3.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 512
#define MAXK 40

static int K, M;
static int S[MAXK], BEST[MAXK];
static int cnt[MAXM];
static int unc;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int in_S(int v) {
    for (int t = 0; t < K; t++)
        if (S[t] == v) return 1;
    return 0;
}

/* Remove element i from S, updating difference counts and the number of uncovered residues. */
static void remove_elem(int i) {
    for (int t = 0; t < K; t++) {
        if (t == i) continue;
        int a = S[i] - S[t];
        if (a < 0) a += M;
        if (--cnt[a] == 0) unc++;
        int b = M - a;
        if (--cnt[b] == 0) unc++;
    }
}

/* Put v at position i and add its differences. */
static void add_elem(int i, int v) {
    S[i] = v;
    for (int t = 0; t < K; t++) {
        if (t == i) continue;
        int a = v - S[t];
        if (a < 0) a += M;
        if (cnt[a]++ == 0) unc--;
        int b = M - a;
        if (cnt[b]++ == 0) unc--;
    }
}

static void full_init(void) {
    memset(cnt, 0, sizeof cnt);
    for (int i = 0; i < K; i++)
        for (int t = 0; t < K; t++) {
            if (t == i) continue;
            int a = S[i] - S[t];
            if (a < 0) a += M;
            cnt[a]++;
        }
    unc = 0;
    for (int x = 1; x < M; x++)
        if (cnt[x] == 0) unc++;
}

/* Simulated annealing on S for the current M. Returns 1 when S covers Z_M \ {0}. */
static int anneal(double t_stop) {
    for (int i = 0; i < K; i++) S[i] = -1;
    for (int i = 0; i < K; i++) {
        int v;
        do { v = rndint(M); } while (in_S(v));
        S[i] = v;
    }
    full_init();
    long it = 0;
    const long cyc = 300000;
    while (unc > 0) {
        if ((++it & 4095) == 0 && now() > t_stop) return 0;
        double ph = (double)(it % cyc) / (double)cyc;
        double T = 0.06 + 0.8 * (1.0 - ph);
        int i = rndint(K);
        int v;
        do { v = rndint(M); } while (in_S(v));
        int old = S[i];
        int before = unc;
        remove_elem(i);
        add_elem(i, v);
        int delta = unc - before;
        if (delta > 0 && rnd01() >= exp(-(double)delta / T)) {
            remove_elem(i);
            add_elem(i, old);
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [m0]\n", argv[0]);
        return 2;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int m0 = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    double tend = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    K = d;
    if (D != 3 || K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    int mmax = K * (K - 1) + 1;   /* a difference cover needs K(K-1) >= M - 1 */
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    int m = m0 > K + 1 ? m0 : K + 1;
    int best_m = 0;

    for (M = m; M <= mmax && now() < tend;) {
        int ok = 0;
        for (int att = 0; att < 3 && !ok && now() < tend; att++) {
            double rem = tend - now();
            double slice = rem / 3.0;
            if (slice < 0.5) slice = rem;
            ok = anneal(now() + slice);
        }
        if (!ok) break;
        best_m = M;
        memcpy(BEST, S, sizeof(int) * (size_t)K);
        M++;
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    M = best_m;
    printf("%d %d\n", 2 * M, M * K);
    for (int i = 0; i < M; i++)
        for (int t = 0; t < K; t++)
            printf("%d %d\n", i, M + (i + BEST[t]) % M);
    return 0;
}
'''


def _pg_data(q):
    """Points/lines of PG(2, q): point i and line i share the vector pts[i]."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG(2,q) incidence plus, per element P of S, a new A-vertex on the lines through P
    and a new B-vertex on the points of line P."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.15 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

    # Bold path (D = 3): cyclic Haar graphs from difference covers, searched in C.
    if D == 3 and d >= 2 and best[0] < lib.moore_bound(d, D):
        budget = 0.80 * time_limit - (time.monotonic() - t0) - 1.5
        if budget > 1.0:
            m0 = best[0] // 2 + 1
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), m0],
                                 timeout=budget + 5)
                n, e = lib.parse_graph_text(text)
                if n > best[0]:
                    consider((n, e))
            except (RuntimeError, ValueError):
                pass   # keep the best construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
