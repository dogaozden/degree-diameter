"""Haar-graph difference-covering search for bipartite degree-diameter graphs.

For D >= 3, the bipartite Haar graph H(Z_m, S) with |S| = d is d-regular, has 2m vertices,
and has diameter at most 3 whenever S - S covers Z_m. C searches for such a covering set S
(simulated annealing over difference counts) for the largest m it can reach. Python keeps the
projective-plane and Araujo-Pardo-Lopez constructions and the arc-extended planes as safe
fallbacks, and every returned graph is checked with lib.is_valid.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Usage: prog d D seed time_limit [m_start]
 * Searches, for m = m_start, m_start+1, ..., a set S of d residues mod m whose
 * pairwise differences cover all of Z_m (a "difference covering").  Such S gives the
 * Haar graph H(Z_m, S): d-regular, bipartite, 2m vertices, diameter <= 3.
 * Output: "m s_1 ... s_d" for the largest m found, or "0".
 */

#define MAXK 40
#define MAXM 4200

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];      /* cnt[r] = number of ordered pairs (s,t), s != t, with s - t = r */
static int uncovered;      /* number of r in 1..M-1 with cnt[r] == 0 */

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void upd(int r, int delta) {
    if (delta > 0) {
        if (cnt[r] == 0) uncovered--;
        cnt[r]++;
    } else {
        cnt[r]--;
        if (cnt[r] == 0) uncovered++;
    }
}

static void pair_upd(int x, int y, int delta) {
    upd(md(x - y), delta);
    upd(md(y - x), delta);
}

static void remove_idx(int i) {
    for (int j = 0; j < K; j++)
        if (j != i) pair_upd(S[i], S[j], -1);
}

static void add_idx(int i) {
    for (int j = 0; j < K; j++)
        if (j != i) pair_upd(S[i], S[j], 1);
}

static void init_state(void) {
    memset(inS, 0, sizeof(int) * (size_t)M);
    memset(cnt, 0, sizeof(int) * (size_t)M);
    for (int j = 0; j < K; j++) {
        int v;
        do {
            v = rndint(M);
        } while (inS[v]);
        inS[v] = 1;
        S[j] = v;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    uncovered = 0;
    for (int r = 1; r < M; r++)
        if (cnt[r] == 0) uncovered++;
}

/* Simulated annealing on the number of uncovered residues. Returns 1 on success. */
static int search_cover(double until) {
    init_state();
    long step = 0;
    const long L = 300000;   /* length of one annealing cycle */
    while (uncovered > 0) {
        if ((step & 1023) == 0 && now() > until) return 0;
        long phase = step % L;
        double T = exp(-3.0 * (double)phase / (double)L);
        step++;

        int r = -1;
        for (int t = 0; t < 64; t++) {
            int c = 1 + rndint(M - 1);
            if (cnt[c] == 0) {
                r = c;
                break;
            }
        }
        int v, i;
        if (r > 0 && (rnd() & 1)) {
            /* focused move: new element v = S[k] +- r covers the uncovered difference r */
            int k = rndint(K);
            int sgn = (rnd() & 1) ? 1 : -1;
            v = md(S[k] + sgn * r);
            if (inS[v]) continue;
            i = (k + 1 + rndint(K - 1)) % K;
        } else {
            v = rndint(M);
            if (inS[v]) continue;
            i = rndint(K);
        }

        int old = S[i];
        int oldU = uncovered;
        remove_idx(i);
        S[i] = v;
        add_idx(i);
        int delta = uncovered - oldU;
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            inS[old] = 0;
            inS[v] = 1;
        } else {
            remove_idx(i);
            S[i] = old;
            add_idx(i);
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [m_start]\n", argv[0]);
        return 2;
    }
    int d = atoi(argv[1]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mstart = argc > 5 ? atoi(argv[5]) : 0;
    double tend = now() + limit * 0.9;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    K = d;
    if (K < 2 || K > MAXK) {
        printf("0\n");
        return 0;
    }
    int mmax = K * (K - 1) + 1;   /* a covering needs K(K-1)+1 >= m */
    if (mmax >= MAXM) mmax = MAXM - 1;

    int m = mstart > K + 1 ? mstart : K + 1;
    int best_m = 0;
    int best_S[MAXK];
    int fails = 0;
    while (m <= mmax && now() < tend && fails < 5) {
        M = m;
        double left = tend - now();
        double slice = left * 0.15;
        if (slice < 0.3) slice = 0.3;
        double until = now() + slice;
        if (until > tend) until = tend;
        if (search_cover(until)) {
            best_m = m;
            memcpy(best_S, S, sizeof(int) * (size_t)K);
            fails = 0;
        } else {
            fails++;
        }
        m++;
    }
    if (best_m == 0) {
        printf("0\n");
        return 0;
    }
    printf("%d", best_m);
    for (int j = 0; j < K; j++) printf(" %d", best_S[j]);
    printf("\n");
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
    and a new B-vertex on the points of line P. Diameter 3."""
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
        try:
            consider(known_start(d, D))
        except ValueError:
            pass
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.12 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

    # Difference-covering Haar graphs: 2m vertices for a d-set S with S - S = Z_m.
    if D >= 3 and d >= 2:
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
        if budget > 0.5:
            mstart = best[0] // 2 + 1   # a covering must beat the current order
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mstart],
                                 timeout=budget + 5)
                vals = [int(x) for x in text.split()]
                if len(vals) == d + 1 and vals[0] >= mstart:
                    m = vals[0]
                    _, edges = lib.haar_graph(m, vals[1:])
                    consider((2 * m, edges))
            except (RuntimeError, ValueError):
                pass   # keep the best construction found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
