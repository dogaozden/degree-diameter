"""Haar-graph search program. Python builds the strongest closed-form baseline it can
(projective planes, arc extensions of PG(2,q), Araujo-Pardo-Lopez, W(q) for D = 4). The C engine
then searches cyclic Haar graphs H(m, S): vertices a_i and b_j, with a_i joined to b_{i+s} for each
s in S, |S| = d, S a subset of Z_m. Each candidate m is checked by BFS from a_0 and b_0 only, since
translations act transitively on each side. Simulated annealing over S finds the largest feasible m."""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Cyclic Haar-graph search.
 *
 * Usage:  prog d D seed time_limit [m_lo]
 * Graph:  H(m, S): a_i = i, b_j = m + j; a_i ~ b_{(i+s) mod m} for s in S, |S| = d.
 * Output: "n m" plus edges for the largest feasible m >= m_lo found, or "0 0".
 *
 * Feasibility: every vertex within distance D of a_0 and of b_0. Translation by Z_m is an
 * automorphism, so this covers all pairs of vertices.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64
#define MAXM 4096

static int d, D;
static int M;
static int S[MAXD];
static int inS[MAXM];

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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Number of vertices within distance D of source (a_0 if srcB == 0, b_0 otherwise). */
static int reach_count(int srcB) {
    static int seen[2 * MAXM];
    static int cur[2 * MAXM], nxt[2 * MAXM];
    static int st = 0;
    st++;
    int src = srcB ? M : 0;
    int nc = 0, cnt = 1;
    seen[src] = st;
    cur[nc++] = src;
    for (int lev = 0; lev < D && nc > 0; lev++) {
        int nn = 0;
        for (int k = 0; k < nc; k++) {
            int v = cur[k];
            if (v < M) {
                for (int t = 0; t < d; t++) {
                    int u = M + (v + S[t]) % M;
                    if (seen[u] != st) { seen[u] = st; nxt[nn++] = u; }
                }
            } else {
                int j = v - M;
                for (int t = 0; t < d; t++) {
                    int u = (j - S[t] + M) % M;
                    if (seen[u] != st) { seen[u] = st; nxt[nn++] = u; }
                }
            }
        }
        cnt += nn;
        memcpy(cur, nxt, sizeof(int) * (size_t)nn);
        nc = nn;
    }
    return cnt;
}

static int cost_of(void) {
    return (2 * M - reach_count(0)) + (2 * M - reach_count(1));
}

/* Anneal S for the current M until cost 0 (success, copies S to outS) or deadline. */
static int anneal(double until, int *outS) {
    memset(inS, 0, sizeof(int) * (size_t)M);
    int k = 0;
    inS[0] = 1;
    S[k++] = 0;
    while (k < d) {
        int x = rndint(M);
        if (!inS[x]) { inS[x] = 1; S[k++] = x; }
    }
    int c = cost_of();
    double T = 2.0;
    long it = 0;
    while (c > 0) {
        if ((++it & 255) == 0 && now() > until) return 0;
        int t = 1 + rndint(d - 1);
        int x = rndint(M);
        if (inS[x]) continue;
        int old = S[t];
        inS[old] = 0;
        inS[x] = 1;
        S[t] = x;
        int nc = cost_of();
        if (nc <= c || rnd01() < exp((double)(c - nc) / T)) {
            c = nc;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[t] = old;
        }
        T *= 0.9995;
        if (T < 0.05) T = 2.0;
    }
    memcpy(outS, S, sizeof(int) * (size_t)d);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double lim = atof(argv[4]);
    int mlo = argc > 5 ? atoi(argv[5]) : d;
    double t0 = now();
    double t_end = t0 + lim * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long moore = moore_bound();
    int bestM = 0;
    int bestS[MAXD];
    if (d >= 2 && d <= MAXD && D >= 2) {
        if (mlo < d) mlo = d;
        for (int m = mlo; m < MAXM && 2L * m <= moore && now() < t_end; m++) {
            M = m;
            if (!anneal(t_end, bestS)) break;
            bestM = m;
        }
    }

    if (bestM > 0) {
        long edges = (long)bestM * d;
        printf("%d %ld\n", 2 * bestM, edges);
        for (int i = 0; i < bestM; i++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", i, bestM + (i + bestS[t]) % bestM);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice with load <= s on every target."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus new A-vertices (per SA point) and B-vertices (per SB line)."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E, list(range(2 * m, 2 * m + na)), list(range(2 * m + na, n))


def _fill_ab(n, edges, d, A, B):
    """Greedily add A-B edges while both endpoints have spare degree."""
    deg = [0] * n
    have = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        have.add((u, v) if u < v else (v, u))
    E = list(edges)
    for a in A:
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] >= d:
                continue
            key = (a, b) if a < b else (b, a)
            if key in have:
                continue
            have.add(key)
            deg[a] += 1
            deg[b] += 1
            E.append(key)
    return n, E


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, one per prime power q."""
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
        SA = _greedy_side(m, s, point_lines, rng, 30, deadline)
        SB = _greedy_side(m, s, line_points, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c, A, B = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append(_fill_ab(n_c, e_c, d, A, B))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only for D >= 4.
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
    """W(q) for the largest prime power q <= min(d - 1, 7)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.12 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Cyclic Haar search: look for H(m, S) with m above half the current best order.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    mlo = best[0] // 2 + 1
    if d >= 2 and D >= 2 and budget > 0.5 and 2 * mlo <= lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mlo],
                             timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass  # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
