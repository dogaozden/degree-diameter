"""Difference-cover Haar graphs for diameter 3, with arc-extended projective planes as the fallback.

Bold change: for D = 3 the main search is no longer lift-based. A Haar graph of a finite abelian
group G with connection set S (|S| = d) has vertices a_x, b_y (x, y in G) and edges a_x b_{x+s}
for s in S. It is bipartite and d-regular. It has diameter 3 exactly when S - S = G, because
same-side pairs are joined by a path of length 2 and opposite-side pairs by a path of length 3.
The C engine anneals over G = Z_a x Z_b for each candidate order m, minimising the number of
uncovered differences, and returns the largest order it solves. The arc-extended projective plane
graph (order 2(q^2+q+5)-style, 394 for d = 16) stays as the fallback, and every result is checked
with lib.is_valid. For D >= 4 this version uses the W(q) construction and K_{d,d} fallbacks only;
the earlier C growth engine has been removed.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Difference-cover search over G = Z_A x Z_B (order M = A*B), set size K.
 * Finds S with 0 in S, |S| = K, S - S = G (every nonzero element is a difference).
 * Usage:  prog K seed time_limit m_lo m_hi
 * Output: "A B K s_1 ... s_K" (elements encoded as i*B + j) or "0".
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64
#define ITERS 400000L

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int A, B, M, K;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int uncov;

static int gsub(int x, int y) {
    int i = x / B - y / B;
    if (i < 0) i += A;
    int j = x % B - y % B;
    if (j < 0) j += B;
    return i * B + j;
}

static int gadd(int x, int y) {
    int i = x / B + y / B;
    if (i >= A) i -= A;
    int j = x % B + y % B;
    if (j >= B) j -= B;
    return i * B + j;
}

static void inc(int x) { if (cnt[x]++ == 0) uncov--; }
static void dec(int x) { if (--cnt[x] == 0) uncov++; }

static void remove_elem(int idx) {
    int s = S[idx];
    for (int t = 0; t < K; t++)
        if (t != idx) { dec(gsub(s, S[t])); dec(gsub(S[t], s)); }
    inS[s] = 0;
}

static void insert_elem(int idx, int y) {
    S[idx] = y;
    inS[y] = 1;
    for (int t = 0; t < K; t++)
        if (t != idx) { inc(gsub(y, S[t])); inc(gsub(S[t], y)); }
}

/* Propose a replacement for S[idx] (idx >= 1). Half the moves target an uncovered difference. */
static int propose(int *idx, int *y) {
    if (rndint(100) < 60) {
        int x = -1;
        for (int tr = 0; tr < 200; tr++) {
            int c = 1 + rndint(M - 1);
            if (cnt[c] == 0) { x = c; break; }
        }
        if (x < 0) x = 1 + rndint(M - 1);
        int t = S[rndint(K)];
        *y = gadd(t, x);
    } else {
        *y = rndint(M);
    }
    if (inS[*y]) return 0;
    *idx = 1 + rndint(K - 1);
    return 1;
}

static int search_group(int a, int b, double until, int *out) {
    A = a; B = b; M = a * b;
    while (now() < until) {
        memset(inS, 0, sizeof(int) * (size_t)M);
        S[0] = 0; inS[0] = 1;
        for (int i = 1; i < K; i++) {
            int y;
            do { y = rndint(M); } while (inS[y]);
            S[i] = y;
            inS[y] = 1;
        }
        memset(cnt, 0, sizeof(int) * (size_t)M);
        uncov = M - 1;
        for (int i = 0; i < K; i++)
            for (int j = i + 1; j < K; j++) {
                inc(gsub(S[i], S[j]));
                inc(gsub(S[j], S[i]));
            }
        for (long it = 0; it < ITERS && uncov > 0; it++) {
            if ((it & 1023) == 0 && now() > until) break;
            double T = pow(0.05, (double)it / (double)ITERS);
            int idx, y;
            if (!propose(&idx, &y)) continue;
            int old = S[idx];
            int before = uncov;
            remove_elem(idx);
            insert_elem(idx, y);
            int delta = uncov - before;
            if (delta > 0 && rnd01() >= exp(-(double)delta / T)) {
                remove_elem(idx);
                insert_elem(idx, old);
            }
        }
        if (uncov == 0) {
            for (int i = 0; i < K; i++) out[i] = S[i];
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0\n"); return 0; }
    K = atoi(argv[1]);
    long seed = atol(argv[2]);
    double limit = atof(argv[3]);
    int mlo = atoi(argv[4]), mhi = atoi(argv[5]);
    if (mhi > MAXM - 1) mhi = MAXM - 1;
    if (K < 2 || K > MAXK) { printf("0\n"); return 0; }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double deadline = now() + limit;
    int bestA = 0, bestB = 0, bestM = 0;
    int bestS[MAXK];
    for (int m = mlo; m <= mhi; m++) {
        if (m < K) continue;
        double left = deadline - now();
        if (left <= 0) break;
        int remaining = mhi - m + 1;
        double slice = left / remaining;
        int fa[64], nf = 0;
        for (int a = 1; a * a <= m && nf < 64; a++)
            if (m % a == 0) fa[nf++] = a;
        double ts = slice / nf;
        int found = 0;
        for (int f = 0; f < nf && !found; f++) {
            int a = fa[f], b = m / a;
            int Sout[MAXK];
            if (search_group(a, b, now() + ts, Sout)) {
                found = 1;
                bestM = m; bestA = a; bestB = b;
                memcpy(bestS, Sout, sizeof(int) * (size_t)K);
            }
        }
    }
    if (bestM == 0) { printf("0\n"); return 0; }
    printf("%d %d %d", bestA, bestB, K);
    for (int i = 0; i < K; i++) printf(" %d", bestS[i]);
    printf("\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3). Fallback construction.
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
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
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
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
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
    """W(q) for the largest prime power q <= min(d - 1, 7), for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


# ----------------------------------------------------------------------------
# Difference-cover Haar graphs (diameter 3).
# ----------------------------------------------------------------------------

def _haar_candidate(d, m_lo, m_hi, seed, budget):
    """Run the C difference-cover search and build the Haar graph it finds, or return None."""
    text = lib.run_c(C_SOURCE, [d, seed, round(budget, 2), m_lo, m_hi],
                     timeout=budget + 10)
    toks = text.split()
    if len(toks) < 3:
        return None
    a, b, k = int(toks[0]), int(toks[1]), int(toks[2])
    if k != d or len(toks) < 3 + k:
        return None
    S = [int(t) for t in toks[3:3 + k]]
    m = a * b
    edges = []
    for s in S:
        si, sj = divmod(s, b)
        for x in range(m):
            xi, xj = divmod(x, b)
            y = ((xi + si) % a) * b + (xj + sj) % b
            edges.append((x, m + y))
    return 2 * m, edges


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

    if D == 3 and d >= 2:
        # Improve only beyond the current order: m must exceed best order / 2.
        m_lo = max(best[0] // 2 + 1, d)
        m_hi = min(d * d - d + 1, 1023)
        budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
        if m_lo <= m_hi and budget > 0.5:
            try:
                consider(_haar_candidate(d, m_lo, m_hi, seed, budget))
            except (RuntimeError, ValueError):
                pass   # keep the best construction so far

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
