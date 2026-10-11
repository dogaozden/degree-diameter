"""Arc-set extension of projective planes (diameter 3).

Start from PG(2, q) incidence, with m = q^2+q+1 points and m lines. For d - q - 1 = s spare
degrees, add a new A-vertex per chosen point P, joined to the q+1 lines through P, and a new
B-vertex per chosen line L, joined to the q+1 points on L. A line may carry at most s A-neighbours
and a point at most s B-neighbours, so SA and SB must be (k, s)-sets: every line (point) meets SA (SB)
in at most s elements. Any such choice keeps diameter 3, so validity holds by construction.

This replaces the parent's conic-based sets with sets found by simulated annealing in C. For
d = 16 (q = 13, s = 2), a conic gives 14 per side (order 394). An annealed (k, 2)-set can reach
about 18 or more per side, which would give order above 394.

Cases without a closed form and not handled here fall back to the Python constructions only.
Every returned graph is checked with lib.is_valid, and a Haar graph is the last resort.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Annealed (k, s)-set search for arc-extended projective planes (D = 3).
 *
 * Usage:  prog d D seed time_limit   < PG incidence graph
 * stdin:  "n m" then m lines "u v"; points are 0..m-1, lines m..2m-1, n = 2m, m = q^2+q+1,
 *         every vertex has degree K = q+1. Otherwise the input is echoed back unchanged.
 * stdout: "n m" then m lines "u v" for the extended graph (or the input if no gain).
 *
 * Construction: SA is a set of points, SB a set of lines. Each line may meet SA in at most
 * s points and each point may meet SB in at most s lines, where s = d - K. New A-vertices
 * (side 0) attach to the lines through each point of SA. New B-vertices (side 1) attach to
 * the points on each line of SB. The sides are independent. Diameter stays 3.
 *
 * Search per side: a set of fixed size is annealed with swap moves, minimizing the total
 * excess V = sum_t max(0, load_t - s). When V reaches 0 the size grows by one.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXK 40
#define MAXE 41000
#define STALL 300000L

static int d, D, K, s, m;
static int ptl[MAXM][MAXK];   /* point -> its lines (0..m-1) */
static int lpt[MAXM][MAXK];   /* line  -> its points (0..m-1) */
static int ptc[MAXM], lnc[MAXM];
static int load[MAXM], in_set[MAXM], pos_of[MAXM], members[MAXM], nmem, V;
static int eu[MAXE], ev[MAXE];
static int deg[2 * MAXM];
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

static void st_reset(void) {
    memset(load, 0, sizeof load);
    memset(in_set, 0, sizeof in_set);
    for (int i = 0; i < MAXM; i++) pos_of[i] = -1;
    nmem = 0;
    V = 0;
}

static void st_add(int (*tg)[MAXK], int e) {
    for (int i = 0; i < K; i++) {
        int t = tg[e][i];
        if (load[t] >= s) V++;
        load[t]++;
    }
    in_set[e] = 1;
    pos_of[e] = nmem;
    members[nmem++] = e;
}

static void st_remove(int (*tg)[MAXK], int e) {
    for (int i = 0; i < K; i++) {
        int t = tg[e][i];
        if (load[t] > s) V--;
        load[t]--;
    }
    in_set[e] = 0;
    int p = pos_of[e];
    int last = members[--nmem];
    members[p] = last;
    pos_of[last] = p;
    pos_of[e] = -1;
}

/* Returns the size of the largest feasible set found; writes it to out. */
static int search_side(int (*tg)[MAXK], int *out, double until) {
    static int order[MAXM];
    st_reset();
    for (int i = 0; i < m; i++) order[i] = i;
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1), t = order[i];
        order[i] = order[j];
        order[j] = t;
    }
    for (int i = 0; i < m; i++) {
        int e = order[i], ok = 1;
        for (int k = 0; k < K; k++)
            if (load[tg[e][k]] >= s) { ok = 0; break; }
        if (ok) st_add(tg, e);
    }
    int best = nmem;
    memcpy(out, members, sizeof(int) * (size_t)nmem);

    double T = 0.6;
    long it = 0, last_ok = 0;
    for (;;) {
        it++;
        if ((it & 1023) == 0 && now() > until) break;

        if (V == 0) {
            last_ok = it;
            if (nmem > best) {
                best = nmem;
                memcpy(out, members, sizeof(int) * (size_t)nmem);
            }
            /* Grow: add the outside element with the fewest violations among random samples. */
            int be = -1, bv = 1 << 30;
            for (int c = 0; c < 64; c++) {
                int e = rndint(m);
                if (in_set[e]) continue;
                int inc = 0;
                for (int k = 0; k < K; k++)
                    if (load[tg[e][k]] >= s) inc++;
                if (inc < bv) { bv = inc; be = e; }
            }
            if (be >= 0) st_add(tg, be);
            T = 0.6;
            continue;
        }

        if (it - last_ok > STALL) {   /* stuck above feasibility: restart from best set */
            st_reset();
            for (int i = 0; i < best; i++) st_add(tg, out[i]);
            last_ok = it;
            T = 0.6;
            continue;
        }

        /* Swap move: remove a member, add a non-member. */
        int x = members[rndint(nmem)];
        int y;
        do { y = rndint(m); } while (in_set[y]);
        int V0 = V;
        st_remove(tg, x);
        st_add(tg, y);
        int dv = V - V0;
        if (!(dv <= 0 || rnd01() < exp(-(double)dv / T))) {
            st_remove(tg, y);
            st_add(tg, x);
        }
        T *= 0.99998;
        if (T < 0.05) T = 0.6;
    }
    return best;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double t_end = t0 + limit * 0.9 - 0.5;
    if (t_end < t0 + 0.2) t_end = t0 + 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n, me;
    if (scanf("%d %d", &n, &me) != 2 || n <= 0 || me < 0 || me > MAXE) return 1;
    for (int i = 0; i < me; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 1;

    int ok = (n % 2 == 0) && (n / 2 <= MAXM);
    if (ok) {
        m = n / 2;
        for (int i = 0; i < me && ok; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || v < 0 || u >= n || v >= n) ok = 0;
            else if (!((u < m && v >= m) || (v < m && u >= m))) ok = 0;
            else { deg[u]++; deg[v]++; }
        }
    }
    if (ok) {
        K = deg[0];
        for (int v = 0; v < n; v++) if (deg[v] != K) { ok = 0; break; }
        if (K < 2 || K > MAXK) ok = 0;
    }
    if (ok) {
        int q = K - 1;
        if (m != q * q + q + 1) ok = 0;
    }
    if (ok) {
        s = d - K;
        if (s < 1 || D != 3) ok = 0;
    }
    if (ok) {
        for (int i = 0; i < me && ok; i++) {
            int p = eu[i] < m ? eu[i] : ev[i];
            int l = (eu[i] < m ? ev[i] : eu[i]) - m;
            if (ptc[p] >= K || lnc[l] >= K) ok = 0;
            else {
                ptl[p][ptc[p]++] = l;
                lpt[l][lnc[l]++] = p;
            }
        }
    }
    if (!ok) {
        printf("%d %d\n", n, me);
        for (int i = 0; i < me; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    static int SA[MAXM], SB[MAXM];
    double mid = t0 + (t_end - t0) * 0.5;
    int na = search_side(ptl, SA, mid);
    int nb = search_side(lpt, SB, t_end);

    int N = 2 * m + na + nb;
    long M = (long)(m + na + nb) * K;
    printf("%d %ld\n", N, M);
    for (int u = 0; u < m; u++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", u, m + ptl[u][k]);
    for (int i = 0; i < na; i++) {
        int x = 2 * m + i, P = SA[i];
        for (int k = 0; k < K; k++)
            printf("%d %d\n", x, m + ptl[P][k]);
    }
    for (int j = 0; j < nb; j++) {
        int y = 2 * m + na + j, L = SB[j];
        for (int k = 0; k < K; k++)
            printf("%d %d\n", lpt[L][k], y);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions: the closed forms and cheap arc candidates used as fallbacks.
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
    """Randomized greedy (k, s)-set."""
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
    """Greedily add A-B edges while both endpoints have spare degree (only shortens distances)."""
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
    """(n, edges) candidates from conic / greedy arc extensions, one per prime power q."""
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
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _arc_q(d):
    """Prime power q whose arc extension has the largest counting bound, or None."""
    best = None
    for q in range(2, min(d - 2, 31) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        mm = q * q + q + 1
        bound = 2 * mm + 2 * (s * mm // (q + 1))
        if best is None or bound > best[0]:
            best = (bound, q)
    return best[1] if best else None


def _arc_q_bound(d, q):
    s = d - q - 1
    mm = q * q + q + 1
    return 2 * mm + 2 * (s * mm // (q + 1))


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

    if D == 3 and best[0] < lib.moore_bound(d, D):
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.1 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Main bold path: annealed arc-set extension of PG(2, q) in C.
    if D == 3 and best[0] < lib.moore_bound(d, D):
        q = _arc_q(d)
        if q is not None and _arc_q_bound(d, q) > best[0]:
            budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
            if budget > 2.0:
                try:
                    n0, e0 = lib.projective_plane_incidence(q)
                    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                     stdin_graph=(n0, e0), timeout=budget + 4)
                    n, e = lib.parse_graph_text(text)
                    consider((n, e))
                except (RuntimeError, ValueError):
                    pass   # keep the Python construction

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
