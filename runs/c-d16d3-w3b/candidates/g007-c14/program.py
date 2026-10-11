import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D = 3: bi-Cayley (Haar-type) graphs from difference covers.
#
# Pick a finite group G of order N and a d-subset S of G. Join A_x to B_y
# iff y = x*s for some s in S. The graph is d-regular on 2N vertices, and it
# has diameter 3 whenever the three sets
#     S S^-1,   S^-1 S,   S S^-1 S
# all equal G. (For abelian G the last two follow from S - S = G.)
# A d-set with this property exists for N up to d^2 - d + 1 (the Moore bound
# /2), so the search can in principle reach order 2(d^2 - d + 1).
#
# The C engine runs simulated annealing on S: a move swaps one element of S
# for an outside element, and the cost is the number of uncovered group
# elements in the three sets above. The group is supplied as a full
# multiplication table and inverse table through the graph input channel.
#
# Fallbacks: K_{d,d} (diameter 2, always valid) and the arc-extended projective
# plane graphs (the previous best construction for D = 3).
# ----------------------------------------------------------------------------

C_DIFF = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXM 256
#define MAXD 32

static int m, d;
static int mul[MAXM][MAXM];
static int inv_[MAXM];
static uint64_t rs = 88172645463325252ULL;
static int S[MAXD];
static int inS[MAXM];

static uint64_t next64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) { return (int)(next64() % (uint64_t)n); }

static double rnd_unit(void) {
    return (double)(next64() >> 11) * (1.0 / 9007199254740992.0);
}

static int cover_cost(void) {
    static int c1[MAXM], c2[MAXM], c3[MAXM];
    static int P[MAXD * MAXD];
    int cnt1 = 0, cnt2 = 0, cnt3 = 0, np = 0;
    memset(c1, 0, sizeof(int) * (size_t)m);
    memset(c2, 0, sizeof(int) * (size_t)m);
    memset(c3, 0, sizeof(int) * (size_t)m);
    for (int i = 0; i < d; i++) {
        for (int j = 0; j < d; j++) {
            int a = S[i], b = S[j];
            int p = mul[a][inv_[b]];      /* S S^-1 */
            int q = mul[inv_[a]][b];      /* S^-1 S */
            P[np++] = p;
            if (!c1[p]) { c1[p] = 1; cnt1++; }
            if (!c2[q]) { c2[q] = 1; cnt2++; }
        }
    }
    for (int i = 0; i < np; i++) {
        for (int k = 0; k < d; k++) {
            int r = mul[P[i]][S[k]];      /* S S^-1 S */
            if (!c3[r]) { c3[r] = 1; cnt3++; }
        }
    }
    return (m - cnt1) + (m - cnt2) + (m - cnt3);
}

int main(int argc, char **argv) {
    if (argc < 4) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;

    int M = 0;
    if (scanf("%d %d", &m, &M) != 2 || m < 1 || m > MAXM || d < 1 || d > MAXD ||
        d > m || M != m * m + m) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m * m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= m || v < 0 || v >= m) {
            printf("0 0\n");
            return 0;
        }
        mul[i / m][i % m] = v;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= m || v < 0 || v >= m) {
            printf("0 0\n");
            return 0;
        }
        inv_[u] = v;
    }

    int perm[MAXM];
    for (int i = 0; i < m; i++) perm[i] = i;
    for (int i = m - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    for (int i = 0; i < d; i++) { S[i] = perm[i]; inS[perm[i]] = 1; }

    int cur = cover_cost();
    clock_t t0 = clock();
    long it = 0;
    double T = 1.0;
    while (cur > 0) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > budget) break;
            double cyc = budget / 3.0 + 1e-9;
            double ph = fmod(el / cyc, 1.0);
            T = 0.9 * (1.0 - ph) + 0.05;
        }
        it++;
        int i = rnd_int(d);
        int x = rnd_int(m);
        if (inS[x]) continue;
        int old = S[i];
        S[i] = x; inS[old] = 0; inS[x] = 1;
        int c2 = cover_cost();
        int delta = c2 - cur;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            S[i] = old; inS[x] = 0; inS[old] = 1;
        }
    }

    if (cur == 0) {
        printf("%d %d\n", m, d);
        for (int i = 0; i < d; i++) printf("%d 0\n", S[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""

PER_RUN = 2.0      # seconds of C annealing per (order, group) attempt
MAX_D_C = 32       # the C engine's MAXD


def _group_tables(N, rng):
    """Return a list of (label, mul table, inverse table) for groups of order N."""
    out = [("Z%d" % N,
            [[(a + b) % N for b in range(N)] for a in range(N)],
            [(-a) % N for a in range(N)])]
    for k in (2, 3, 4):
        if N % k or N // k < 3:
            continue
        m = N // k
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        r = rng.choice(rs)
        try:
            order, mulf, invf = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        if order != N:
            continue
        mul = [[mulf(a, b) for b in range(N)] for a in range(N)]
        inv = [invf(a) for a in range(N)]
        out.append((f"Z{m}x|Z{k}r{r}", mul, inv))
    return out


def _diff_run(N, mul, inv, d, seed, budget):
    """Run the C annealer; return the d-subset S of the group, or None."""
    edges = []
    for a in range(N):
        row = mul[a]
        for b in range(N):
            edges.append((a, row[b]))     # index a*N + b -> mul table entry
    for a in range(N):
        edges.append((a, inv[a]))         # index N*N + a -> inverse table entry
    try:
        out = lib.run_c(C_DIFF, [d, seed, round(budget, 2)],
                        stdin_graph=(N, edges), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 != N or len(e2) != d:
        return None
    S = [u for u, _ in e2]
    if len(set(S)) != d or any(not (0 <= s < N) for s in S):
        return None
    return S


def _diff_graph(N, mul, S):
    """Bi-Cayley graph: A_x = x, B_y = N + y, A_x ~ B_{x*s} for s in S."""
    edges = [(x, N + mul[x][s]) for x in range(N) for s in S]
    return 2 * N, edges


def _diff_cover_search(d, D, deadline, seed, best_n):
    """Search group orders N upward from best_n/2 + 1; return the largest valid graph found."""
    rng = random.Random(seed + 101)
    moore_half = lib.moore_bound(d, D) // 2
    N = max(d, best_n // 2 + 1)
    best = None
    fails = 0
    run_no = 0
    while N <= moore_half and fails < 4:
        if time.monotonic() > deadline - 1.0:
            break
        ok = False
        for _label, mul, inv in _group_tables(N, rng):
            remain = deadline - time.monotonic() - 0.5
            if remain < 0.3:
                break
            budget = min(PER_RUN, remain)
            S = _diff_run(N, mul, inv, d, seed * 1000 + run_no, budget)
            run_no += 1
            if S is None:
                continue
            n, e = _diff_graph(N, mul, S)
            if lib.is_valid(n, e, d, D):
                best = (n, e)
                ok = True
                break
        fails = 0 if ok else fails + 1
        N += 1
    return best


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), the previous
# best D = 3 construction, kept as a fallback.
# ----------------------------------------------------------------------------

_LS_ITERS = 20000


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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy for the load-constrained set problem."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates from arc-extended PG(2, q) for prime powers q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Driver.
#   D = 3: arc-extended PG graphs (up to 25% of time), then the difference-cover
#          search from just above the arc order (up to 85% of time).
#   D = 2 and other D: K_{d,d}, which has diameter 2 (not a target here).
# Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        arcs = _arc_extensions(d, start + 0.25 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs[:4]:
            consider(g)

        if d <= MAX_D_C:
            consider(_diff_cover_search(d, D, end, seed, best_n))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
