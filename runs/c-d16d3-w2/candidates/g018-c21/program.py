import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference-cover search in finite groups.
#
# A bipartite graph H(G, S) has vertices a_x and b_x (x in G), with a_x joined
# to b_{x s} for each s in S, |S| = d. If S S^{-1} = G, every two a-vertices
# share a neighbour, every a-b pair is at distance <= 3, and so diameter is 3.
# The order is 2|G|, and the Moore bound gives |G| <= d^2 - d + 1.
#
# Groups are Z_m x|_r Z_k with element (a, b) coded as a*k + b, the same
# convention as lib.semidirect_group. The engine runs simulated annealing on
# S, round-robin over candidate groups, and drops any group with order at most
# the best order found so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXG 512
#define MAXD 64
#define MAXN 1024

typedef struct {
    int m, k, r, N;
    int P[MAXN];
    int S[MAXD];
    int inS[MAXN];
    int cost;
    int bestc;
    int alive;
    int stall;
} Grp;

static Grp G[MAXG];
static int ng = 0;
static int d = 0;
static int solS[MAXD];
static int solG = -1;
static int bestN = 0;
static uint64_t rs = 88172645463325252ULL;
static unsigned char cov[MAXN];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 11);
}

static double rnd01(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k, b = x % g->k;
    int c = y / g->k, e = y % g->k;
    int A = (a + g->P[b] * c) % g->m;
    int B = (b + e) % g->k;
    return A * g->k + B;
}

static int ginv(const Grp *g, int x) {
    int a = x / g->k, b = x % g->k;
    int nb = (g->k - b) % g->k;
    int A = (g->P[nb] * a) % g->m;
    A = (g->m - A) % g->m;
    return A * g->k + nb;
}

/* Number of group elements NOT of the form s * t^{-1} with s, t in S. */
static int eval(const Grp *g, const int *S) {
    int N = g->N;
    int inv[MAXD];
    memset(cov, 0, (size_t)N);
    for (int j = 0; j < d; j++) inv[j] = ginv(g, S[j]);
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            cov[gmul(g, S[i], inv[j])] = 1;
    int unc = 0;
    for (int x = 0; x < N; x++)
        if (!cov[x]) unc++;
    return unc;
}

static void init_state(Grp *g) {
    memset(g->inS, 0, sizeof(int) * (size_t)g->N);
    for (int i = 0; i < d; i++) {
        int y;
        do {
            y = (int)(rnd() % (uint32_t)g->N);
        } while (g->inS[y]);
        g->S[i] = y;
        g->inS[y] = 1;
    }
    g->cost = eval(g, g->S);
    g->bestc = g->cost;
    g->stall = 0;
}

static int run_group(Grp *g, int iters) {
    const double T = 0.6;
    if (g->cost == 0) return 1;
    for (int it = 0; it < iters; it++) {
        int i = (int)(rnd() % (uint32_t)d);
        int y;
        do {
            y = (int)(rnd() % (uint32_t)g->N);
        } while (g->inS[y]);
        int old = g->S[i];
        g->S[i] = y;
        int c2 = eval(g, g->S);
        int delta = c2 - g->cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            g->inS[old] = 0;
            g->inS[y] = 1;
            g->cost = c2;
            if (c2 < g->bestc) {
                g->bestc = c2;
                g->stall = 0;
            } else {
                g->stall++;
            }
        } else {
            g->S[i] = old;
            g->stall++;
        }
        if (g->cost == 0) return 1;
        if (g->stall > 20000) {
            init_state(g);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("none\n"); return 0; }
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    int T = atoi(argv[4]);
    if (d < 2 || d > MAXD || T < 0 || argc < 5 + 3 * T) {
        printf("none\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd();

    ng = 0;
    for (int t = 0; t < T && ng < MAXG; t++) {
        int m = atoi(argv[5 + 3 * t]);
        int k = atoi(argv[6 + 3 * t]);
        int r = atoi(argv[7 + 3 * t]);
        if (m < 2 || k < 1) continue;
        long N = (long)m * k;
        if (N <= d || N > MAXN) continue;
        Grp *g = &G[ng];
        memset(g, 0, sizeof *g);
        g->m = m;
        g->k = k;
        g->r = r;
        g->N = (int)N;
        g->P[0] = 1 % m;
        for (int b = 1; b < k; b++) g->P[b] = (g->P[b - 1] * r) % m;
        g->alive = 1;
        init_state(g);
        ng++;
    }

    clock_t t0 = clock();
    for (;;) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el > budget) break;
        int active = 0;
        for (int gi = 0; gi < ng; gi++) {
            Grp *g = &G[gi];
            if (!g->alive) continue;
            if (g->N <= bestN) { g->alive = 0; continue; }
            active = 1;
            if (run_group(g, 3000)) {
                bestN = g->N;
                solG = gi;
                memcpy(solS, g->S, sizeof(int) * (size_t)d);
                g->alive = 0;
            }
            if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        }
        if (!active) break;
    }

    if (solG < 0) { printf("none\n"); return 0; }
    Grp *g = &G[solG];
    printf("found %d %d %d", g->m, g->k, g->r);
    for (int i = 0; i < d; i++) printf(" %d", solS[i]);
    printf("\n");
    return 0;
}
"""


def _group_params(N, rng):
    """Candidate groups of order N as (m, k, r): cyclic, Z_m x Z_k, and one random semidirect product."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        out.append((m, k, 1))
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if cands:
            out.append((m, k, rng.choice(cands)))
    return out


def _group_search(d, Nmax, lowN, seed, budget, timeout):
    """Run the C difference-cover search; return (n, edges) of the best Haar-type graph found, or None."""
    if budget < 1.0:
        return None
    rng = random.Random(seed)
    flat = []
    count = 0
    for N in range(Nmax, lowN - 1, -1):
        for m, k, r in _group_params(N, rng):
            flat += [m, k, r]
            count += 1
    if count == 0:
        return None
    args = [d, seed & 0xFFFFFFFF, round(budget, 2), count] + flat
    try:
        out = lib.run_c(C_SOURCE, args, timeout=timeout)
    except Exception:
        return None
    toks = out.split()
    if len(toks) < 4 + d or toks[0] != "found":
        return None
    m, k, r = int(toks[1]), int(toks[2]), int(toks[3])
    S = [int(x) for x in toks[4:4 + d]]
    try:
        N, mul, _ = _semidirect(m, k, r)
    except ValueError:
        return None
    edges = [(x, N + mul(x, s)) for x in range(N) for s in S]
    return 2 * N, edges


def _semidirect(m, k, r):
    """Thin wrapper so the group construction is isolated; returns (order, mul, inv)."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    return order, mul, inv


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), kept as a
# secondary candidate.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
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

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) baseline (D >= 4).
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D == 3:
        # Arc-extended PG graphs as a secondary candidate.
        arcs = _arc_extensions(d, start + 0.10 * time_limit,
                               random.Random(seed * 7919 + d))
        for g in sorted(arcs, key=lambda t: -t[0]):
            consider(g)

        # Main attempt: difference-cover Haar graphs with order above the record.
        Nmax = d * d - d + 1          # Moore bound for D = 3 is 2 * Nmax
        lowN = max(d + 1, Nmax - 45)
        deadline_total = start + 0.85 * time_limit
        budget = deadline_total - time.monotonic() - 2.0
        timeout = max(2.0, 0.95 * time_limit - (time.monotonic() - start))
        consider(_group_search(d, Nmax, lowN, seed, budget, timeout))
        return best

    # D >= 4: generalized quadrangle baseline when it applies.
    consider(_best_gq(d))
    return best
