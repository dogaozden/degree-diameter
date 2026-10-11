import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing for difference covers in an arbitrary finite
# group G (given by its full multiplication table, identity = 0).
#
# A k-subset S of G gives the bipartite Haar-type graph H(G, S): a_g ~ b_h iff
# g^{-1} h in S. It is k-regular on 2|G| vertices. A-A distance is at most 2
# iff S^{-1} S covers G \ {e}. Then S^{-1} S S = G, so B-A and A-B pairs are at
# distance at most 3 as well, and the diameter is 3. The C program minimises the
# number of uncovered nonzero group elements with incremental counts.
# Input: "G G*G" then G*G pairs "idx value" giving mt[idx] = value.
# Args: k budget_seconds seed. Output: the graph, or "0 0" when no cover is found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int G, K, zeros;
static int *mt, *iv, *cnt, *inS, *S;
static uint64_t rs = 88172645463325252ULL;

static uint64_t next64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(next64() % (uint64_t)n); }
static double rnd01(void) { return (double)(next64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static void inc(int x) { if (cnt[x]++ == 0 && x != 0) zeros--; }
static void dec(int x) { if (--cnt[x] == 0 && x != 0) zeros++; }

/* Replace S[i] by nw, updating the ordered-pair counts and the zero count. */
static void edit(int i, int nw) {
    int old = S[i];
    for (int j = 0; j < K; j++) if (j != i) {
        int t = S[j];
        dec(mt[iv[old] * G + t]);
        dec(mt[iv[t] * G + old]);
    }
    S[i] = nw; inS[old] = 0; inS[nw] = 1;
    for (int j = 0; j < K; j++) if (j != i) {
        int t = S[j];
        inc(mt[iv[nw] * G + t]);
        inc(mt[iv[t] * G + nw]);
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    double budget = atof(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 3 || m != n * n) { printf("0 0\n"); return 0; }
    G = n;
    if (K < 2 || K > G - 1 || (long long)K * (K - 1) + 1 < (long long)G) { printf("0 0\n"); return 0; }

    mt = calloc((size_t)G * G, sizeof(int));
    iv = calloc((size_t)G, sizeof(int));
    cnt = calloc((size_t)G, sizeof(int));
    inS = calloc((size_t)G, sizeof(int));
    S = calloc((size_t)K, sizeof(int));
    if (!mt || !iv || !cnt || !inS || !S) return 1;

    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 1;
        if (u < 0 || u >= G * G || v < 0 || v >= G) return 1;
        mt[u] = v;
    }
    for (int x = 0; x < G; x++) {
        iv[x] = -1;
        for (int y = 0; y < G; y++) if (mt[x * G + y] == 0) { iv[x] = y; break; }
        if (iv[x] < 0) { printf("0 0\n"); return 0; }
    }

    clock_t t0 = clock();
    const double T = 0.45;
    const long long restart_every = 4000000LL;
    long long iter = 0;
    int found = 0, timeup = 0;

    while (!found && !timeup) {
        memset(cnt, 0, sizeof(int) * (size_t)G);
        memset(inS, 0, sizeof(int) * (size_t)G);
        zeros = G - 1;
        for (int i = 0; i < K; i++) {
            int y;
            do { y = 1 + rndint(G - 1); } while (inS[y]);
            S[i] = y;
            inS[y] = 1;
        }
        for (int i = 0; i < K; i++)
            for (int j = 0; j < K; j++)
                if (i != j) inc(mt[iv[S[i]] * G + S[j]]);

        long long since = 0;
        while (zeros > 0 && since < restart_every) {
            iter++; since++;
            if ((iter & 4095) == 0 && elapsed(t0) > budget) { timeup = 1; break; }
            int i = rndint(K);
            int y = 1 + rndint(G - 1);
            if (inS[y]) continue;
            int old = S[i];
            int z0 = zeros;
            edit(i, y);
            int dz = zeros - z0;
            if (dz > 0 && rnd01() >= exp(-dz / T)) edit(i, old);
        }
        if (zeros == 0) found = 1;
    }

    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * G, G * K);
    for (int g = 0; g < G; g++)
        for (int i = 0; i < K; i++)
            printf("%d %d\n", g, G + mt[g * G + S[i]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line holding at most s points of S and every point lying on at
# most s lines indexed by S. Add a new A-vertex per P in S (joined to the lines
# through P) and a new B-vertex per j in S (joined to the points on line j).
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
# Group difference-cover Haar graphs, searched by the C engine.
#
# Groups of order m are semidirect products Z_a x| Z_b (the cyclic group is
# (m, 1, 1)). Each candidate group is passed as a full multiplication table.
# A cover of size d found in a group of order m yields a d-regular bipartite
# graph on 2m vertices with diameter 3. The Moore-type limit is m <= d(d-1)+1.
# ----------------------------------------------------------------------------

def _group_specs(m, rng, extra=3):
    """Return (a, b, r) triples for semidirect products Z_a x| Z_b of order m; the first is cyclic."""
    specs = [(m, 1, 1)]
    divs = [b for b in range(2, m) if m % b == 0 and m // b >= 2]
    rng.shuffle(divs)
    for b in divs:
        if len(specs) > extra:
            break
        a = m // b
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
        if rs:
            specs.append((a, b, rng.choice(rs)))
    return specs


def _find_cover(spec, k, seed, budget):
    """Run the C annealer on the group given by spec; return (n, edges) of the Haar graph, or None."""
    a, b, r = spec
    order, mul, _ = lib.semidirect_group(a, b, r)
    # Table encoding: header "order order*order", then pairs (x*order+y, x*y).
    edges = [(x * order + y, mul(x, y)) for x in range(order) for y in range(order)]
    out = lib.run_c(C_SOURCE, [k, f"{budget:.3f}", seed],
                    stdin_graph=(order, edges), timeout=budget + 5.0)
    n, E = lib.parse_graph_text(out)
    if n == 0 or not E:
        return None
    return n, E


def _cover_phase(d, seed, n_best, deadline, consider):
    """Search upward in group order m for covers giving graphs bigger than n_best."""
    k = d
    cap = k * (k - 1) + 1
    m = max(n_best // 2 + 1, k + 1)
    rng = random.Random(seed * 104729 + d)
    while m <= cap:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            return
        ok = False
        for spec in _group_specs(m, rng):
            remaining = deadline - time.monotonic()
            if remaining < 0.8:
                return
            budget = min(remaining - 0.3, max(0.5, 0.35 * remaining))
            res = _find_cover(spec, k, seed + 31 * m, budget)
            if res is not None:
                consider(res[0], res[1])
                ok = True
                break
        if not ok:
            return
        m += 1


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2 or d < 2:
        return best

    # Projective-plane based candidates (fast).
    arcs = _arc_extensions(d, start + 0.12 * time_limit, random.Random(seed * 7919 + d))
    arcs.sort(key=lambda t: -t[0])
    for n_c, e_c in arcs[:3]:
        consider(n_c, e_c)

    # Main search: C annealing for difference covers in groups of growing order.
    # Haar graphs have diameter 3, which is within D for every D >= 3.
    try:
        _cover_phase(d, seed, best[0], deadline, consider)
    except RuntimeError:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
