import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference-cover search for Haar graphs.
#
# A Haar graph H(Z_m, S) has parts a_i and b_j, with a_i ~ b_{i+s} for s in S.
# If |S| = d and S - S covers all of Z_m, then the graph is bipartite, d-regular,
# and has diameter at most 3. The same-side pairs are at distance 2, and the
# opposite-side pairs are at distance at most 3, because S - S + S = Z_m.
# So the problem is to find a d-subset of Z_m whose difference set covers Z_m,
# for the largest possible m. The order is 2m.
#
# Method: for m = m0, m0+1, ..., run simulated annealing on the number of
# uncovered nonzero differences. Each accepted cover gives a graph of order 2m.
# ----------------------------------------------------------------------------

DIFF_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 1024

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int K, M;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int unc;

/* Add (sg=+1) or remove (sg=-1) the unordered pair {a,b} from the difference counts. */
static void bump(int a, int b, int sg) {
    int x = (a - b + M) % M;
    int y = (M - x) % M;
    int c[2] = {x, y};
    for (int t = 0; t < 2; t++) {
        int z = c[t];
        if (sg < 0) {
            cnt[z]--;
            if (cnt[z] == 0) unc++;
        } else {
            if (cnt[z] == 0) unc--;
            cnt[z]++;
        }
    }
}

/* Replace S[i] by nv, updating counts. */
static void change(int i, int nv) {
    int old = S[i];
    for (int j = 0; j < K; j++) if (j != i) bump(old, S[j], -1);
    inS[old] = 0;
    for (int j = 0; j < K; j++) if (j != i) bump(nv, S[j], +1);
    inS[nv] = 1;
    S[i] = nv;
}

static int search(double tend) {
    memset(cnt, 0, sizeof(int) * M);
    memset(inS, 0, sizeof(int) * M);
    unc = M - 1;
    for (int i = 0; i < K; i++) {
        int v;
        do { v = rndi(M); } while (inS[v]);
        S[i] = v;
        inS[v] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) bump(S[i], S[j], +1);
    if (unc == 0) return 1;

    long it = 0;
    const long L = 200000;
    while (1) {
        if ((it & 1023) == 0 && now_s() > tend) return 0;
        it++;
        double phase = (double)(it % L) / (double)L;
        double T = 0.12 + 1.0 * (1.0 - phase);
        int i = rndi(K);
        int nv;
        if (rndu() < 0.4) {
            nv = rndi(M);
        } else {
            int r = rndi(M - 1);
            int x = 0;
            for (int t = 0; t < M - 1; t++) {
                int z = 1 + (r + t) % (M - 1);
                if (cnt[z] == 0) { x = z; break; }
            }
            if (x == 0) continue;
            int s = S[rndi(K)];
            nv = (rndu() < 0.5) ? (s + x) % M : (s - x + M) % M;
        }
        if (inS[nv]) continue;
        int old = S[i];
        int before = unc;
        change(i, nv);
        int delta = unc - before;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            if (unc == 0) return 1;
        } else {
            change(i, old);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (D < 3 || d < 2 || d > MAXK) { printf("0 0\n"); return 0; }
    K = d;

    int m = d * d / 2;
    if (m < d + 1) m = d + 1;
    int bestM = 0;
    int bestS[MAXK];
    int fails = 0;
    double t0 = now_s();
    while (m < MAXM - 1 && m <= K * (K - 1) + 1) {
        double rem = budget - (now_s() - t0);
        if (rem < 0.2) break;
        double slice = budget * 0.12;
        if (slice < 0.3) slice = 0.3;
        if (slice > rem) slice = rem;
        M = m;
        if (search(now_s() + slice)) {
            bestM = m;
            memcpy(bestS, S, sizeof(int) * K);
            fails = 0;
        } else {
            fails++;
            if (fails >= 3) break;
        }
        m++;
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    M = bestM;
    printf("%d %d\n", 2 * M, M * K);
    for (int i = 0; i < M; i++)
        for (int j = 0; j < K; j++)
            printf("%d %d\n", i, M + (i + bestS[j]) % M);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane based starting graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(min(d - 1, 40), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """True if every target is hit at most s times by S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy set so that every target is hit at most s times."""
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
    """Conic (plus nucleus when q is even) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
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
    """Candidate graphs from PG(2, q) with arc-extension vertices, q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
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
# Difference-cover Haar graph search (C).
# ----------------------------------------------------------------------------

def _diff_cover_graph(d, seed, budget):
    """Run the C difference-cover search; return (n, edges) or None."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(DIFF_SOURCE, [d, 3, seed, round(budget, 2)],
                        stdin_graph=None, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 2 or not e:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Driver.
#   D <= 2 : K_{d,d} (diameter 2), or a single edge when D == 1.
#   D >= 3 : the best of PG-based starts and the Haar difference-cover graph.
#            A Haar graph H(Z_m, S) with S - S = Z_m has diameter <= 3, so it is
#            valid for every D >= 3. Every candidate is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def elapsed():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        try:
            for g in _arc_extensions(d, start + 0.05 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        except Exception:
            pass

        budget = 0.8 * time_limit - elapsed() - 1.5
        if budget >= 0.5:
            consider(_diff_cover_graph(d, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
