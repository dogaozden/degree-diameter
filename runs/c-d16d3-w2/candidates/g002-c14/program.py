import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line holds at most s points of S and every point lies on at
# most s lines indexed by S. Add a new A-vertex joined to the q+1 lines through
# each P in S, and a new B-vertex joined to the q+1 points on each line j in S.
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
# NEW (D = 3): non-abelian bi-Cayley (Haar-type) graphs over metacyclic groups.
#
# Let G be a finite group, S a k-subset of G, and let the graph have vertices
# a_g, b_g (g in G) with a_g ~ b_{g s} for s in S. It is k-regular on 2|G|
# vertices and left multiplication is an automorphism. Then:
#   * A-A distance <= 2 for all pairs  <=>  S S^{-1} = G,
#   * B-B distance <= 2 for all pairs  <=>  S^{-1} S = G,
#   * A-B distance <= 3 follows from S S^{-1} = G.
# So the diameter is 3 exactly when both covering conditions hold. For abelian
# groups these coincide (classical difference covers). Non-abelian groups give
# a second family, and the search for them runs in the C engine below.
# Groups tried: Z_M x| Z_K with r^K = 1 mod M, gcd(r, M) = 1 (order M*K).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXGROUPS 16384
#define ITERS 20000

static int GORD, KS;
static int mt[MAXG][MAXG];
static int invt[MAXG];
static int cntA[MAXG], cntB[MAXG];
static int S[MAXG];
static int pwv[MAXG];
static int GLM[MAXGROUPS], GLK[MAXGROUPS], GLR[MAXGROUPS];
static int ordv[MAXGROUPS];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long gcd_l(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Element (a,b) of Z_M x| Z_K is coded a*K+b; (a,b)(c,d) = (a + r^b c, b + d). */
static void build_group(int M, int K, int r) {
    GORD = M * K;
    pwv[0] = 1 % M;
    for (int b = 1; b < K; b++) pwv[b] = (int)((long)pwv[b - 1] * r % M);
    for (int x = 0; x < GORD; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < GORD; y++) {
            int c = y / K, dd = y % K;
            mt[x][y] = (int)(((long)a + (long)pwv[b] * c) % M) * K + (b + dd) % K;
        }
    }
    for (int x = 0; x < GORD; x++)
        for (int y = 0; y < GORD; y++)
            if (mt[x][y] == 0) invt[x] = y;
}

static int list_groups(int ord) {
    int n = 0;
    for (int K = 1; K <= ord; K++) {
        if (ord % K) continue;
        int M = ord / K;
        if (K == 1 || M == 1) {
            if (n < MAXGROUPS) { GLM[n] = M; GLK[n] = K; GLR[n] = 0; n++; }
            continue;
        }
        for (int r = 1; r < M; r++) {
            if (gcd_l(r, M) != 1) continue;
            if (powmod_l(r, K, M) != 1 % M) continue;
            if (n < MAXGROUPS) { GLM[n] = M; GLK[n] = K; GLR[n] = r; n++; }
        }
    }
    return n;
}

static int inS_upto(int y, int cnt) {
    for (int q = 0; q < cnt; q++) if (S[q] == y) return 1;
    return 0;
}

/* cntA[x] = #ordered pairs (i,j), i != j, with S_i S_j^{-1} = x; cntB[x] likewise for S_i^{-1} S_j. */
static void init_counts(void) {
    memset(cntA, 0, sizeof cntA);
    memset(cntB, 0, sizeof cntB);
    for (int i = 0; i < KS; i++)
        for (int j = 0; j < KS; j++) {
            if (i == j) continue;
            cntA[mt[S[i]][invt[S[j]]]]++;
            cntB[mt[invt[S[i]]][S[j]]]++;
        }
}

/* Add (sgn=+1) or remove (sgn=-1) the pairs between element x and every S[j], j != skip. */
static void touch(int skip, int x, int sgn) {
    int xi = invt[x];
    for (int j = 0; j < KS; j++) {
        if (j == skip) continue;
        int t = S[j], ti = invt[t];
        cntA[mt[x][ti]] += sgn;
        cntA[mt[t][xi]] += sgn;
        cntB[mt[xi][t]] += sgn;
        cntB[mt[ti][x]] += sgn;
    }
}

static int uncovered(void) {
    int c = 0;
    for (int x = 1; x < GORD; x++) {
        if (cntA[x] == 0) c++;
        if (cntB[x] == 0) c++;
    }
    return c;
}

static int anneal(int iters, double T0, double T1) {
    for (int j = 0; j < KS;) {
        int y = rndint(GORD);
        if (!inS_upto(y, j)) S[j++] = y;
    }
    init_counts();
    int cur = uncovered();
    for (int it = 0; it < iters && cur > 0; it++) {
        double T = T0 + (T1 - T0) * ((double)it / (double)iters);
        int i = rndint(KS);
        int y = rndint(GORD);
        if (inS_upto(y, KS)) continue;
        int old = S[i];
        touch(i, old, -1);
        S[i] = y;
        touch(i, y, 1);
        int nc = uncovered();
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            touch(i, y, -1);
            S[i] = old;
            touch(i, old, 1);
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x2545F4914F6CDD1DULL;
    double budget = atof(argv[4]);
    int lo = argc > 5 ? atoi(argv[5]) : 0;
    if (D != 3 || d < 3 || d > 100) { printf("0 0\n"); return 0; }

    double deadline = now_s() + budget;
    KS = d;
    int cap = d * (d - 1) + 1;   /* |G| - 1 <= k(k-1) is necessary */
    int Gt = lo > d + 1 ? lo : d + 1;
    int bestG = 0, bestM = 0, bestK = 0, bestR = 0;
    static int bestS[MAXG];

    while (Gt <= cap && Gt < MAXG) {
        double t_now = now_s();
        if (t_now >= deadline) break;
        int ng = list_groups(Gt);
        if (ng == 0) { Gt++; continue; }
        for (int i = 0; i < ng; i++) ordv[i] = i;
        double slice_end = t_now + 0.5 * (deadline - t_now);
        int found = 0;
        while (!found && now_s() < slice_end) {
            for (int i = ng - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = ordv[i]; ordv[i] = ordv[j]; ordv[j] = tmp;
            }
            for (int t = 0; t < ng && !found; t++) {
                if (now_s() >= slice_end) break;
                int g = ordv[t];
                build_group(GLM[g], GLK[g], GLR[g]);
                if (anneal(ITERS, 1.0, 0.2)) {
                    found = 1;
                    bestG = GORD;
                    bestM = GLM[g];
                    bestK = GLK[g];
                    bestR = GLR[g];
                    for (int j = 0; j < KS; j++) bestS[j] = S[j];
                }
            }
        }
        if (!found) break;
        Gt++;
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    build_group(bestM, bestK, bestR);
    printf("%d %d\n", 2 * GORD, KS * GORD);
    for (int g = 0; g < GORD; g++)
        for (int j = 0; j < KS; j++)
            printf("%d %d\n", g, GORD + mt[g][bestS[j]]);
    return 0;
}
"""


def _c_haar_search(d, budget, lo, seed):
    """Run the C non-abelian cover search for D = 3; return (n, edges) or None."""
    if lo > d * (d - 1) + 1:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, 3, seed, f"{budget:.2f}", lo], timeout=budget + 8.0)
        n, edges = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n <= 0:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D == 3 and d >= 3:
        remaining = 0.72 * time_limit - (time.monotonic() - start)
        if remaining > 2.0:
            res = _c_haar_search(d, remaining, best_n // 2 + 1, seed)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
