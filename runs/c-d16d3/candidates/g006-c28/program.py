"""Bi-Cayley search for D = 3, with the arc-extended projective-plane construction as a fallback.

A bi-Cayley graph over a group G of order N with connection set S (|S| = d) has vertices
(g,0) and (g,1) with (g,0) ~ (g s,1). It is bipartite and d-regular. Its diameter is at most 3
exactly when S S^-1 = G and S^-1 S = G, so each such S gives a valid graph on 2N vertices.
The C engine searches for such S by annealing over several groups of each order N, starting
just above the current best order. Python builds the known constructions, runs C, and checks
every result with lib.is_valid before returning it.
"""
import random
import time

import lib

BICAY_C = r'''
/* Bi-Cayley difference-cover search for bipartite degree-diameter graphs with D = 3.
 *
 * Usage:  prog d D seed time_limit minN
 * Output: "n m" then m lines "u v" for the largest valid bi-Cayley graph found with
 *         N >= minN (n = 2N), or "0 0" if none is found.
 *
 * Group G = Z_m semidirect Z_k (element a*k+b), product (a + r^b c, b + e), with r^k = 1 mod m.
 * Cyclic groups are the case k = 1, r = 1.
 * Vertices (g,0) and (g,1) for g in G; edge (g,0)-(g s,1) for every s in S, |S| = d.
 * Valid iff S S^-1 = G and S^-1 S = G.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64
#define MAXN 560
#define MAXG 8192

typedef struct { int m, k, r; } Grp;

static int d;
static int N;
static int GM[MAXN][MAXN];
static int GI[MAXN];
static int S[MAXD];
static unsigned char inS[MAXN];
static int cov1[MAXN], cov2[MAXN];
static int unc;
static Grp GL[MAXG];
static int ngl;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ coverage counters */

static void inc1(int g) { if (cov1[g]++ == 0) unc--; }
static void dec1(int g) { if (--cov1[g] == 0) unc++; }
static void inc2(int g) { if (cov2[g]++ == 0) unc--; }
static void dec2(int g) { if (--cov2[g] == 0) unc++; }

/* Add (sign > 0) or remove (sign < 0) every ordered pair involving slot i. */
static void pairs_update(int i, int sign) {
    int x = S[i], ix = GI[x];
    if (sign > 0) { inc1(0); inc2(0); }
    else          { dec1(0); dec2(0); }
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int t = S[j], it = GI[t];
        if (sign > 0) {
            inc1(GM[x][it]);
            inc1(GM[t][ix]);
            inc2(GM[ix][t]);
            inc2(GM[it][x]);
        } else {
            dec1(GM[x][it]);
            dec1(GM[t][ix]);
            dec2(GM[ix][t]);
            dec2(GM[it][x]);
        }
    }
}

static void rebuild(void) {
    memset(cov1, 0, sizeof(int) * (size_t)N);
    memset(cov2, 0, sizeof(int) * (size_t)N);
    unc = 2 * N;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int s = S[i], t = S[j];
            inc1(GM[s][GI[t]]);
            inc2(GM[GI[s]][t]);
        }
}

/* ------------------------------------------------------------ groups */

static int build_group(int m, int k, int r) {
    int n = m * k;
    if (m < 2 || k < 1 || n > MAXN - 1) return 0;
    static int rp[MAXN];
    rp[0] = 1;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    N = n;
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            GM[x][y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < n; x++) {
        GI[x] = -1;
        for (int y = 0; y < n; y++)
            if (GM[x][y] == 0) { GI[x] = y; break; }
        if (GI[x] < 0) return 0;
    }
    return 1;
}

static void list_groups(int n) {
    ngl = 0;
    for (int k = 1; k <= n; k++) {
        if (n % k) continue;
        int m = n / k;
        if (m < 2) continue;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            if (ngl < MAXG) {
                GL[ngl].m = m;
                GL[ngl].k = k;
                GL[ngl].r = r;
                ngl++;
            }
        }
    }
}

/* ------------------------------------------------------------ annealing */

static int run_sa(long maxit, double T0, double T1) {
    double lr = log(T1 / T0);
    for (long it = 0; it < maxit; it++) {
        if (unc == 0) return 1;
        if ((it & 1023) == 0 && now() > t_end) return 0;
        double T = T0 * exp(lr * (double)it / (double)maxit);
        int i = rndint(d);
        int a = S[i];
        int x;
        do { x = rndint(N); } while (inS[x]);
        int old = unc;
        pairs_update(i, -1);
        S[i] = x;
        inS[a] = 0;
        inS[x] = 1;
        pairs_update(i, +1);
        int delta = unc - old;
        if (delta <= 0 || rnd01() < exp(-delta / T)) continue;
        pairs_update(i, -1);
        S[i] = a;
        inS[x] = 0;
        inS[a] = 1;
        pairs_update(i, +1);
    }
    return unc == 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit minN\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int minN = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 3 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    int Nmax = d * (d - 1) + 1;
    if (minN < d + 1) minN = d + 1;

    int bestN = 0;
    Grp bestG = {0, 0, 0};
    int BS[MAXD];

    for (int n = minN; n <= Nmax && n < MAXN && now() < t_end; n++) {
        list_groups(n);
        if (ngl == 0) break;
        int found = 0;
        while (!found && now() < t_end) {
            Grp g = GL[rndint(ngl)];
            if (!build_group(g.m, g.k, g.r)) continue;
            memset(inS, 0, sizeof(unsigned char) * (size_t)N);
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (inS[x]);
                S[i] = x;
                inS[x] = 1;
            }
            rebuild();
            if (run_sa(300000, 1.0, 0.1)) {
                found = 1;
                bestN = n;
                bestG = g;
                memcpy(BS, S, sizeof(int) * (size_t)d);
            }
        }
        if (!found) break;
    }

    if (!bestN) {
        printf("0 0\n");
        return 0;
    }
    build_group(bestG.m, bestG.k, bestG.r);
    printf("%d %ld\n", 2 * bestN, (long)bestN * d);
    for (int g = 0; g < bestN; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, bestN + GM[g][BS[i]]);
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
    and a new B-vertex on the points of line P. Diameter 3, max degree q+1+s."""
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
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
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

    # Bold path for D = 3: search bi-Cayley graphs over groups of order N >= best/2 + 1.
    if D == 3 and 3 <= d <= 23 and best[0] < lib.moore_bound(d, D):
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
        if budget > 1.0:
            min_n = best[0] // 2 + 1
            try:
                text = lib.run_c(BICAY_C, [d, D, seed, round(budget, 2), min_n],
                                 timeout=budget + 5)
                n, e = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except (RuntimeError, ValueError):
                pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
