import random
import time

import lib


# ----------------------------------------------------------------------------
# Main new construction: Haar graphs H(m, S) over Z_m with |S| = d.
#
# Vertices a_x and b_y (x, y in Z_m); a_x ~ b_{x+s} for s in S. The graph is
# d-regular and bipartite on 2m vertices. Translation x -> x + c is an
# automorphism, so only the representatives a_0 and b_0 need checking. For
# D = 3 the condition is S - S = Z_m, and the Moore bound gives m <= 1 + d(d-1)/2... 
# more precisely 2m <= 2(1 + (d-1) + (d-1)^2) for D = 3, so m <= 241 at d = 16.
#
# A C engine climbs m upward from d+1. For each m it runs simulated annealing
# over d-subsets S, minimising the number of (representative, vertex) pairs
# at distance > D. Every success is kept, so the last success is the output.
#
# Fallbacks: K_{d,d} (valid for D >= 2) and the arc-extended projective plane
# graphs (the parent's construction, which gives 394 at d = 16).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1100
#define MAXK 64
#define ITERS 150000L

static int K, DD, M;
static uint64_t rs = 88172645463325252ULL;
static double T_END;
static int dist_arr[2 * MAXM];
static int queue_arr[2 * MAXM];
static int cur[MAXK];
static int best_sol[MAXK];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 11);
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int contains(const int *A, int k, int r) {
    for (int i = 0; i < k; i++) if (A[i] == r) return 1;
    return 0;
}

/* Number of (representative, vertex) pairs at distance > DD.
   Representatives a_0 and b_0 suffice by translation symmetry. */
static int cost_of(const int *S) {
    int N = 2 * M;
    int total = 0;
    for (int r = 0; r < 2; r++) {
        int src = (r == 0) ? 0 : M;
        for (int i = 0; i < N; i++) dist_arr[i] = -1;
        int qh = 0, qt = 0;
        dist_arr[src] = 0;
        queue_arr[qt++] = src;
        while (qh < qt) {
            int u = queue_arr[qh++];
            int du = dist_arr[u];
            if (du >= DD) continue;
            if (u < M) {
                for (int i = 0; i < K; i++) {
                    int v = M + (u + S[i]) % M;
                    if (dist_arr[v] < 0) {
                        dist_arr[v] = du + 1;
                        queue_arr[qt++] = v;
                    }
                }
            } else {
                int y = u - M;
                for (int i = 0; i < K; i++) {
                    int v = (y - S[i] + M) % M;
                    if (dist_arr[v] < 0) {
                        dist_arr[v] = du + 1;
                        queue_arr[qt++] = v;
                    }
                }
            }
        }
        total += N - qt;
    }
    return total;
}

/* Annealing for a fixed m > K. Returns 1 and stores best_sol on success. */
static int try_m(int m, long iters) {
    const double T0 = 1.5, T1 = 0.15;
    M = m;
    for (int i = 0; i < K; i++) {
        int r;
        do { r = (int)(rnd() % (uint32_t)m); } while (contains(cur, i, r));
        cur[i] = r;
    }
    int c = cost_of(cur);
    if (c == 0) {
        memcpy(best_sol, cur, sizeof(int) * K);
        return 1;
    }
    for (long it = 0; it < iters; it++) {
        if (now() > T_END) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = (int)(rnd() % (uint32_t)K);
        int r;
        do { r = (int)(rnd() % (uint32_t)m); } while (contains(cur, K, r));
        int old = cur[i];
        cur[i] = r;
        int c2 = cost_of(cur);
        int delta = c2 - c;
        int acc = 0;
        if (delta <= 0) {
            acc = 1;
        } else {
            double u = (double)(rnd() % 1000000u) / 1000000.0;
            if (u < exp(-(double)delta / T)) acc = 1;
        }
        if (acc) {
            c = c2;
            if (c == 0) {
                memcpy(best_sol, cur, sizeof(int) * K);
                return 1;
            }
        } else {
            cur[i] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int mmax = atoi(argv[5]);
    if (K < 2 || K > MAXK || DD < 3) { printf("0 0\n"); return 0; }
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    T_END = now() + budget;
    int best_m = K;
    int bs[MAXK];
    for (int i = 0; i < K; i++) bs[i] = i;   /* K_{K,K} fallback */

    int m = K + 1;
    while (m <= mmax && now() < T_END) {
        if (try_m(m, ITERS)) {
            best_m = m;
            memcpy(bs, best_sol, sizeof(int) * K);
            m++;
        }
    }
    printf("%d %d\n", best_m, K);
    for (int i = 0; i < K; i++) printf("%d%c", bs[i], i + 1 < K ? ' ' : '\n');
    return 0;
}
"""


def _haar_climb(d, D, seed, budget):
    """Run the C Haar-graph search; return (n, edges) or None."""
    if d < 2 or budget < 0.5:
        return None
    mmax = min(lib.moore_bound(d, D) // 2, 1000)
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mmax],
                    stdin_graph=None, timeout=budget + 15.0)
    t = out.split()
    m, k = int(t[0]), int(t[1])
    S = [int(x) for x in t[2:2 + k]]
    if m < 1 or k != d or len(S) != k:
        return None
    return lib.haar_graph(m, S)


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Kept from the
# parent as a candidate: at d = 16 it gives 394 via the conic on PG(2, 13).
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
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomised greedy choice so that every target is hit at most s times."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if _loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points):
            out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Driver. Time plan (fractions of time_limit):
#   0.00-0.10  arc-extended PG candidates (cheap)
#   0.10-0.72  C Haar difference-cover climb
# Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2 or d < 2:
        return best

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    rng = random.Random(seed * 7919 + d)
    for g in _arc_extensions(d, start + 0.10 * time_limit, rng):
        consider(g)

    budget = 0.72 * time_limit - elapsed()
    if budget >= 0.5:
        try:
            consider(_haar_climb(d, D, seed, budget))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
