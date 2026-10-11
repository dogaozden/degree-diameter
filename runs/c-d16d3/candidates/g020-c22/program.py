import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: search for cyclic Haar graphs H(Z_m, S) with |S| = d.
#
# Vertices a_i (id i) and b_j (id m+j). a_i ~ b_j iff j - i is in S (mod m).
# The map a_i -> a_{i+t}, b_j -> b_{j+t} is an automorphism, and so is
# sigma: a_i -> b_{-i}, b_j -> a_{-j}. Hence every pair of vertices is at
# distance <= D exactly when every vertex is within distance D of a_0.
# The search anneals S to minimise the number of vertices not reached from
# a_0 within D steps, and grows m while it succeeds.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static long rnd_below(long n) {
    return (long)(rnd64() % (uint64_t)n);
}

static double rnd_unit(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int d_;
static int D_;
static long M;
static long *S;
static char *inS;
static int *stamp;
static int *dist;
static long *queue;
static int cur;

static clock_t T_START;

static double elapsed(void) {
    return (double)(clock() - T_START) / (double)CLOCKS_PER_SEC;
}

/* Number of vertices NOT within distance D_ of a_0. */
static long bad_count(void) {
    long head = 0, tail = 0, reached = 1;
    cur++;
    if (cur == 0x7fffffff) {
        memset(stamp, 0, sizeof(int) * (size_t)(2 * M));
        cur = 1;
    }
    stamp[0] = cur;
    dist[0] = 0;
    queue[tail++] = 0;
    while (head < tail) {
        long u = queue[head++];
        int du = dist[u];
        if (du >= D_) continue;
        if (u < M) {
            for (int k = 0; k < d_; k++) {
                long j = u + S[k];
                if (j >= M) j -= M;
                long v = M + j;
                if (stamp[v] != cur) {
                    stamp[v] = cur;
                    dist[v] = du + 1;
                    queue[tail++] = v;
                    reached++;
                }
            }
        } else {
            long j = u - M;
            for (int k = 0; k < d_; k++) {
                long i = j - S[k];
                if (i < 0) i += M;
                if (stamp[i] != cur) {
                    stamp[i] = cur;
                    dist[i] = du + 1;
                    queue[tail++] = i;
                    reached++;
                }
            }
        }
    }
    return 2 * M - reached;
}

static void random_set(void) {
    memset(inS, 0, (size_t)M);
    for (int k = 0; k < d_; k++) {
        long v;
        do {
            v = rnd_below(M);
        } while (inS[v]);
        inS[v] = 1;
        S[k] = v;
    }
}

static long anneal(long iters, double T0, double T1, double tl) {
    random_set();
    long cost = bad_count();
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 255) == 0 && elapsed() >= tl) break;
        double frac = (double)it / (double)iters;
        double T = T0 * pow(T1 / T0, frac);
        int k = (int)rnd_below(d_);
        long nv = rnd_below(M);
        if (inS[nv]) continue;
        long old = S[k];
        inS[old] = 0;
        inS[nv] = 1;
        S[k] = nv;
        long c2 = bad_count();
        long delta = c2 - cost;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            inS[nv] = 0;
            inS[old] = 1;
            S[k] = old;
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    T_START = clock();
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long lo = (argc > 5) ? atol(argv[5]) : 1;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    if (d_ < 1 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }

    /* Moore-type bound on one side: sum_{i<D} (d-1)^i. */
    double mm = 0.0, pw = 1.0;
    for (int i = 0; i < D_; i++) {
        mm += pw;
        pw *= (double)(d_ - 1);
        if (pw > 1e9) break;
    }
    long mmax = (long)mm;
    if (mmax > 3000000) mmax = 3000000;

    long Mcur = lo;
    if (Mcur < d_) Mcur = d_;

    long bestM = 0;
    long *bestS = (long *)malloc(sizeof(long) * (size_t)d_);
    const long ITERS = 30000;

    while (Mcur <= mmax && elapsed() < tl) {
        M = Mcur;
        inS = (char *)malloc((size_t)M);
        stamp = (int *)calloc((size_t)(2 * M), sizeof(int));
        dist = (int *)malloc(sizeof(int) * (size_t)(2 * M));
        queue = (long *)malloc(sizeof(long) * (size_t)(2 * M));
        S = (long *)malloc(sizeof(long) * (size_t)d_);
        cur = 0;

        int found = 0;
        while (elapsed() < tl) {
            long c = anneal(ITERS, 2.0, 0.15, tl);
            if (c == 0) {
                found = 1;
                break;
            }
        }
        if (found) {
            memcpy(bestS, S, sizeof(long) * (size_t)d_);
            bestM = M;
        }
        free(inS);
        free(stamp);
        free(dist);
        free(queue);
        free(S);
        inS = NULL;
        stamp = NULL;
        dist = NULL;
        queue = NULL;
        S = NULL;
        if (!found) break;
        Mcur++;
    }

    if (bestM == 0) {
        printf("0 0\n");
        free(bestS);
        return 0;
    }
    long n = 2 * bestM;
    long ecount = bestM * (long)d_;
    printf("%ld %ld\n", n, ecount);
    for (long i = 0; i < bestM; i++) {
        for (int k = 0; k < d_; k++) {
            long j = (i + bestS[k]) % bestM;
            printf("%ld %ld\n", i, bestM + j);
        }
    }
    free(bestS);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), kept as the
# safe fallback for D >= 3.
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
# Build: Haar-graph difference-cover search in C, with fallbacks.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs (diameter 3) as a second fallback.
    if D >= 3:
        try:
            arcs = _arc_extensions(d, t0 + 0.10 * time_limit, random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs[:2]:
                consider(n_c, e_c)
        except Exception:
            pass

    # Main search: cyclic Haar graphs with a difference-cover-like connection set.
    budget = 0.80 * time_limit - (time.monotonic() - t0) - 1.0
    if D >= 2 and budget >= 2.0:
        lo = max(d, best_n // 4)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo],
                            timeout=budget + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
