"""Cyclic Haar-graph search: bipartite graphs on Z_m x {A, B} with A_x ~ B_{x+s} for s in S, |S| = d.

The C core runs simulated annealing over the connection set S for a growing modulus m. Diameter
is checked with two BFS runs (from A_0 and B_0), because translations of Z_m act transitively on
each side. Exact constructions (projective planes, Araujo-Lopez, generalized quadrangles) are kept
for the cases where they apply. K_{d,d} is the safe fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Cyclic Haar-graph search.
 * Usage: prog d D seed time_limit m_start
 * Output: "n m" plus edge lines for the best valid Haar graph found (K_{d,d} if none).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 4096
#define MAXDG 32

static int d, D, M;
static int S[MAXDG];
static int dist_[2 * MAXM];
static int q_[2 * MAXM];
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Number of nodes NOT reached from src within D steps. Nodes 0..M-1 are A, M..2M-1 are B. */
static int bfs_unreached(int src) {
    int N = 2 * M;
    for (int i = 0; i < N; i++) dist_[i] = -1;
    int h = 0, t = 0;
    q_[t++] = src;
    dist_[src] = 0;
    while (h < t) {
        int v = q_[h++];
        if (dist_[v] >= D) continue;
        int nd = dist_[v] + 1;
        if (v < M) {
            for (int i = 0; i < d; i++) {
                int u = v + S[i];
                if (u >= M) u -= M;
                u += M;
                if (dist_[u] < 0) {
                    dist_[u] = nd;
                    q_[t++] = u;
                }
            }
        } else {
            int y = v - M;
            for (int i = 0; i < d; i++) {
                int x = y - S[i];
                if (x < 0) x += M;
                if (dist_[x] < 0) {
                    dist_[x] = nd;
                    q_[t++] = x;
                }
            }
        }
    }
    return N - t;
}

/* Zero iff the Haar graph has diameter <= D (translation symmetry covers all pairs). */
static int cost(void) { return bfs_unreached(0) + bfs_unreached(M); }

static int in_set(int v, int skip) {
    for (int j = 0; j < d; j++)
        if (j != skip && S[j] == v) return 1;
    return 0;
}

static int try_m(int m, long iters) {
    M = m;
    for (int j = 0; j < d; j++) S[j] = -1;
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int v;
        do {
            v = rndint(M);
        } while (in_set(v, i));
        S[i] = v;
    }
    int c = cost();
    if (c == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now() > t_end) return 0;
        int i = 1 + rndint(d - 1);
        int old = S[i];
        int v;
        do {
            v = rndint(M);
        } while (in_set(v, i));
        S[i] = v;
        int c2 = cost();
        double frac = (double)it / (double)iters;
        double T = 0.3 + 6.0 * (1.0 - frac);
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c == 0) return 1;
        } else {
            S[i] = old;
        }
    }
    return 0;
}

static void print_haar(int m, const int *Sv) {
    printf("%d %ld\n", 2 * m, (long)m * d);
    for (int x = 0; x < m; x++)
        for (int j = 0; j < d; j++) {
            int y = (x + Sv[j]) % m;
            printf("%d %d\n", x, m + y);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double lim = atof(argv[4]);
    int mstart = argc > 5 ? atoi(argv[5]) : d;
    if (d < 2 || D < 2) {
        printf("2 1\n0 1\n");
        return 0;
    }
    if (d > MAXDG) {
        printf("2 1\n0 1\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + lim;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long moore;
    {
        long s = 0, p = 1;
        for (int i = 0; i < D && s <= 1000000L; i++) {
            s += p;
            p *= (d - 1);
        }
        moore = 2 * s;
    }
    int mcap = (int)(moore / 2);
    if (mcap > MAXM) mcap = MAXM;
    if (mcap < d) mcap = d;
    if (mstart < d) mstart = d;
    if (mstart > mcap) mstart = mcap;

    int best = 0;
    int bestS[MAXDG];
    int cur = mstart;

    while (now() < t_end) {
        int m;
        if (best == 0) {
            m = cur;
        } else {
            int span = 1 + best / 100;
            m = best + 1 + rndint(span);
        }
        if (m > mcap) m = mcap;
        if (m <= best) break;
        if (try_m(m, 4000)) {
            best = m;
            memcpy(bestS, S, sizeof(int) * d);
        } else if (best == 0) {
            int dec = 1 + cur / 20;
            cur -= dec;
            if (cur < d) cur = d;
        }
    }

    if (best == 0) {
        best = d;
        for (int j = 0; j < d; j++) bestS[j] = j;
    }
    print_haar(best, bestS);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions for calibration-style cases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 3.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the current best with (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # New construction: cyclic Haar-graph search in C.
    budget = end - time.monotonic() - 0.5
    if budget > 1.0:
        moore = lib.moore_bound(d, D)
        mstart = max(d, moore // 4)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mstart],
                             stdin_graph=None, timeout=budget + 8)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
