import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing for BI-CAYLEY graphs over a finite group G of
# order N = m*k (semidirect product Z_m x| Z_k, element (a,b) coded a*k+b).
#
# Graph: A-vertices g and B-vertices N+g, with edge g -- N + g*s for each s in S
# (|S| = d, distinct). Left multiplication by h is an automorphism, so G acts
# transitively on each side. Diameter <= D holds iff a_1 reaches all 2N vertices
# within D steps AND b_1 reaches all 2N vertices within D steps. The cost is the
# total number of unreached vertices from these two sources, so cost 0 is exact.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 2048
#define MAXD 64
#define STALL 30000

static int M, K, N, DEG, DIAM;
static int PW[MAXG];
static int INV[MAXG];
static int S[MAXD], IS[MAXD], bestS[MAXD];
static int dist[2 * MAXG];
static int qu[2 * MAXG];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, d = y % K;
    int t = (int)(((long long)a + (long long)PW[b] * c) % M);
    return t * K + (b + d) % K;
}

static void setIS(void) {
    for (int i = 0; i < DEG; i++) IS[i] = INV[S[i]];
}

/* Number of vertices reached from src within DIAM steps. */
static int reach(int src) {
    int V = 2 * N;
    for (int i = 0; i < V; i++) dist[i] = -1;
    int head = 0, tail = 0;
    qu[tail++] = src;
    dist[src] = 0;
    while (head < tail) {
        int u = qu[head++];
        if (dist[u] >= DIAM) continue;
        int nd = dist[u] + 1;
        if (u < N) {
            for (int i = 0; i < DEG; i++) {
                int w = N + gmul(u, S[i]);
                if (dist[w] < 0) {
                    dist[w] = nd;
                    qu[tail++] = w;
                }
            }
        } else {
            int h = u - N;
            for (int i = 0; i < DEG; i++) {
                int w = gmul(h, IS[i]);
                if (dist[w] < 0) {
                    dist[w] = nd;
                    qu[tail++] = w;
                }
            }
        }
    }
    return tail;
}

static long long cost(void) {
    int V = 2 * N;
    return (long long)(V - reach(0)) + (long long)(V - reach(N));
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("FAIL\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    M = atoi(argv[3]);
    K = atoi(argv[4]);
    int r = atoi(argv[5]);
    unsigned long long seed = strtoull(argv[6], NULL, 10);
    double tl = atof(argv[7]);
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || M < 2 || K < 1 || tl <= 0) {
        printf("FAIL\n");
        return 0;
    }
    if ((long long)M * K > MAXG) {
        printf("FAIL\n");
        return 0;
    }
    N = M * K;
    if (DEG > N) {
        printf("FAIL\n");
        return 0;
    }
    r %= M;
    if (r < 0) r += M;

    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    PW[0] = 1 % M;
    for (int b = 1; b < K; b++) PW[b] = (int)((long long)PW[b - 1] * r % M);

    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if (gmul(x, y) == 0) {
                INV[x] = y;
                break;
            }
        }
        if (INV[x] < 0) {
            printf("FAIL\n");
            return 0;
        }
    }

    static int used[MAXG];
    memset(used, 0, sizeof used);
    for (int i = 0; i < DEG; i++) {
        int x;
        do {
            x = rnd(N);
        } while (used[x]);
        used[x] = 1;
        S[i] = x;
    }
    setIS();

    long long cur = cost();
    long long best = cur;
    memcpy(bestS, S, sizeof(int) * DEG);

    double tstart = (double)clock() / CLOCKS_PER_SEC;
    double frac = 0.0;
    long long it = 0, lastImp = 0;

    while (cur > 0) {
        if ((it & 127) == 0) {
            frac = ((double)clock() / CLOCKS_PER_SEC - tstart) / tl;
            if (frac >= 1.0) break;
        }
        it++;

        if (it - lastImp > STALL) {
            memcpy(S, bestS, sizeof(int) * DEG);
            for (int t = 0; t < 2; t++) {
                int i = rnd(DEG), x = rnd(N);
                int dup = 0;
                for (int j = 0; j < DEG; j++)
                    if (S[j] == x) { dup = 1; break; }
                if (!dup) S[i] = x;
            }
            setIS();
            cur = cost();
            lastImp = it;
            continue;
        }

        int i = rnd(DEG), x = rnd(N);
        int dup = 0;
        for (int j = 0; j < DEG; j++)
            if (S[j] == x) { dup = 1; break; }
        if (dup) continue;

        int old = S[i];
        S[i] = x;
        IS[i] = INV[x];
        long long c2 = cost();
        double T = 0.8 * (1.0 - frac) + 0.08;
        long long dl = c2 - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(bestS, S, sizeof(int) * DEG);
                lastImp = it;
            }
        } else {
            S[i] = old;
            IS[i] = INV[old];
        }
    }

    if (cur == 0) {
        printf("OK");
        for (int i = 0; i < DEG; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: group choice, attempt schedule, and fallback constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _group_options(N):
    """All (m, k, r) with N = m*k, giving the semidirect product Z_m x| Z_k (r^k = 1 mod m)."""
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _run_sa(d, D, m, k, r, seed, budget):
    """Run the C bi-Cayley annealer; return the connection set S (list of d group elements) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, m, k, r, seed, f"{budget:.2f}"],
                        timeout=budget + 5.0)
    except RuntimeError:
        return None
    toks = out.split()
    if len(toks) != d + 1 or toks[0] != "OK":
        return None
    try:
        return [int(x) for x in toks[1:]]
    except ValueError:
        return None


def _attempt(N, rng, deadline, d, D, consider, tries):
    """Try a few groups of order N; on success pass the bi-Cayley graph (2N vertices) to consider."""
    opts = _group_options(N)
    if not opts or N < d:
        return False
    for _ in range(tries):
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            return False
        m, k, r = rng.choice(opts)
        budget = min(6.0, max(0.5, 0.3 * remaining))
        S = _run_sa(d, D, m, k, r, rng.randrange(1, 1 << 30), budget)
        if S is None:
            continue
        _, mul, _ = lib.semidirect_group(m, k, r)
        edges = [(g, N + mul(g, s)) for g in range(N) for s in S]
        if lib.is_valid(2 * N, edges, d, D):
            consider(2 * N, edges)
            return True
    return False


def _bicayley_search(d, D, rng, deadline, best_n, consider):
    """Search for the largest N such that a bi-Cayley graph of order 2N works.

    Ascending steps while feasible, then bisection between the last success and the first failure.
    """
    lo = None
    hi = None
    cur = max(d + 1, best_n // 2 + 1)
    step = 16
    while time.monotonic() < deadline - 0.5:
        cur = max(cur, d)
        if cur > 1500:
            break
        ok = _attempt(cur, rng, deadline, d, D, consider, 2)
        if ok:
            lo = cur if lo is None else max(lo, cur)
            if hi is None:
                step = min(step * 2, 64)
                cur = lo + step
            else:
                if hi - lo <= 1:
                    break
                cur = (lo + hi) // 2
        else:
            hi = cur if hi is None else min(hi, cur)
            if lo is None:
                if hi <= d:
                    break
                step = max(1, step // 2)
                cur = max(d, hi - step)
            else:
                if hi - lo <= 1:
                    break
                cur = (lo + hi) // 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)
    deadline = start + max(0.0, 0.88 * tl - 1.0)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Cheap algebraic fallbacks.
    try:
        if D == 3 and d >= 3:
            qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
            if qs:
                pn, pe = lib.projective_plane_incidence(qs[0])
                consider(pn, pe)
        if D == 4 and d >= 3 and tl >= 15:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
    except Exception:
        pass

    # Main search: bi-Cayley graphs over semidirect products of order N.
    if d >= 2 and D >= 2:
        try:
            _bicayley_search(d, D, rng, deadline, best_n, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
