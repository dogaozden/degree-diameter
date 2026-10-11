import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bi-Cayley (Haar-type) graphs over finite groups.
#
# Let G be a group of order N and S a set of d distinct elements. The graph has
# vertices a_g and b_g (g in G) and edges a_g -- b_{g*s} for s in S. It is
# d-regular and bipartite. Left multiplication by h is an automorphism
# (a_g -> a_{hg}, b_g -> b_{hg}), so the diameter is at most D iff the
# eccentricities of a_1 and b_1 are at most D. The C engine therefore checks
# only two BFS runs per candidate S, and anneals S to make both reach everything.
#
# The group is a semidirect product Z_m x| Z_k (element a*k+b, multiplication
# (a,b)(c,d) = (a + r^b c, b+d)); k = 1 gives cyclic groups. For each order N we
# try several groups. Once a valid S is found for N, N is increased by one.
# Any failure keeps the best valid graph found so far, and K_{d,d} or the
# generalized quadrangle incidence graph is the fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1600

static int M, K, R, N, DEG, DIAM;
static int *MT;
static int INV[MAXG];
static int PW[MAXG];
static int S[64], Sinv[64];
static char inS[MAXG];
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

static int gmul(int x, int y) { return MT[x * N + y]; }

/* Number of vertices NOT within DIAM of src in the bi-Cayley graph. */
static int bfs_unreached(int src) {
    int V = 2 * N;
    for (int i = 0; i < V; i++) dist[i] = -1;
    int qh = 0, qt = 0;
    qu[qt++] = src;
    dist[src] = 0;
    while (qh < qt) {
        int u = qu[qh++];
        int du = dist[u];
        if (du >= DIAM) continue;
        if (u < N) {
            for (int i = 0; i < DEG; i++) {
                int w = N + gmul(u, S[i]);
                if (dist[w] < 0) {
                    dist[w] = du + 1;
                    qu[qt++] = w;
                }
            }
        } else {
            int h = u - N;
            for (int i = 0; i < DEG; i++) {
                int w = gmul(h, Sinv[i]);
                if (dist[w] < 0) {
                    dist[w] = du + 1;
                    qu[qt++] = w;
                }
            }
        }
    }
    return V - qt;
}

static long cost(void) { return (long)bfs_unreached(0) + (long)bfs_unreached(N); }

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0\n");
        return 0;
    }
    M = atoi(argv[1]);
    K = atoi(argv[2]);
    R = atoi(argv[3]);
    DEG = atoi(argv[4]);
    DIAM = atoi(argv[5]);
    unsigned long long seed = strtoull(argv[6], NULL, 10);
    double tl = atof(argv[7]);
    if (M < 2 || K < 1) {
        printf("0\n");
        return 0;
    }
    N = M * K;
    if (N > MAXG || DEG < 1 || DEG > 64 || DEG >= N || DIAM < 1 || tl <= 0) {
        printf("0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    /* Multiplication table of Z_M x|_R Z_K, element a*K + b. */
    MT = malloc(sizeof(int) * (size_t)N * (size_t)N);
    if (!MT) {
        printf("0\n");
        return 0;
    }
    PW[0] = 1 % M;
    for (int b = 1; b < K; b++) PW[b] = (int)(((long long)PW[b - 1] * R) % M);
    for (int x = 0; x < N; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < N; y++) {
            int c = y / K, d = y % K;
            MT[x * N + y] = ((a + PW[b] * c) % M) * K + (b + d) % K;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) INV[x] = y;

    memset(inS, 0, sizeof(inS));
    for (int i = 0; i < DEG; i++) {
        int x;
        do {
            x = rnd(N);
        } while (inS[x]);
        inS[x] = 1;
        S[i] = x;
        Sinv[i] = INV[x];
    }

    long cur = cost();
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    double frac = 0.0;
    long it = 0;
    while (cur > 0) {
        if ((it & 63) == 0) {
            double el = (double)clock() / CLOCKS_PER_SEC - t0;
            if (el >= tl) break;
            frac = el / tl;
        }
        it++;
        double T = 0.8 * (1.0 - frac) + 0.15;
        int i = rnd(DEG);
        int old = S[i];
        int nw;
        do {
            nw = rnd(N);
        } while (inS[nw]);
        inS[old] = 0;
        inS[nw] = 1;
        S[i] = nw;
        Sinv[i] = INV[nw];
        long c2 = cost();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            inS[nw] = 0;
            inS[old] = 1;
            S[i] = old;
            Sinv[i] = INV[old];
        }
    }

    if (cur == 0) {
        printf("1");
        for (int i = 0; i < DEG; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("0\n");
    }
    free(MT);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q <= d - 1 (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _bicayley(m, k, r, S):
    """Bi-Cayley graph over Z_m x|_r Z_k with connection set S: a_g -- b_{g*s}."""
    N, mul, _ = lib.semidirect_group(m, k, r)
    edges = [(g, N + mul(g, s)) for g in range(N) for s in S]
    return 2 * N, edges


def _groups_of(N, rng):
    """Candidate groups of order N: cyclic first, then sampled semidirect products."""
    cyc, rest = [], []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            cyc.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        rest += [(m, k, r) for r in rs[:4]]
    rng.shuffle(rest)
    return cyc + rest[:24]


def _scan(d, D, rng, n_start, deadline):
    """Find bi-Cayley graphs of increasing order N; retry the same N with longer budgets on failure."""
    best = None
    N = n_start
    mult = 1.0
    while True:
        if deadline - time.monotonic() < 0.6 or mult > 16:
            break
        found = None
        for (m, k, r) in _groups_of(N, rng):
            remaining = deadline - time.monotonic()
            if remaining < 0.6:
                break
            bud = min(0.4 * mult, remaining - 0.4)
            if bud < 0.1:
                break
            try:
                out = lib.run_c(C_SOURCE, [m, k, r, d, D, rng.randrange(1 << 30), f"{bud:.2f}"],
                                timeout=bud + 5.0)
            except RuntimeError:
                continue
            tok = out.split()
            if len(tok) == d + 1 and tok[0] == "1":
                S = [int(x) for x in tok[1:]]
                n2, e2 = _bicayley(m, k, r, S)
                if lib.is_valid(n2, e2, d, D):
                    found = (n2, e2)
                    break
        if found is not None:
            if best is None or found[0] > best[0]:
                best = found
            N += 1
            mult = 1.0
        else:
            mult *= 2.0
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

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

    # D = 4: generalized quadrangle incidence graph as a stronger fallback.
    if D == 4 and d >= 3:
        try:
            g = _best_gq(d)
            if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = g
        except Exception:
            pass

    deadline = start + 0.88 * tl - 1.0
    try:
        res = _scan(d, D, rng, max(d + 1, best[0] // 2 + 1), deadline)
    except Exception:
        res = None

    if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
        best = res
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
