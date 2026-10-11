import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference-cover search for diameter-3 bi-Cayley (Haar-type) graphs.
#
# For a finite group G of order m and a k-subset S, the bipartite graph with
# a_g ~ b_{g s} (s in S) is k-regular on 2m vertices. A-A distances are <= 2 iff
# S S^{-1} = G, B-B distances are <= 2 iff S^{-1} S = G, and A-B distances are
# <= 3 because S S^{-1} S = G then holds. So diameter 3 follows from both covers.
# The search runs simulated annealing on S over the candidate groups of each
# order (cyclic and semidirect products Z_a x|_r Z_k) and raises the order.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1800
#define MAXK 128
#define MAXC 40000

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int M, K;
static int MUL[MAXM * MAXM];
static int INV[MAXM];
static int S[MAXK];
static int inS[MAXM];
static int cnt1[MAXM], cnt2[MAXM];
static int zeros;

typedef struct { int a, k, r; } Grp;
static Grp cands[MAXC];
static int ncand;

static int gcd_i(int x, int y) { while (y) { int t = x % y; x = y; y = t; } return x; }

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

/* Candidate groups of order Mo: cyclic Z_Mo, and Z_a x|_r Z_k with a*k = Mo. */
static void enum_groups(int Mo) {
    ncand = 0;
    for (int k = 1; k <= Mo; k++) {
        if (Mo % k) continue;
        int a = Mo / k;
        if (k == 1) {
            if (ncand < MAXC) cands[ncand++] = (Grp){a, 1, 1};
            continue;
        }
        if (a < 2) continue;
        for (int r = 1; r < a && ncand < MAXC; r++) {
            if (gcd_i(r, a) != 1) continue;
            if (powmod_l(r, k, a) != 1 % a) continue;
            cands[ncand++] = (Grp){a, k, r};
        }
    }
}

/* Multiplication table: element (x1, b1) = x1*k + b1, (x1,b1)(x2,b2) = (x1 + r^b1 x2, b1 + b2). */
static void build_group(Grp g) {
    int a = g.a, k = g.k;
    M = a * k;
    static int pw[MAXM];
    pw[0] = 1 % a;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * g.r % a);
    for (int x = 0; x < M; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < M; y++) {
            int a2 = y / k, b2 = y % k;
            int v1 = (int)((a1 + (long)pw[b1] * a2) % a);
            MUL[x * M + y] = v1 * k + (b1 + b2) % k;
        }
    }
    for (int x = 0; x < M; x++)
        for (int y = 0; y < M; y++)
            if (MUL[x * M + y] == 0) { INV[x] = y; break; }
}

static void bump(int *c, int g, int sgn) {
    if (sgn > 0) {
        if (c[g] == 0) zeros--;
        c[g]++;
    } else {
        c[g]--;
        if (c[g] == 0) zeros++;
    }
}

/* Ordered pair (x, y), x != y: contributes x*y^-1 to cnt1 and x^-1*y to cnt2. */
static void pair_add(int x, int y, int sgn) {
    bump(cnt1, MUL[x * M + INV[y]], sgn);
    bump(cnt2, MUL[INV[x] * M + y], sgn);
}

static void set_replace(int i, int y) {
    int old = S[i];
    for (int j = 0; j < K; j++)
        if (j != i) {
            pair_add(old, S[j], -1);
            pair_add(S[j], old, -1);
        }
    inS[old] = 0;
    S[i] = y;
    inS[y] = 1;
    for (int j = 0; j < K; j++)
        if (j != i) {
            pair_add(y, S[j], 1);
            pair_add(S[j], y, 1);
        }
}

/* Simulated annealing for S with S S^-1 = G and S^-1 S = G. Returns 1 on success. */
static int anneal(double tend, long iters) {
    memset(inS, 0, sizeof(int) * M);
    for (int i = 0; i < K;) {
        int x = rndi(M);
        if (!inS[x]) { inS[x] = 1; S[i++] = x; }
    }
    memset(cnt1, 0, sizeof(int) * M);
    memset(cnt2, 0, sizeof(int) * M);
    zeros = 2 * (M - 1);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) pair_add(S[i], S[j], 1);

    double T = 1.5, T1 = 0.08;
    double fac = pow(T1 / T, 1.0 / (double)iters);
    for (long it = 0; it < iters; it++, T *= fac) {
        if (zeros == 0) return 1;
        if ((it & 4095) == 0 && now_s() > tend) break;
        int i = rndi(K);
        int old = S[i];
        int which = rndi(2);
        int *cc = which ? cnt2 : cnt1;
        int g = -1;
        int st = rndi(M - 1);
        for (int t = 0; t < M - 1; t++) {
            int c = 1 + (st + t) % (M - 1);
            if (cc[c] == 0) { g = c; break; }
        }
        int y;
        if (g > 0 && rndu() < 0.7) {
            int j = rndi(K - 1);
            if (j >= i) j++;
            if (which == 0) y = MUL[g * M + S[j]];
            else y = MUL[S[j] * M + INV[g]];
        } else {
            y = rndi(M);
        }
        if (inS[y]) continue;
        int oldz = zeros;
        set_replace(i, y);
        int dz = zeros - oldz;
        if (dz > 0 && rndu() >= exp(-dz / T)) set_replace(i, old);
    }
    return zeros == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double tend = now_s() + budget;

    if (D != 3 || d < 2 || d > MAXK) {
        printf("0 0\n");
        return 0;
    }
    K = d;
    int cap = K * (K - 1) + 1;
    if (cap > MAXM - 1) cap = MAXM - 1;
    int target = (int)(0.8 * cap);
    if (target < K + 1) target = K + 1;

    int best_m = 0;
    int best_S[MAXK];
    Grp best_g = {1, 1, 1};
    int fails = 0;
    long iters = 1500000;

    while (now_s() < tend && target <= cap) {
        enum_groups(target);
        if (ncand == 0) {
            target--;
            if (target < K + 1) break;
            continue;
        }
        Grp g = cands[rndi(ncand)];
        build_group(g);
        int ok = anneal(tend, iters);
        if (ok) {
            best_m = M;
            best_g = g;
            memcpy(best_S, S, sizeof(int) * K);
            target = best_m + 1;
            fails = 0;
        } else {
            fails++;
            if (best_m == 0 && fails % 3 == 0) target -= 2;
            if (target < K + 1) target = K + 1;
        }
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    build_group(best_g);
    memcpy(S, best_S, sizeof(int) * K);
    int n = 2 * M, m = M * K;
    printf("%d %d\n", n, m);
    for (int x = 0; x < M; x++)
        for (int j = 0; j < K; j++)
            printf("%d %d\n", x, M + MUL[x * M + S[j]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3, any d >= q + 2).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare capacity is s = d - q - 1. Choose point set SA with
# every line holding <= s points of SA (A-vertex per point joined to its lines),
# and line set SB with every point on <= s lines of SB (B-vertex per line).
# The two sides are independent, so each is optimized separately.
# ----------------------------------------------------------------------------

def _pg_data(q):
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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, pl, lp, SA, SB):
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _ = _pg_data(q)
        SA = _greedy_side(m, s, pl, rng, 30, deadline)
        SB = _greedy_side(m, s, lp, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
                SB = cs
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

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

    # Arc-extended projective plane graphs: valid for every D >= 3.
    if D >= 3 and d >= 2:
        cands = _arc_candidates(d, start + 0.08 * time_limit, rng)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands[:3]:
            consider(n_c, e_c)

    # Main search for D = 3: difference-cover bi-Cayley graphs in C.
    if D == 3 and d >= 2:
        budget = max(1.0, 0.8 * time_limit - 1.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=None,
                            timeout=0.92 * time_limit)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    # Generalized quadrangle baseline for D >= 4.
    if D >= 4 and best_n < 2 * (d * d):
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
