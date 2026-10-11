"""Bold variant: group-Haar diameter-3 search, with the structured starts kept as fallbacks.

New construction. For a finite group G of order N and a d-subset S of G, the bipartite
graph on A = G and B = G (a_x ~ b_{x s} for s in S) has max degree d. It has diameter
at most 3 exactly when S S^{-1} = G, since then every pair of same-side vertices is
at distance 2, and every cross pair is at distance 1 or 3 (because S S^{-1} S = G).
So the problem becomes: find a group G of order N as large as possible (N <= d^2-d+1)
and a covering set S with S S^{-1} = G.

Groups are semidirect products Z_m x| Z_k (all admissible (m, k, r)), so cyclic
groups and non-abelian groups are both covered. A C engine scans N upward, runs
simulated annealing on S (cost = number of group elements not in S S^{-1}), and
prints the Haar graph of the largest order it covered.

Fallbacks, all checked with lib.is_valid: the Araujo-Pardo/Lopez and projective-plane
starts when they apply, the conic blow-up, and the PG(2,q) incidence graph extended
by a local-search arc (these reproduce the previous parent's order). K_{d,d} is the
always-valid last resort. The largest valid candidate is returned.
"""
import itertools
import random
import time

import lib

C_HAAR = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 512
#define MAXD 40

typedef struct { int m, k, r; } Grp;

static int d;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
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

static int N;
static int MT[MAXN][MAXN];
static int INV[MAXN];
static int rp[MAXN];

/* Elements of Z_m x|_r Z_k are coded a*k+b; identity is 0. */
static void build_group(int m, int k, int r) {
    N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int a = x / k, b = x % k, c = y / k, e = y % k;
            MT[x][y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

static int S[MAXD];
static int mark[MAXN];
static int stamp = 0;

static int cost_of(const int *X) {
    stamp++;
    int cnt = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int x = MT[X[i]][INV[X[j]]];
            if (mark[x] != stamp) { mark[x] = stamp; cnt++; }
        }
    return N - cnt;
}

static int has_n(const int *X, int n, int x) {
    for (int i = 0; i < n; i++) if (X[i] == x) return 1;
    return 0;
}

static int anneal(int iters, int *out) {
    if (N < d) return 0;
    if (N == d) {
        for (int i = 0; i < d; i++) out[i] = i;
        return 1;
    }
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(N); } while (has_n(S, i, x));
        S[i] = x;
    }
    int cur = cost_of(S);
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 1023) == 0 && now() > t_end) break;
        double T = pow(0.03, (double)it / (double)iters);
        int i = rndint(d);
        int old = S[i];
        int x;
        do { x = rndint(N); } while (has_n(S, d, x));
        S[i] = x;
        int c = cost_of(S);
        if (c <= cur || rnd01() < exp((double)(cur - c) / T)) cur = c;
        else S[i] = old;
    }
    if (cur != 0) return 0;
    for (int i = 0; i < d; i++) out[i] = S[i];
    return 1;
}

static int ngroups_for(int Nn, Grp *G, int cap) {
    int cnt = 0;
    for (int m = 1; m <= Nn; m++) {
        if (Nn % m) continue;
        int k = Nn / m;
        if (m == 1) {
            if (cnt < cap) { G[cnt].m = 1; G[cnt].k = k; G[cnt].r = 0; }
            cnt++;
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < cap) { G[cnt].m = m; G[cnt].k = k; G[cnt].r = r; }
            cnt++;
        }
    }
    return cnt;
}

int main(int argc, char **argv) {
    if (argc < 4) return 2;
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + budget;

    int hi = d * d - d + 1;
    if (hi > MAXN - 1) hi = MAXN - 1;
    int lo = d;

    static Grp G[4096];
    int bestN = 0, bm = 0, bk = 0, br = 0;
    int bestS[MAXD];
    int fails = 0;

    for (int Nn = lo; Nn <= hi && now() < t_end; Nn++) {
        int cnt = ngroups_for(Nn, G, 4096);
        if (cnt > 4096) cnt = 4096;
        for (int i = cnt - 1; i > 0; i--) {
            int j = rndint(i + 1);
            Grp t = G[i]; G[i] = G[j]; G[j] = t;
        }
        int tries = cnt < 24 ? cnt : 24;
        int success = 0;
        for (int gi = 0; gi < tries && now() < t_end && !success; gi++) {
            build_group(G[gi].m, G[gi].k, G[gi].r);
            for (int rep = 0; rep < 2 && !success && now() < t_end; rep++) {
                int out[MAXD];
                if (anneal(50000, out)) {
                    success = 1;
                    bestN = Nn;
                    bm = G[gi].m; bk = G[gi].k; br = G[gi].r;
                    for (int i = 0; i < d; i++) bestS[i] = out[i];
                }
            }
        }
        if (success) fails = 0;
        else if (++fails >= 3) break;
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    build_group(bm, bk, br);
    printf("%d %d\n", 2 * bestN, bestN * d);
    for (int x = 0; x < bestN; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, bestN + MT[x][bestS[i]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (fallbacks, validated before use).
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Moore graph or Araujo-Pardo/Lopez graph for D = 3 when they apply."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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


def _local_arc(m, s, point_lines, line_points, rng, init, deadline, iters):
    """Plateau local search for a large set S where each line and point carries at most s members."""
    inS = [False] * m
    cl = [0] * m
    cp = [0] * m
    S = []

    def fits(P):
        return all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P])

    def put(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def take(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    for P in init:
        if not inS[P] and fits(P):
            put(P)
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            put(P)
        else:
            fullL = {L for L in point_lines[P] if cl[L] >= s}
            fullQ = {Q for Q in line_points[P] if cp[Q] >= s}
            blockers = [Q for Q in S
                        if any(L in fullL for L in point_lines[Q])
                        or any(R in fullQ for R in line_points[Q])]
            if len(blockers) != 1:
                continue
            b = blockers[0]
            take(b)
            if fits(P):
                put(P)
            else:
                put(b)
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[], _greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2 and q >= 3:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        init = max(cands, key=len)
        loc = _local_arc(m, s, pl, lp, rng, init,
                         min(deadline, time.monotonic() + 0.5), 4000)
        cands.append(loc)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def starts(d, D, deadline, rng):
    out = []
    try:
        ks = known_start(d, D)
        if ks is not None:
            out.append(ks)
    except Exception:
        pass
    try:
        cb = conic_blowup(d, D)
        if cb is not None:
            out.append(cb)
    except Exception:
        pass
    if D >= 3:
        try:
            out.extend(_arc_extensions(d, deadline, rng))
        except Exception:
            pass
    return out


# ----------------------------------------------------------------------------
# Build: group-Haar search, then pick the largest valid candidate.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    best = fallback
    if D == 2:
        return best
    rng = random.Random(seed * 7919 + d)

    cands = []
    for g in starts(d, D, t0 + 0.20 * time_limit, rng):
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass

    remaining = hard_end - time.monotonic() - 1.5
    if remaining > 2.0:
        try:
            text = lib.run_c(C_HAAR, [d, seed, f"{remaining:.2f}"],
                             timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(text)
            if n > 0 and lib.is_valid(n, e, d, D):
                cands.append((n, e))
        except Exception:
            pass

    for g in cands:
        if g[0] > best[0]:
            best = g
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
