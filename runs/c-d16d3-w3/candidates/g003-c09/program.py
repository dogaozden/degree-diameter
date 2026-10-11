"""Group-Haar difference-cover search for diameter-3 bipartite graphs.

New construction idea: for a finite group G of order m and a set S of size d, the Haar-type
bipartite graph with parts A = G and B = G, joined by g ~ h iff g^{-1}h in S, has 2m vertices
and is d-regular. It has diameter 3 exactly when S S^{-1} = G and S^{-1} S = G, because the
A-A and B-B distances then are at most 2 and every A-B pair is within distance 3 (G S = G).
So the search is for a d-subset of G covering G by both difference sets, with m as large as
possible. The bound m <= d(d-1)+1 comes from counting differences.

The C engine anneals over semidirect products Z_a x| Z_b (x = u*b+v, r^b = 1 mod a), starting
from the largest feasible m above a lower bound, and returns the largest m it covers. Python keeps
the best structured start (projective-plane arc extensions, conic blow-ups, Araujo-Pardo/Lopez,
W(q), K_{d,d}) as the fallback, so the result is never worse than the starts.
"""
import itertools
import random
import time

import lib

C_HAAR = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 640
#define MAXD 40

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
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

/* Current group: element x = u*b + v with u in Z_a, v in Z_b,
   (u,v)(u',v') = (u + r^v u', v + v'). Identity is 0. */
static int GM;
static int MT[MAXM][MAXM];
static int INV[MAXM];

static void build_group(int a, int b, int r) {
    static int pw[MAXM];
    int m = a * b;
    GM = m;
    pw[0] = 1 % a;
    for (int v = 1; v < b; v++) pw[v] = (int)((long)pw[v - 1] * r % a);
    for (int x = 0; x < m; x++) {
        int u = x / b, v = x % b;
        for (int y = 0; y < m; y++) {
            int u2 = y / b, v2 = y % b;
            int u3 = (int)((u + (long)pw[v] * u2) % a);
            int v3 = (v + v2) % b;
            MT[x][y] = u3 * b + v3;
        }
    }
    for (int x = 0; x < m; x++)
        for (int y = 0; y < m; y++)
            if (MT[x][y] == 0) {
                INV[x] = y;
                break;
            }
}

static int cntA[MAXM], cntB[MAXM];

/* Number of non-identity group elements missed by S S^{-1} plus those missed by S^{-1} S. */
static int cover_cost(const int *S, int dd) {
    int m = GM;
    memset(cntA, 0, sizeof(int) * m);
    memset(cntB, 0, sizeof(int) * m);
    for (int i = 0; i < dd; i++)
        for (int j = 0; j < dd; j++) {
            if (i == j) continue;
            int iv = INV[S[j]];
            cntA[MT[S[i]][iv]]++;
            cntB[MT[iv][S[i]]]++;
        }
    int u = 0;
    for (int g = 1; g < m; g++) {
        if (!cntA[g]) u++;
        if (!cntB[g]) u++;
    }
    return u;
}

static int sa_cover(int *S, int m, int dd, double until, long maxit) {
    for (int i = 0; i < dd; i++) {
        for (;;) {
            int y = rndint(m), ok = 1;
            for (int k = 0; k < i; k++)
                if (S[k] == y) {
                    ok = 0;
                    break;
                }
            if (ok) {
                S[i] = y;
                break;
            }
        }
    }
    int cost = cover_cost(S, dd);
    double T = 0.8;
    for (long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 1023) == 0 && now() > until) break;
        int i = rndint(dd), y = rndint(m);
        int dup = 0;
        for (int k = 0; k < dd; k++)
            if (S[k] == y) {
                dup = 1;
                break;
            }
        if (dup) continue;
        int old = S[i];
        S[i] = y;
        int nc = cover_cost(S, dd);
        if (nc <= cost || rnd01() < exp((cost - nc) / T)) cost = nc;
        else S[i] = old;
        T *= 0.9999;
        if (T < 0.12) T = 0.8;
    }
    return cost == 0;
}

static void random_group(int m, int *a, int *b, int *r) {
    int divs[64], nd = 0;
    for (int k = 1; k <= m && nd < 64; k++)
        if (m % k == 0) divs[nd++] = k;
    for (int tries = 0; tries < 200; tries++) {
        int bb = divs[rndint(nd)];
        int aa = m / bb;
        int rr = aa == 1 ? 0 : 1 + rndint(aa - 1);
        if (aa > 1 && gcd(rr, aa) != 1) continue;
        if (powmod(rr, bb, aa) != 1 % aa) continue;
        *a = aa;
        *b = bb;
        *r = rr;
        return;
    }
    *a = m;
    *b = 1;
    *r = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int m_lo = argc > 5 ? atoi(argv[5]) : d;
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D != 3) {
        printf("0 0\n");
        return 0;
    }
    int m_hi = d * (d - 1) + 1;
    if (m_hi > MAXM - 1) m_hi = MAXM - 1;
    if (m_lo < d) m_lo = d;

    int bestm = 0, ba = 0, bb = 0, br = 0;
    int bestS[MAXD];
    int S[MAXD];
    int fails = 0;
    for (int m = m_lo; m <= m_hi && now() < t_end && fails < 8; m++) {
        double slice = (t_end - now()) / 4;
        if (slice > 4.0) slice = 4.0;
        if (slice < 1.0) slice = 1.0;
        double until = now() + slice;
        if (until > t_end) until = t_end;
        int ok = 0;
        while (!ok && now() < until) {
            int a, b, r;
            random_group(m, &a, &b, &r);
            build_group(a, b, r);
            if (sa_cover(S, m, d, until, 400000)) {
                ok = 1;
                bestm = m;
                ba = a;
                bb = b;
                br = r;
                memcpy(bestS, S, sizeof(int) * d);
            }
        }
        if (ok) fails = 0;
        else fails++;
    }

    if (!bestm) {
        printf("0 0\n");
        return 0;
    }
    build_group(ba, bb, br);
    int m = bestm;
    printf("%d %d\n", 2 * m, m * d);
    for (int g = 0; g < m; g++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", g, m + MT[g][bestS[k]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (unchanged from the parent).
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Best directly constructible graph for D = 3: Moore graph or Araujo-Pardo/Lopez."""
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
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def _gq_w(q):
    """Incidence graph of W(q), the generalized quadrangle (diameter 4)."""
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


def starts(d, D, deadline, rng):
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    if D >= 3:
        out.extend(_arc_extensions(d, deadline, rng))
    if D >= 4 and d - 1 <= 6:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _run_haar(m_lo, d, D, seed, budget):
    text = lib.run_c(C_HAAR, [d, D, seed, f"{budget:.2f}", m_lo],
                     stdin_graph=None, timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    for g in starts(d, D, t0 + 0.12 * time_limit, rng):
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass
    if lib.is_valid(fallback[0], fallback[1], d, D):
        cands.append(fallback)
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    # Group-Haar difference-cover search, ascending from half the best start order.
    if D == 3 and d >= 2:
        remaining = hard_end - time.monotonic()
        if remaining > 2.0:
            try:
                n1, e1 = _run_haar(max(d, best[0] // 2), d, D, seed * 31 + 3, remaining - 1.0)
                if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                    best = (n1, e1)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
