"""Diameter-3 search with a difference-cover (Haar-graph) construction, plus cheap structured starts.

Main idea for D = 3:
  The bipartite Haar graph H(G, S) has parts A = G and B = G, with a_x ~ b_{xs} for s in S, |S| = d.
  It has diameter <= 3 exactly when S S^{-1} = G and S^{-1} S = G (the cross condition then follows).
  So the task is to find a group G of order N with |S| = d and S S^{-1} = S^{-1} S = G. That gives a
  d-regular bipartite graph on 2N vertices. Since |S S^{-1}| <= d(d-1)+1, we have N <= d(d-1)+1, and
  the record 394 for d = 16 corresponds to N = 197. The C engine searches orders N upward from the best
  structured start, over cyclic groups and semidirect products Z_m x| Z_k. For each group it runs
  simulated annealing on S, with 0 fixed in S (WLOG, since right translation preserves both conditions).

Structured starts (validated with lib.is_valid): PG(2,q) incidence, Araujo-Pardo/Lopez graphs,
conic blow-ups, arc-extended PG(2,q) incidence graphs, and W(q) for D >= 4. K_{d,d} is the
always-valid fallback.

Scope: the Haar search is used only for D = 3. Other D values get the structured starts and K_{d,d}
only. Every returned graph is checked with lib.is_valid, and any failure falls back to the best valid start.
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

#define MAXN 1024
#define MAXDESC 8192
#define MAXD 64

typedef struct { int type, m, k, r; } Desc;

static int MULT[MAXN][MAXN];
static int INV[MAXN];
static int rp[MAXN];
static int N, d;
static Desc descs[MAXDESC];
static int ndesc;
static int S[MAXD];
static int inS[MAXN];
static int stA[MAXN], stB[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

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

/* Group of order m (type 0: cyclic Z_m) or Z_m x|_r Z_k (type 1, element code a*k+b). */
static void build_group(Desc g) {
    if (g.type == 0) {
        N = g.m;
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++) {
                int s = x + y;
                if (s >= N) s -= N;
                MULT[x][y] = s;
            }
    } else {
        int m = g.m, k = g.k;
        N = m * k;
        rp[0] = 1 % m;
        for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * g.r % m);
        for (int x = 0; x < N; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < N; y++) {
                int c = y / k, e = y % k;
                MULT[x][y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
            }
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MULT[x][y] == 0) { INV[x] = y; break; }
    }
}

static void enum_descs(int n) {
    ndesc = 0;
    descs[ndesc].type = 0; descs[ndesc].m = n; descs[ndesc].k = 1; descs[ndesc].r = 0;
    ndesc++;
    for (int m = 2; m <= n / 2; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            if (ndesc < MAXDESC) {
                descs[ndesc].type = 1;
                descs[ndesc].m = m;
                descs[ndesc].k = k;
                descs[ndesc].r = r;
                ndesc++;
            }
        }
    }
}

/* Uncovered elements of S S^{-1} plus uncovered elements of S^{-1} S. Zero means valid. */
static int cost_now(void) {
    int cA = 0, cB = 0;
    stamp++;
    for (int i = 0; i < d; i++) {
        int si = S[i], ii = INV[si];
        for (int j = 0; j < d; j++) {
            int g = MULT[si][INV[S[j]]];
            if (stA[g] != stamp) { stA[g] = stamp; cA++; }
            int h = MULT[ii][S[j]];
            if (stB[h] != stamp) { stB[h] = stamp; cB++; }
        }
    }
    return (N - cA) + (N - cB);
}

static int sa_attempt(long steps) {
    for (int x = 0; x < N; x++) inS[x] = 0;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int g;
        do { g = rndint(N); } while (inS[g]);
        S[i] = g;
        inS[g] = 1;
    }
    int cur = cost_now();
    if (cur == 0) return 1;
    double T = 1.5;
    double fac = pow(0.08 / 1.5, 1.0 / (double)steps);
    for (long s = 0; s < steps; s++) {
        int i = 1 + rndint(d - 1);
        int g = rndint(N);
        if (inS[g]) { T *= fac; continue; }
        int old = S[i];
        S[i] = g;
        int nc = cost_now();
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[g] = 1;
            cur = nc;
            if (cur == 0) return 1;
        } else {
            S[i] = old;
        }
        T *= fac;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    int lo = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD) { printf("0 0\n"); return 0; }
    int hi = d * (d - 1) + 1;
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo < d) lo = d;

    double tend = now() + budget;
    int bestN = 0;
    Desc bestG;
    int bestS[MAXD];
    memset(&bestG, 0, sizeof(bestG));

    for (int n = lo; n <= hi; n++) {
        double rem = tend - now();
        if (rem <= 0) break;
        double slice = rem / (double)(hi - n + 1);
        double send = now() + slice;
        enum_descs(n);
        int found = 0;
        while (now() < send && !found) {
            Desc g = descs[rndint(ndesc)];
            build_group(g);
            if (sa_attempt(60000)) {
                found = 1;
                bestN = n;
                bestG = g;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    build_group(bestG);
    memcpy(S, bestS, sizeof(int) * (size_t)d);
    int n = bestN;
    printf("%d %d\n", 2 * n, n * d);
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, n + MULT[x][S[i]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts.
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Best directly constructible graph for D = 3: projective plane or Araujo-Pardo/Lopez."""
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
# Difference-cover search driver.
# ----------------------------------------------------------------------------

def haar_cover_search(d, lo, seed, budget):
    """Run the C search for a bipartite Haar graph of order 2N with N >= lo and |S| = d."""
    text = lib.run_c(C_HAAR, [d, lo, seed, f"{budget:.2f}"],
                     stdin_graph=None, timeout=budget + 15.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    rng = random.Random(seed * 7919 + d)

    cands = [fallback]
    try:
        cands.extend(starts(d, D, t0 + 0.12 * time_limit, rng))
    except Exception:
        pass
    valid = []
    for g in cands:
        try:
            if lib.is_valid(g[0], g[1], d, D):
                valid.append(g)
        except Exception:
            pass
    if not valid:
        return fallback
    best = max(valid, key=lambda g: g[0])

    if D == 3 and d >= 3:
        lo = best[0] // 2 + 1
        hi = d * (d - 1) + 1
        if lo <= hi:
            elapsed = time.monotonic() - t0
            left = 0.85 * time_limit - elapsed - 2.0
            budget = min(left, 0.75 * time_limit)
            if budget > 3.0:
                try:
                    n1, e1 = haar_cover_search(d, lo, seed * 131 + 7, budget)
                    if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                        best = (n1, e1)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
