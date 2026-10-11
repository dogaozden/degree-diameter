"""Diameter-3 search via bi-Cayley graphs over small groups, with structured starts as fallback.

Main new engine (D == 3): a bipartite graph on G x {0,1} with edges (g,0)-(g*s,1) for s in S,
|S| = d, |G| = m. If S*S^-1 = G then every pair on the same side is at distance <= 2 and
every cross pair at distance <= 3, so the graph is valid with 2m vertices and degree d.
The C engine searches groups G = Z_A x|_r Z_K of order m (m = A*K, r^K = 1 mod A) and
uses simulated annealing on the number of uncovered nonidentity group elements. It climbs
m upward from the best known order and keeps the largest success.

Fallbacks: the structured starts (projective planes, Araujo-Pardo/Lopez, conic blow-ups,
arc extensions, W(q) for D >= 4) and K_{d,d}. Every candidate is checked with lib.is_valid
before it is returned, so a failed engine only wastes time.
"""
import itertools
import random
import time

import lib

C_BICAY = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 512
#define MAXD 32
#define MAXC 8192
#define ITERS 1500000L

static int d;
static int M;
static int mul[MAXM][MAXM];
static int invt[MAXM];
static int S[MAXD];
static unsigned char inS[MAXM];
static int cnt[MAXM];
static int U;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
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

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Group Z_A x|_r Z_K, element x = a*K + b, (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2). Identity is 0. */
static void build_group(int A, int K, int r) {
    int rp[MAXM];
    M = A * K;
    rp[0] = 1 % A;
    for (int b = 1; b < K; b++) rp[b] = (int)((long)rp[b - 1] * r % A);
    for (int x = 0; x < M; x++) {
        int a1 = x / K, b1 = x % K;
        for (int y = 0; y < M; y++) {
            int a2 = y / K, b2 = y % K;
            mul[x][y] = (int)((((long)a1 + (long)rp[b1] * a2) % A) * K + (b1 + b2) % K);
        }
    }
    for (int x = 0; x < M; x++)
        for (int y = 0; y < M; y++)
            if (mul[x][y] == 0) { invt[x] = y; break; }
}

static void bump(int x, int dl) {
    if (x == 0) return;
    if (dl > 0) {
        if (cnt[x] == 0) U--;
        cnt[x]++;
    } else {
        cnt[x]--;
        if (cnt[x] == 0) U++;
    }
}

/* Add (dl=+1) or remove (dl=-1) all ordered quotients s t^-1 and t s^-1 for t in S[0..nf), t != S[skip]. */
static void touch(int s, int skip, int dl, int nf) {
    for (int j = 0; j < nf; j++) {
        if (j == skip) continue;
        int t = S[j];
        bump(mul[s][invt[t]], dl);
        bump(mul[t][invt[s]], dl);
    }
}

static int sa_run(long iters, double T0, double T1, double until) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(inS, 0, (size_t)M);
    U = M - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int k = 1; k < d; k++) {
        int g;
        do g = 1 + rndint(M - 1); while (inS[g]);
        S[k] = g;
        inS[g] = 1;
        touch(g, k, 1, k);
    }
    if (U == 0) return 1;
    double lr = log(T1 / T0);
    double T = T0;
    for (long it = 0; it < iters; it++) {
        if ((it & 1023) == 0) {
            if (now() > until) return 0;
            T = T0 * exp(lr * (double)it / (double)iters);
        }
        int i = 1 + rndint(d - 1);
        int old = S[i];
        int g;
        do g = rndint(M); while (inS[g]);
        int U0 = U;
        touch(old, i, -1, d);
        inS[old] = 0;
        S[i] = g;
        inS[g] = 1;
        touch(g, i, 1, d);
        int dU = U - U0;
        if (dU > 0 && rnd01() >= exp(-(double)dU / T)) {
            touch(g, i, -1, d);
            inS[g] = 0;
            S[i] = old;
            inS[old] = 1;
            touch(old, i, 1, d);
        }
        if (U == 0) return 1;
    }
    return 0;
}

static int collect(int m, int *cA, int *cK, int *cR) {
    int nc = 0;
    for (int K = 1; K <= m; K++) {
        if (m % K) continue;
        int A = m / K;
        if (A == 1) {
            if (nc < MAXC) { cA[nc] = 1; cK[nc] = K; cR[nc] = 0; nc++; }
            continue;
        }
        for (int r = 1; r < A; r++) {
            if (gcdi(r, A) != 1) continue;
            if (powmod(r, K, A) != 1 % A) continue;
            if (nc < MAXC) { cA[nc] = A; cK[nc] = K; cR[nc] = r; nc++; }
        }
    }
    return nc;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    int lo = atoi(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    if (d < 3 || d > MAXD) { printf("0 0\n"); return 0; }

    int Mmax = d * (d - 1) + 1;
    if (Mmax > MAXM) Mmax = MAXM;
    int cur = lo < d + 1 ? d + 1 : lo;
    double t_end = now() + budget;
    int bestM = 0, bestS[MAXD], bA = 0, bK = 0, bR = 0;
    static int cA[MAXC], cK[MAXC], cR[MAXC];
    const double T0s[3] = {0.5, 0.8, 1.2};

    while (cur <= Mmax && now() < t_end) {
        int hit = 0;
        for (int m = cur; m < cur + 3 && m <= Mmax && now() < t_end && !hit; m++) {
            int nc = collect(m, cA, cK, cR);
            if (nc == 0) continue;
            int c = rndint(nc);
            int A = cA[c], K = cK[c], R = cR[c];
            build_group(A, K, R);
            double T0 = T0s[rndint(3)];
            if (sa_run(ITERS, T0, 0.08, t_end)) {
                bestM = m;
                memcpy(bestS, S, sizeof(S));
                bA = A; bK = K; bR = R;
                cur = m + 1;
                hit = 1;
            }
        }
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    build_group(bA, bK, bR);
    printf("%d %d\n", 2 * M, M * d);
    for (int g = 0; g < M; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, M + mul[g][bestS[j]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts.
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
# C engine driver.
# ----------------------------------------------------------------------------

def _run_bicayley(d, seed, budget, lo):
    text = lib.run_c(C_BICAY, [d, seed, f"{budget:.2f}", lo], timeout=budget + 5.0)
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
    for g in starts(d, D, t0 + 0.10 * time_limit, rng):
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

    # Bi-Cayley search for D = 3: groups of order m, 2m vertices, degree d.
    if D == 3 and 3 <= d <= 30:
        lo = best[0] // 2 + 1
        remaining = hard_end - time.monotonic()
        budget = remaining - 1.5
        if budget > 3.0 and lo <= d * (d - 1) + 1:
            try:
                n1, e1 = _run_bicayley(d, seed * 31 + 5, budget, lo)
                if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                    best = (n1, e1)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
