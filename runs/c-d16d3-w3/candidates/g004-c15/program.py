"""Bold change for the D = 3 targets: bi-Cayley (Haar-type) graphs from difference covers.

Construction: take a group G of order M and a d-subset S of G with S S^{-1} = G and
S^{-1} S = G. The bipartite graph with parts {a_g} and {b_g} and edges a_g ~ b_{g s}
(s in S) is d-regular on 2M vertices. Any two a's share a neighbour (since S S^{-1} = G),
any two b's share a neighbour (since S^{-1} S = G), and an a and a b are joined by a path
of length <= 3 (since S S^{-1} S covers G). So the diameter is at most 3, and the graph
is valid for every D >= 3.

Groups used: cyclic Z_M and semidirect products Z_a x|_r Z_b with a*b = M. The C engine
searches for S by simulated annealing, maximising the number of covered elements of
S S^{-1} and S^{-1} S. The Python side raises M upward from just above the parent's order
and keeps the largest M for which a cover is found. Every graph is checked with lib.is_valid.

Fallbacks: the parent's structured starts (projective planes, Araujo-Pardo/Lopez, arc
extensions, conic blow-ups, W(q) for D >= 4) and K_{d,d}. Any failure keeps the best valid
graph seen so far.
"""
import itertools
import math
import random
import time

import lib

C_COVER = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64

static int A, B, R, M, K;
static int RP[MAXM];
static int MT[MAXM][MAXM];
static int INV[MAXM];
static int S[MAXK];
static int inS[MAXM];
static int cntL[MAXM], cntR[MAXM];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Semidirect product Z_A x|_R Z_B, element (a, b) coded as a*B + b, identity 0. */
static int gmul(int x, int y) {
    int a1 = x / B, b1 = x % B, a2 = y / B, b2 = y % B;
    long t = ((long)a1 + (long)RP[b1] * a2) % A;
    return (int)(t * B + (b1 + b2) % B);
}

static int evaluate(void) {
    memset(cntL, 0, sizeof(int) * (size_t)M);
    memset(cntR, 0, sizeof(int) * (size_t)M);
    for (int i = 0; i < K; i++) {
        int si = S[i], ti = INV[si];
        for (int j = 0; j < K; j++) {
            int sj = S[j];
            cntL[MT[si][INV[sj]]]++;
            cntR[MT[ti][sj]]++;
        }
    }
    int c = 0;
    for (int g = 0; g < M; g++) {
        c += cntL[g] > 0;
        c += cntR[g] > 0;
    }
    return c;
}

static void output_found(void) {
    printf("FOUND\n");
    for (int i = 0; i < K; i++) printf("%d ", S[i]);
    printf("\n");
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("NONE\n");
        return 0;
    }
    A = atoi(argv[1]);
    B = atoi(argv[2]);
    R = atoi(argv[3]);
    K = atoi(argv[4]);
    unsigned long seed = strtoul(argv[5], NULL, 10);
    double budget = atof(argv[6]);
    if (A < 1 || B < 1 || (long)A * B > MAXM || K < 1 || K > MAXK) {
        printf("NONE\n");
        return 0;
    }
    M = A * B;
    if (K > M) {
        printf("NONE\n");
        return 0;
    }
    R %= A;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    RP[0] = 1 % A;
    for (int b = 1; b < B; b++) RP[b] = (int)((long)RP[b - 1] * R % A);
    if (B > 1 && ((long)RP[B - 1] * R % A) != (1 % A)) {
        printf("NONE\n");
        return 0;
    }
    for (int x = 0; x < M; x++)
        for (int y = 0; y < M; y++) MT[x][y] = gmul(x, y);
    for (int x = 0; x < M; x++) {
        INV[x] = -1;
        for (int y = 0; y < M; y++)
            if (MT[x][y] == 0) {
                INV[x] = y;
                break;
            }
        if (INV[x] < 0) {
            printf("NONE\n");
            return 0;
        }
    }

    double tend = now() + budget;
    const long ITERS = 40000;
    while (now() < tend) {
        memset(inS, 0, sizeof(int) * (size_t)M);
        for (int i = 0; i < K;) {
            int g = rndint(M);
            if (!inS[g]) {
                inS[g] = 1;
                S[i++] = g;
            }
        }
        int cur = evaluate();
        if (cur == 2 * M) {
            output_found();
            return 0;
        }
        for (long it = 0; it < ITERS; it++) {
            if ((it & 2047) == 0 && now() >= tend) break;
            double frac = (double)it / (double)ITERS;
            double T = 1.5 * pow(0.05, frac);
            int i = rndint(K);
            int x = rndint(M);
            if (inS[x]) continue;
            int old = S[i];
            inS[old] = 0;
            inS[x] = 1;
            S[i] = x;
            int nv = evaluate();
            if (nv >= cur || rnd01() < exp((nv - cur) / T)) {
                cur = nv;
                if (cur == 2 * M) {
                    output_found();
                    return 0;
                }
            } else {
                inS[x] = 0;
                inS[old] = 1;
                S[i] = old;
            }
        }
    }
    printf("NONE\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (carried over from the parent; all results are validated).
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
# Difference-cover (bi-Cayley) search.
# ----------------------------------------------------------------------------

def _mul(A, B, R, x, y):
    """Multiplication in Z_A x|_R Z_B with element (a, b) coded as a*B + b."""
    a1, b1 = divmod(x, B)
    a2, b2 = divmod(y, B)
    return ((a1 + pow(R, b1, A) * a2) % A) * B + (b1 + b2) % B


def _group_choices(M, rng):
    """Cyclic group of order M first, then up to two random semidirect products of order M."""
    cyc = (M, 1, 1)
    extra = []
    for a in range(2, M // 2 + 1):
        if M % a:
            continue
        b = M // a
        if b < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                extra.append((a, b, r))
    rng.shuffle(extra)
    return [cyc] + extra[:2]


def _cover_try(A, B, R, K, seed, budget, d, D):
    """Run the C search for one group; return (n, edges) for a valid Haar-type graph, or None."""
    text = lib.run_c(C_COVER, [A, B, R, K, seed, f"{budget:.2f}"], timeout=budget + 5.0)
    tok = text.split()
    if len(tok) < 1 + K or tok[0] != "FOUND":
        return None
    S = [int(t) for t in tok[1:1 + K]]
    if len(set(S)) != K:
        return None
    M = A * B
    edges = []
    for g in range(M):
        for s in S:
            edges.append((g, M + _mul(A, B, R, g, s)))
    n = 2 * M
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def _cover_search(d, D, lo, deadline, seed, rng):
    """Increase M from lo while covers are found; return the largest valid graph found, or None."""
    hi = d * d - d + 1  # a cover of size d covers at most d(d-1)+1 elements
    best = None
    M = lo
    while M <= hi:
        remaining = deadline - time.monotonic()
        if remaining < 0.8:
            break
        groups = _group_choices(M, rng)
        per = min(remaining, 8.0) / len(groups)
        got = None
        for (A, B, R) in groups:
            left = deadline - time.monotonic()
            if left < 0.3:
                break
            try:
                got = _cover_try(A, B, R, d, seed * 1000 + M, min(max(0.3, per), left), d, D)
            except Exception:
                got = None
            if got is not None:
                break
        if got is None:
            break
        best = got
        M += 1
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 72% of time_limit."""
    t0 = time.monotonic()
    end = t0 + 0.72 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    try:
        for g in starts(d, D, t0 + 0.12 * time_limit, rng):
            try:
                if lib.is_valid(g[0], g[1], d, D):
                    cands.append(g)
            except Exception:
                pass
    except Exception:
        pass
    if lib.is_valid(fallback[0], fallback[1], d, D):
        cands.append(fallback)
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    if D >= 3 and d >= 3:
        lo = best[0] // 2 + 1
        try:
            got = _cover_search(d, D, lo, end, seed, rng)
        except Exception:
            got = None
        if got is not None and got[0] > best[0] and lib.is_valid(got[0], got[1], d, D):
            best = got

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
