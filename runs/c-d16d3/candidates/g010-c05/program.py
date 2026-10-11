"""Cyclic Haar-graph search for D = 3, plus the earlier projective-plane constructions as fallbacks.

For bipartite D = 3, the Haar graph of Z_N with connection set S (|S| = d) is valid iff
  (a) S - S covers every nonzero residue (same-side pairs at distance 2), and
  (b) S - S + S covers every residue, including 0 (opposite-side pairs at distance <= 3).
It is d-regular on 2N vertices, so the search maximises N. The C engine runs simulated
annealing over the sets S, with a binary search over N and then climbing from the best N.
Projective-plane and arc-extended constructions are kept as safe fallbacks.
"""
import random
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 64
#define MAXN 1024

static int K, Dg, N;
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

static int S[MAXK];
static int bestS[MAXK];
static int cnt[MAXN];
static int cost;

static inline int md(int x) {
    x %= N;
    if (x < 0) x += N;
    return x;
}
static inline void dec(int r) { if (--cnt[r] == 0) cost++; }
static inline void inc(int r) { if (cnt[r]++ == 0) cost--; }

/* Add or remove element x against every other element of S (index skip is ignored). */
static void touch(int x, int skip, int add) {
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        int r1 = md(x - S[j]), r2 = md(S[j] - x);
        if (add) { inc(r1); inc(r2); }
        else { dec(r1); dec(r2); }
    }
}

static void init_random(void) {
    memset(cnt, 0, sizeof(int) * N);
    cost = N - 1;   /* residues 1..N-1 all uncovered */
    int k = 0;
    while (k < K) {
        int y = rndint(N), ok = 1;
        for (int j = 0; j < k; j++) if (S[j] == y) { ok = 0; break; }
        if (ok) S[k++] = y;
    }
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            inc(md(S[i] - S[j]));
            inc(md(S[j] - S[i]));
        }
}

static int triple_ok(void) {
    static unsigned char mark[MAXN];
    memset(mark, 0, (size_t)N);
    for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++)
            for (int c = 0; c < K; c++)
                mark[md(S[a] - S[b] + S[c])] = 1;
    for (int r = 0; r < N; r++) if (!mark[r]) return 0;
    return 1;
}

static int attempt(double until) {
    init_random();
    double T = 0.4;
    long it = 0;
    for (;;) {
        ++it;
        if ((it & 4095) == 0 && now() > until) return 0;
        if (cost == 0 && triple_ok()) return 1;
        if (it % 400000 == 0) init_random();
        int i = rndint(K), y = rndint(N), dup = 0;
        for (int j = 0; j < K; j++) if (S[j] == y) { dup = 1; break; }
        if (dup) continue;
        int x = S[i], c0 = cost;
        touch(x, i, 0);
        S[i] = y;
        touch(y, i, 1);
        int c1 = cost;
        if (!(c1 <= c0 || rnd01() < exp((double)(c0 - c1) / T))) {
            touch(y, i, 0);
            S[i] = x;
            touch(x, i, 1);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    K = atoi(argv[1]);
    Dg = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (Dg != 3 || K < 2 || K > MAXK) { printf("0 0\n"); return 0; }
    int Nmax = K * (K - 1) + 1;
    if (Nmax > MAXN - 1) Nmax = MAXN - 1;

    int best_N = 0;
    int lo = K, hi = Nmax;
    while (lo <= hi && now() < t_end) {
        int mid = (lo + hi) / 2;
        N = mid;
        double slice = (t_end - now()) * 0.12;
        if (slice < 0.2) slice = 0.2;
        double until = now() + slice;
        if (until > t_end) until = t_end;
        if (attempt(until)) {
            best_N = mid;
            memcpy(bestS, S, sizeof(int) * K);
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }
    while (now() < t_end && best_N + 1 <= Nmax) {
        N = best_N + 1;
        double slice = (t_end - now()) * 0.5;
        if (attempt(now() + slice)) {
            best_N = N;
            memcpy(bestS, S, sizeof(int) * K);
        } else {
            break;
        }
    }

    if (best_N == 0) { printf("0 0\n"); return 0; }
    N = best_N;
    memcpy(S, bestS, sizeof(int) * K);
    long m = (long)N * K;
    printf("%d %ld\n", 2 * N, m);
    for (int i = 0; i < N; i++)
        for (int j = 0; j < K; j++)
            printf("%d %d\n", i, N + md(i + S[j]));
    return 0;
}
'''


def _pg_data(q):
    """Points/lines of PG(2, q): point i and line i share the vector pts[i]."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG(2,q) incidence plus, per element P of S, a new A-vertex on the lines through P
    and a new B-vertex on the points of line P. Diameter 3, max degree q+1+s."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D == 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.10 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

        # Bold branch: cyclic Haar graphs (difference covers), searched in C.
        budget = 0.75 * time_limit - (time.monotonic() - t0) - 1.0
        if budget > 0.5:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 5)
                n, e = lib.parse_graph_text(text)
                consider((n, e))
            except (RuntimeError, ValueError):
                pass   # keep the best construction found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
