"""Bipartite Cayley (Haar-type) search for degree-diameter graphs.

Each candidate is a group G of order N with a d-subset S, giving the bipartite graph on
G x {A, B} with a_x ~ b_{xs} for s in S. Left multiplication is an automorphism, so the
graph is valid iff every vertex is within distance D of a_1 and of b_1. The C engine runs
simulated annealing on S, with cost equal to the number of unreached vertices from those
two sources, and grows N one step at a time. Groups are Z_m x| Z_k, cyclic included.

For D = 3 the Python side first tries the projective-plane and Araujo-Pardo-Lopez
constructions and arc-extended planes, then runs the C search and keeps whichever graph
is larger. Every returned graph is checked with lib.is_valid, with K_{d,d} as the fallback.
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

#define MAXN 512
#define MAXD 32
#define SLICE 3.0

static int d, D, N, M, K, R;
static int rp[MAXN];
static int mt[MAXN][MAXN];
static int iv[MAXN];
static int vis[2 * MAXN];
static int vstamp = 0;
static int qu[2 * MAXN];
static int inS[MAXN];
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
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

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k+b, identity 0. */
static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    return (int)((a + (long)rp[b] * c) % M) * K + (b + e) % K;
}

static void set_group(int m, int k, int r) {
    M = m; K = k; R = r; N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) mt[x][y] = gmul(x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x][y] == 0) { iv[x] = y; break; }
}

/* Uniform random group of order n among cyclic and semidirect Z_m x| Z_k (reservoir sampling). */
static void random_group(int n, int *pm, int *pk, int *pr) {
    int cnt = 1;
    *pm = n; *pk = 1; *pr = 1;
    for (int k = 2; k <= n; k++) {
        if (n % k) continue;
        int m = n / k;
        if (m < 2) continue;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { *pm = m; *pk = k; *pr = r; }
        }
    }
}

/* Unreached-vertex count from a_1 and from b_1 within distance D. Zero iff the graph is valid. */
static int cost_of(const int *S) {
    int ivS[MAXD];
    for (int i = 0; i < d; i++) ivS[i] = iv[S[i]];
    int total = 0;
    for (int src = 0; src < 2; src++) {
        vstamp++;
        int start = src == 0 ? 0 : N;
        int head = 0, tail = 0, depth = 0;
        qu[tail++] = start;
        vis[start] = vstamp;
        while (head < tail && depth < D) {
            int end = tail;
            while (head < end) {
                int v = qu[head++];
                if (v < N) {
                    for (int i = 0; i < d; i++) {
                        int u = N + mt[v][S[i]];
                        if (vis[u] != vstamp) { vis[u] = vstamp; qu[tail++] = u; }
                    }
                } else {
                    int y = v - N;
                    for (int i = 0; i < d; i++) {
                        int u = mt[y][ivS[i]];
                        if (vis[u] != vstamp) { vis[u] = vstamp; qu[tail++] = u; }
                    }
                }
            }
            depth++;
        }
        total += 2 * N - tail;
    }
    return total;
}

static int anneal(double until, int *S) {
    for (int x = 0; x < N; x++) inS[x] = 0;
    for (int i = 0; i < d; i++) {
        int g;
        do g = rndint(N); while (inS[g]);
        S[i] = g;
        inS[g] = 1;
    }
    int cur = cost_of(S);
    long it = 0;
    const long L = 40000;
    for (;;) {
        if (cur == 0) return 1;
        if ((it & 63) == 0 && now() > until) return 0;
        double T = 1.5 * pow(0.02, (double)(it % L) / (double)L);
        it++;
        int i = rndint(d), g = rndint(N);
        if (inS[g]) continue;
        int old = S[i];
        S[i] = g;
        int c = cost_of(S);
        if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
            inS[old] = 0;
            inS[g] = 1;
            cur = c;
        } else {
            S[i] = old;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    /* Moore bound for the half-graph: sum_{i<D} (d-1)^i. */
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        if (s > MAXN) break;
        p *= (d - 1);
    }
    int Nmax = s < MAXN ? (int)s : MAXN;

    int bestN = 0, bm = 0, bk = 0, br = 0;
    int bestS[MAXD];
    int S[MAXD];
    int target = d;
    while (target <= Nmax && now() < t_end) {
        int m, k, r;
        random_group(target, &m, &k, &r);
        set_group(m, k, r);
        double until = now() + SLICE;
        if (until > t_end) until = t_end;
        if (anneal(until, S)) {
            bestN = target;
            bm = m; bk = k; br = r;
            memcpy(bestS, S, sizeof(int) * d);
            target++;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    set_group(bm, bk, br);
    printf("%d %d\n", 2 * bestN, bestN * d);
    for (int x = 0; x < bestN; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, bestN + mt[x][bestS[i]]);
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
    and a new B-vertex on the points of line P. Diameter 3."""
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
        if best[0] < lib.moore_bound(d, D):
            rng = random.Random(seed * 7919 + d)
            for cand in sorted(_arc_candidates(d, t0 + 0.1 * time_limit, rng), key=lambda t: -t[0]):
                consider(cand)

    # Bipartite Cayley search (any D >= 2). Skip it if the Moore bound is already reached.
    if best[0] < lib.moore_bound(d, D) and d >= 2:
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
        if budget > 0.5:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 timeout=budget + 3)
                n, e = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except (RuntimeError, ValueError):
                pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
