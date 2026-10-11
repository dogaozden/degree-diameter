import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold alternative for D = 4: bi-Cayley graphs over semidirect products.
#
# Vertices: L(i, x) = i*N + x and R(j, y) = 2N + j*N + y, for i, j in {0, 1} and
# x, y in G, where G = Z_m x| Z_k has order N = m*k. Edges: L(i, x) ~ R(j, x*s)
# for s in S[i][j]. The sizes are |S00| = |S11| = A and |S01| = |S10| = d - A,
# so the graph is d-regular and bipartite. Left multiplication by G is an
# automorphism, so diameter <= D only needs BFS from one representative per
# orbit (4 sources). Simulated annealing swaps set elements to minimise the
# number of unreached (source, vertex) pairs. This is a different search space
# from the previous annealer, which works on general graphs.
# ----------------------------------------------------------------------------

BICAY_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1100
#define VMAX (4 * NMAX)
#define DM 16

static int M, K, R, N, D, DEG, A;
static int PW[NMAX];
static int *MT;
static int INV[NMAX];
static int S[2][2][DM];
static int sz[2][2];
static unsigned char mem[2][2][NMAX];
static int dist[VMAX], Q[VMAX];
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

static int mulg(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    return ((a + PW[b] * c) % M) * K + (b + e) % K;
}

static int reach_count(int src) {
    int V = 4 * N;
    for (int v = 0; v < V; v++) dist[v] = -1;
    int h = 0, t = 0, cnt = 1;
    dist[src] = 0;
    Q[t++] = src;
    while (h < t) {
        int v = Q[h++];
        int dv = dist[v];
        if (dv >= D) continue;
        if (v < 2 * N) {
            int i = v / N, x = v % N;
            for (int j = 0; j < 2; j++)
                for (int k = 0; k < sz[i][j]; k++) {
                    int w = 2 * N + j * N + MT[x * N + S[i][j][k]];
                    if (dist[w] < 0) {
                        dist[w] = dv + 1;
                        Q[t++] = w;
                        cnt++;
                    }
                }
        } else {
            int u = v - 2 * N;
            int j = u / N, y = u % N;
            for (int i = 0; i < 2; i++)
                for (int k = 0; k < sz[i][j]; k++) {
                    int w = i * N + MT[y * N + INV[S[i][j][k]]];
                    if (dist[w] < 0) {
                        dist[w] = dv + 1;
                        Q[t++] = w;
                        cnt++;
                    }
                }
        }
    }
    return cnt;
}

static int cost(void) {
    int c = 0;
    int srcs[4] = {0, N, 2 * N, 3 * N};
    for (int s = 0; s < 4; s++) c += 4 * N - reach_count(srcs[s]);
    return c;
}

static void random_fill(void) {
    memset(mem, 0, sizeof mem);
    int want[2][2] = {{A, DEG - A}, {DEG - A, A}};
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++) {
            sz[i][j] = want[i][j];
            for (int k = 0; k < sz[i][j]; k++) {
                int e;
                do { e = rnd(N); } while (mem[i][j][e]);
                S[i][j][k] = e;
                mem[i][j][e] = 1;
            }
        }
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    M = atoi(argv[1]);
    K = atoi(argv[2]);
    R = atoi(argv[3]);
    A = atoi(argv[4]);
    DEG = atoi(argv[5]);
    D = atoi(argv[6]);
    rs = strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[8]);
    for (int i = 0; i < 20; i++) nextr();
    N = M * K;
    if (N < 2 || N > NMAX || DEG < 2 || DEG > DM || A < 1 || A >= DEG || D < 1 || DEG > N || M < 1 || K < 1) {
        printf("0\n");
        return 0;
    }
    MT = (int *)malloc(sizeof(int) * (size_t)N * (size_t)N);
    if (!MT) { printf("0\n"); return 0; }
    PW[0] = 1 % M;
    for (int b = 1; b < K; b++) PW[b] = (int)((long long)PW[b - 1] * R % M);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = mulg(x, y);
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
    }

    random_fill();
    int c = cost();
    int found = (c == 0);
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    while (!found) {
        double fr = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
        if (fr >= 1.0) break;
        double T = 2.0 * (1.0 - fr) + 0.1;
        int i = rnd(2), j = rnd(2);
        if (sz[i][j] == 0) continue;
        int k = rnd(sz[i][j]);
        int e = rnd(N);
        if (mem[i][j][e]) continue;
        int old = S[i][j][k];
        mem[i][j][old] = 0;
        S[i][j][k] = e;
        mem[i][j][e] = 1;
        int c2 = cost();
        int dl = c2 - c;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            c = c2;
            if (c == 0) found = 1;
        } else {
            mem[i][j][e] = 0;
            S[i][j][k] = old;
            mem[i][j][old] = 1;
        }
    }

    if (!found) {
        printf("0\n");
    } else {
        printf("1\n");
        for (int i = 0; i < 2; i++)
            for (int j = 0; j < 2; j++) {
                printf("%d", sz[i][j]);
                for (int k = 0; k < sz[i][j]; k++) printf(" %d", S[i][j][k]);
                printf("\n");
            }
    }
    free(MT);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q + 1, diameter 4, order 2(q+1)(q^2+1)."""
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
    """W(q) for the largest prime power q <= d - 1 with q <= 16."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate(n, half, edges, d, rng):
    """Greedily join deficient vertices on opposite sides (side 0 = [0, half), side 1 = [half, n))."""
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    left = [v for v in range(half) if deg[v] < d]
    right = [v for v in range(half, n) if deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (a, b) not in existing]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


def _bicay_cands(N, rng):
    """Semidirect groups Z_m x| Z_k of order N (cyclic included), shuffled."""
    cands = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            cands.append((N, 1, 1))
        elif m >= 2:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(rs)
            cands += [(m, k, r) for r in rs[:3]]
    rng.shuffle(cands)
    return cands


def _parse_bicay(out):
    """Parse the C output into {(i, j): element list} or None if no graph was found."""
    t = out.split()
    if not t or t[0] != "1":
        return None
    pos = 1
    S = {}
    for ij in ((0, 0), (0, 1), (1, 0), (1, 1)):
        s = int(t[pos])
        pos += 1
        S[ij] = [int(x) for x in t[pos:pos + s]]
        pos += s
    return S


def _bicay_graph(m, k, r, S):
    """Build the bi-Cayley graph: L(i, x) ~ R(j, x*s) for s in S[(i, j)]."""
    N, mul, _ = lib.semidirect_group(m, k, r)
    edges = []
    for (i, j), els in S.items():
        for s in els:
            for x in range(N):
                edges.append((i * N + x, 2 * N + j * N + mul(x, s)))
    return 4 * N, edges


def _bicay_search(d, D, fb_n, deadline, rng):
    """Ascending search over group orders N for a valid bi-Cayley graph on 4N vertices."""
    best = None
    N = max(2, fb_n // 4 + 1)
    Nhi = min(lib.moore_bound(d, D) // 4, 1100)
    errs = 0
    while N <= Nhi:
        got = False
        for (m, k, r) in _bicay_cands(N, rng)[:8]:
            left = deadline - time.monotonic()
            if left < 1.0:
                return best
            budget = min(5.0, left - 0.5)
            a = rng.randint(1, d - 1)
            seed = rng.randrange(1 << 30)
            try:
                out = lib.run_c(BICAY_SOURCE, [m, k, r, a, d, D, seed, f"{budget:.2f}"],
                                timeout=budget + 4.0)
                S = _parse_bicay(out)
                if S is not None:
                    n, e = _bicay_graph(m, k, r, S)
                    if lib.is_valid(n, e, d, D):
                        best = (n, e)
                        got = True
                        break
            except Exception:
                errs += 1
                if errs >= 3:
                    return best
        if got:
            N += 1
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
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            consider(*lib.projective_plane_incidence(qs[0]))

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            half = gq[0] // 2
            consider(gq[0], _saturate(gq[0], half, gq[1], d, rng))

    # Main bold path for D = 4: bi-Cayley search, using most of the budget.
    if D == 4 and 4 <= d <= 16:
        bi_deadline = start + 0.88 * tl - 1.0
        res = _bicay_search(d, D, best_n, bi_deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
