"""Bi-Cayley search over finite groups, with algebraic fallbacks.

Changed in this version: the old voltage-lift engine is replaced. For each target the program
builds a bipartite graph on two copies of a group G, A_x ~ B_{x*s} for s in a d-element set S.
Left multiplication by G is an automorphism, so the diameter test needs only two BFS runs, from
A_e and B_e. The C engine hill-climbs S over several non-abelian groups (AGL(2,3), GL(2,5),
PSL(2,8), and metacyclic semidirect products), in ascending order of order, so the largest group
that works is found. Every result is checked with lib.is_valid. The algebraic starts (PG(2,q),
the Araujo-Lopez graph, W(q), H(3)) remain the fallback, so every case returns a valid graph.
"""
import itertools
import math
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXN 1200

static int N, d, D, E;
static int *T, *INV, *vis, *qu;
static int stampc = 0;
static double t_end;
static int bad_input = 0;
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

static long readlong(void) {
    int c = getchar();
    while (c != EOF && (c < '0' || c > '9')) c = getchar();
    if (c == EOF) { bad_input = 1; return 0; }
    long x = 0;
    while (c >= '0' && c <= '9') {
        x = x * 10 + (c - '0');
        c = getchar();
    }
    return x;
}

static int in_prefix(const int *S, int cnt, int g) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == g) return 1;
    return 0;
}

/* Number of vertices (of the 2N) not reached from src within distance D. */
static int reach_bad_from(int src, const int *S, const int *IS) {
    int head = 0, tail = 0, level_end;
    stampc++;
    qu[tail++] = src;
    vis[src] = stampc;
    level_end = tail;
    for (int depth = 0; depth < D && head < tail; depth++) {
        while (head < level_end) {
            int v = qu[head++];
            if (v < N) {
                const int *row = T + (size_t)v * N;
                for (int i = 0; i < d; i++) {
                    int w = N + row[S[i]];
                    if (vis[w] != stampc) {
                        vis[w] = stampc;
                        qu[tail++] = w;
                    }
                }
            } else {
                const int *row = T + (size_t)(v - N) * N;
                for (int i = 0; i < d; i++) {
                    int w = row[IS[i]];
                    if (vis[w] != stampc) {
                        vis[w] = stampc;
                        qu[tail++] = w;
                    }
                }
            }
        }
        level_end = tail;
    }
    return 2 * N - tail;
}

/* Vertices A_x = x and B_y = N + y. A_x ~ B_{x s}, B_y ~ A_{y s^-1}. By transitivity,
 * BFS from A_E and B_E decides the diameter. */
static int bad_of(const int *S, const int *IS) {
    return reach_bad_from(E, S, IS) + reach_bad_from(N + E, S, IS);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    E = atoi(argv[5]);
    t_end = t0 + budget;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long n = readlong();
    long m = readlong();
    if (bad_input || n < 2 || n > MAXN || m != n * n || d < 1 || d > MAXD || D < 1 ||
        E < 0 || E >= n || n <= d) {
        printf("0 0\n");
        return 0;
    }
    N = (int)n;
    T = malloc(sizeof(int) * (size_t)N * (size_t)N);
    INV = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)(2 * N), sizeof(int));
    qu = malloc(sizeof(int) * (size_t)(2 * N));
    if (!T || !INV || !vis || !qu) {
        printf("0 0\n");
        return 0;
    }
    for (long e = 0; e < m; e++) {
        long u = readlong();
        long v = readlong();
        if (bad_input || u < 0 || u >= m || v < 0 || v >= N) {
            printf("0 0\n");
            return 0;
        }
        T[u] = (int)v;
    }
    for (int x = 0; x < N; x++) {
        int found = 0;
        for (int y = 0; y < N; y++)
            if (T[(size_t)x * N + y] == E) {
                INV[x] = y;
                found = 1;
                break;
            }
        if (!found) {
            printf("0 0\n");
            return 0;
        }
    }

    int S[MAXD], IS[MAXD], bestS[MAXD];
    int found = 0;
    while (!found && now() < t_end) {
        for (int i = 0; i < d; i++) {
            int g;
            do { g = rndint(N); } while (in_prefix(S, i, g));
            S[i] = g;
        }
        for (int i = 0; i < d; i++) IS[i] = INV[S[i]];
        int cur = bad_of(S, IS);
        for (int st = 0; st < 20000 && cur > 0; st++) {
            if ((st & 255) == 0 && now() >= t_end) break;
            int i = rndint(d);
            int g;
            do { g = rndint(N); } while (in_prefix(S, d, g));
            int old = S[i];
            S[i] = g;
            IS[i] = INV[g];
            int nb = bad_of(S, IS);
            if (nb <= cur || rnd01() < 0.01) {
                cur = nb;
            } else {
                S[i] = old;
                IS[i] = INV[old];
            }
        }
        if (cur == 0) {
            found = 1;
            memcpy(bestS, S, sizeof S);
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + T[(size_t)x * N + bestS[i]]);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _h3_lines(pts, index, s):
    """Lines of H(3) from Tits' description, with the right-hand sign multiplier s (1 or 2 mod 3)."""
    P = len(pts)

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1]
                + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % 3

    def norm(v):
        c = next(t for t in v if t)
        inv = 1 if c == 1 else 2
        return tuple((t * inv) % 3 for t in v)

    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            if bil(x, y):
                continue

            def pl(a, b):
                return (x[a] * y[b] - x[b] * y[a]) % 3

            conds = [(pl(1, 2), pl(3, 4)), (pl(5, 4), pl(3, 2)), (pl(2, 0), pl(3, 5)),
                     (pl(6, 5), pl(3, 0)), (pl(0, 1), pl(3, 6)), (pl(4, 6), pl(3, 1))]
            if any((a - s * b) % 3 for a, b in conds):
                continue
            L = set()
            for a in range(3):
                for b in range(3):
                    if a == 0 and b == 0:
                        continue
                    v = tuple((a * x[k] + b * y[k]) % 3 for k in range(7))
                    if any(v):
                        L.add(index[norm(v)])
            if len(L) == 4:
                lines.add(tuple(sorted(L)))
    return lines


def _hexagon_h3():
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, 4-regular, diameter 6.

    Returns (n, edges) or None. Accepted only if lib.is_valid confirms it.
    """
    pts = []
    for v in itertools.product(range(3), repeat=7):
        if not any(v):
            continue
        if v[next(i for i, c in enumerate(v) if c)] != 1:
            continue
        if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % 3:
            continue
        pts.append(v)
    P = len(pts)
    if P != 364:
        return None
    index = {v: i for i, v in enumerate(pts)}
    for s in (1, 2):
        lines = _h3_lines(pts, index, s)
        if len(lines) != P:
            continue
        lines = sorted(lines)
        edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
        if lib.is_valid(2 * P, edges, 4, 6):
            return 2 * P, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 7))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


# ------------------------------------------------------------- finite groups

def _mat_mul(p, M, K):
    a, b, c, e = M
    A, B, C, F = K
    return ((a * A + b * C) % p, (a * B + b * F) % p, (c * A + e * C) % p, (c * B + e * F) % p)


def _gl_mats(p):
    return [M for M in itertools.product(range(p), repeat=4) if (M[0] * M[3] - M[1] * M[2]) % p]


def _gl2_group(p):
    """GL(2,p) as (order, mul, identity index)."""
    mats = _gl_mats(p)
    idx = {M: i for i, M in enumerate(mats)}

    def mul(i, j):
        return idx[_mat_mul(p, mats[i], mats[j])]

    return len(mats), mul, idx[(1, 0, 0, 1)]


def _agl2_group(p):
    """AGL(2,p) = Z_p^2 x| GL(2,p) as (order, mul, identity index)."""
    mats = _gl_mats(p)
    elts = [(v, M) for v in itertools.product(range(p), repeat=2) for M in mats]
    idx = {g: i for i, g in enumerate(elts)}

    def mul(i, j):
        (v, M), (w, K) = elts[i], elts[j]
        Mw = ((M[0] * w[0] + M[1] * w[1]) % p, (M[2] * w[0] + M[3] * w[1]) % p)
        return idx[(((v[0] + Mw[0]) % p, (v[1] + Mw[1]) % p), _mat_mul(p, M, K))]

    return len(elts), mul, idx[((0, 0), (1, 0, 0, 1))]


def _psl28_group():
    """SL(2,8) = PSL(2,8), order 504, as (order, mul, identity index)."""
    F = lib.GF(8)
    fm = [[F.mul(a, b) for b in range(8)] for a in range(8)]
    fa = [[F.add(a, b) for b in range(8)] for a in range(8)]
    mats = []
    for M in itertools.product(range(8), repeat=4):
        a, b, c, e = M
        if fa[fm[a][e]][fm[b][c]] == 1 ^ 0 and F.sub(fm[a][e], fm[b][c]) == 1:
            mats.append(M)
    idx = {M: i for i, M in enumerate(mats)}

    def mul(i, j):
        a, b, c, e = mats[i]
        A, B, C, G = mats[j]
        prod = (fa[fm[a][A]][fm[b][C]], fa[fm[a][B]][fm[b][G]],
                fa[fm[c][A]][fm[e][C]], fa[fm[c][B]][fm[e][G]])
        return idx[prod]

    return len(mats), mul, idx[(1, 0, 0, 1)]


def _semi_maker(m, k, r):
    def make():
        N, mul, _inv = lib.semidirect_group(m, k, r)
        return N, mul, 0  # identity is element (0, 0)

    return make


def _semi_spec(N):
    """One non-abelian semidirect product Z_m x| Z_k of order N, or None."""
    triples = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                triples.append((m, k, r))
    if not triples:
        return None
    m, k, r = triples[len(triples) // 2]
    return (N, _semi_maker(m, k, r))


def _group_specs(lo, hi, d):
    """Candidate (order, maker) pairs with lo <= order <= hi, sorted by order."""
    specs = []
    for N, make in ((432, lambda: _agl2_group(3)),
                    (480, lambda: _gl2_group(5)),
                    (504, _psl28_group)):
        if lo <= N <= hi and N > d:
            specs.append((N, make))
    window = list(range(max(lo, d + 2), min(hi, lo + 200) + 1))
    step = max(1, len(window) // 12)
    for N in window[::step][:12]:
        spec = _semi_spec(N)
        if spec is not None:
            specs.append(spec)
    specs.sort(key=lambda t: t[0])
    return specs


def _table(N, mul):
    """Flat multiplication table as edges (x*N+y, x*y), for the C engine."""
    return [(x * N + y, mul(x, y)) for x in range(N) for y in range(N)]


def _bicayley_search(d, D, seed, best, moore, deadline):
    lo = best[0] // 2 + 1
    hi = min(moore // 2, 1200)
    specs = _group_specs(lo, hi, d)
    for idx, (N, make) in enumerate(specs):
        if 2 * N <= best[0]:
            continue
        left = deadline - time.monotonic()
        if left < 2.0:
            break
        slice_ = left / (len(specs) - idx)
        try:
            Nn, mul, e = make()
            edges = _table(Nn, mul)
            text = lib.run_c(C_SOURCE, [d, D, seed + idx, 0.85 * slice_, e],
                             stdin_graph=(Nn, edges), timeout=slice_ + 5)
            n, out = lib.parse_graph_text(text)
        except Exception:
            continue
        if n > best[0] and lib.is_valid(n, out, d, D):
            best = (n, out)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 4 and D >= 6:
        try:
            hexg = _hexagon_h3()
        except Exception:
            hexg = None
        if hexg is not None and hexg[0] > best[0] and lib.is_valid(hexg[0], hexg[1], d, D):
            best = hexg

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore or D < 2:
        return best

    deadline = t0 + 0.8 * time_limit
    try:
        cand_best = _bicayley_search(d, D, seed, best, moore, deadline)
        if cand_best[0] > best[0] and lib.is_valid(cand_best[0], cand_best[1], d, D):
            best = cand_best
    except Exception:
        pass
    return best
