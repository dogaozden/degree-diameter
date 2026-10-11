"""Bi-Cayley graphs over explicit non-cyclic groups, searched in C.

Bold change: instead of voltage lifts with Z_m x| Z_k voltages, this version builds a bi-Cayley
graph over an explicit group G with a multiplication table. Vertices are A_g and B_h for g, h in G,
and A_g is joined to B_{g s} for each s in a connection set S of size d. Left multiplication is an
automorphism that acts transitively on each side, so the diameter is <= D iff BFS of depth D from
A_e and from B_e reaches everything. Each cost evaluation is therefore two BFS runs.

Groups come from: explicit non-abelian groups (S4, A5, S5, SL(2,3), GL(2,3), SL(2,5), SL(2,7)),
direct products of those with cyclic groups, semidirect products Z_m x| Z_k, and cyclic groups.
The C engine anneals over S for each group in turn. Every result is re-checked with lib.is_valid,
and the best known construction is kept as a fallback, so every case returns a valid graph.
Risk: this family may not reach the parent's 352 for d=5, D=5, so the result may fall back to
the simpler constructions.
"""
import math
import random
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley search. Input (stdin): "N m" with m = N*N, then m lines "u v" where
 * u = T[k / N][k % N] is the group multiplication table (identity index 0), v is ignored.
 * Args: d D seed time_limit.
 * Graph: A_g = g, B_h = N + h, A_g ~ B_{g*s} for s in S (|S| = d).
 * Cost: vertices unreached within D from A_0 plus from B_0 (zero => diameter <= D).
 * Output: "OK s_1 ... s_d" on success, otherwise "NONE".
 */

#define MAXG 512
#define MAXD 16

static int N, d, D;
static int T[MAXG][MAXG];
static int INV[MAXG];
static int S[MAXD];
static int VIS[2 * MAXG];
static int QU[2 * MAXG];
static int stamp = 0;
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

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

static long cost_of(void) {
    long total = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        stamp++;
        int head = 0, tail = 0;
        QU[tail++] = s0;
        VIS[s0] = stamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = QU[head++];
                if (v < N) {
                    for (int i = 0; i < d; i++) {
                        int u = N + T[v][S[i]];
                        if (VIS[u] != stamp) {
                            VIS[u] = stamp;
                            QU[tail++] = u;
                        }
                    }
                } else {
                    int h = v - N;
                    for (int i = 0; i < d; i++) {
                        int u = T[h][INV[S[i]]];
                        if (VIS[u] != stamp) {
                            VIS[u] = stamp;
                            QU[tail++] = u;
                        }
                    }
                }
            }
        }
        total += 2L * N - tail;
    }
    return total;
}

static int read_table(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXG || m != n * n) return 0;
    N = n;
    for (int k = 0; k < m; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= N) return 0;
        T[k / N][k % N] = u;
    }
    for (int i = 0; i < N; i++) {
        if (T[0][i] != i || T[i][0] != i) return 0;
    }
    for (int i = 0; i < N; i++) {
        int found = 0;
        for (int j = 0; j < N; j++) {
            if (T[i][j] == 0) {
                INV[i] = j;
                found = 1;
                break;
            }
        }
        if (!found) return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("NONE\n");
        return 0;
    }
    if (!read_table() || N < d) {
        printf("NONE\n");
        return 0;
    }

    while (now() < t_end) {
        for (int i = 0; i < d; i++) {
            int x;
            do {
                x = rndint(N);
            } while (in_S(x, i));
            S[i] = x;
        }
        long cost = cost_of();
        long steps = 6000;
        for (long s = 0; s < steps && cost > 0; s++) {
            if ((s & 127) == 0 && now() > t_end) break;
            double Tm = 1.0 * (1.0 - (double)s / (double)steps) + 0.03;
            int i = rndint(d);
            int old = S[i];
            int nv = rndint(N);
            if (in_S(nv, d)) continue;
            S[i] = nv;
            long c2 = cost_of();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tm)) {
                cost = c2;
            } else {
                S[i] = old;
            }
        }
        if (cost == 0) {
            printf("OK");
            for (int i = 0; i < d; i++) printf(" %d", S[i]);
            printf("\n");
            return 0;
        }
    }
    printf("NONE\n");
    return 0;
}
'''

MAX_GROUP = 512

# Explicit base groups: ("perm", generators) or ("mat", p, generators) for matrices mod p.
_BASE_SPECS = {
    "S4": ("perm", [(1, 0, 2, 3), (1, 2, 3, 0)]),
    "A5": ("perm", [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]),
    "S5": ("perm", [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)]),
    "SL23": ("mat", 3, [(1, 1, 0, 1), (0, 2, 1, 0)]),
    "GL23": ("mat", 3, [(1, 1, 0, 1), (0, 2, 1, 0), (1, 0, 0, 2)]),
    "SL25": ("mat", 5, [(1, 1, 0, 1), (0, 4, 1, 0)]),
    "SL27": ("mat", 7, [(1, 1, 0, 1), (0, 6, 1, 0)]),
}

_BASE_CACHE = {}


def _closure(gens, mul, ident, cap):
    """Elements of the group generated by gens (identity first), or None if more than cap."""
    index = {ident: 0}
    elems = [ident]
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in index:
                    if len(elems) >= cap:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems, index


def _mat_mul(p):
    def mul(x, y):
        a, b, c, e = x
        f, g, h, k = y
        return ((a * f + b * h) % p, (a * g + b * k) % p,
                (c * f + e * h) % p, (c * g + e * k) % p)
    return mul


def _base_table(name):
    """(order, multiplication table with identity at index 0) for a named base group, or None."""
    if name in _BASE_CACHE:
        return _BASE_CACHE[name]
    spec = _BASE_SPECS[name]
    if spec[0] == "perm":
        gens = spec[1]
        k = len(gens[0])
        ident = tuple(range(k))

        def mul(x, y):
            return tuple(x[i] for i in y)
    else:
        p, gens = spec[1], spec[2]
        ident = (1, 0, 0, 1)
        mul = _mat_mul(p)
    res = _closure(gens, mul, ident, MAX_GROUP)
    if res is None:
        out = None
    else:
        elems, index = res
        T = [[index[mul(a, b)] for b in elems] for a in elems]
        out = (len(elems), T)
    _BASE_CACHE[name] = out
    return out


def _product_table(H, k):
    """Direct product of the group H (order n, table TH) with the cyclic group Z_k."""
    n, TH = H
    N = n * k
    T = [[0] * N for _ in range(N)]
    for h1 in range(n):
        for c1 in range(k):
            row = T[h1 * k + c1]
            TH1 = TH[h1]
            for h2 in range(n):
                for c2 in range(k):
                    row[h2 * k + c2] = TH1[h2] * k + (c1 + c2) % k
    return N, T


def _make_table(spec):
    """Build the multiplication table (order, T) for a candidate spec."""
    N, kind, params = spec
    if kind == "base":
        return _base_table(params[0])
    if kind == "prod":
        name, k = params
        H = _base_table(name)
        if H is None:
            return None
        return _product_table(H, k)
    if kind == "semi":
        m, k, r = params
        order, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(i, j) for j in range(order)] for i in range(order)]
        return order, T
    # cyclic
    T = [[(i + j) % N for j in range(N)] for i in range(N)]
    return N, T


def _search_bi_cayley(d, D, best, seed, t0, time_limit):
    moore = lib.moore_bound(d, D)
    hi = min(moore // 2, MAX_GROUP)
    lo = max(best[0] // 2 + 1, moore // 4, d)
    if lo > hi:
        return best
    rng = random.Random(seed)

    base_specs = []
    for name in _BASE_SPECS:
        tab = _base_table(name)
        if tab is None:
            continue
        nb = tab[0]
        if lo <= nb <= hi:
            base_specs.append((nb, "base", (name,)))
        for k in range(2, hi // nb + 1):
            if lo <= nb * k <= hi:
                base_specs.append((nb * k, "prod", (name, k)))
    base_specs.sort(key=lambda s: s[0])

    semi = []
    for N in range(lo, hi + 1):
        for m in range(2, N // 2 + 1):
            if N % m:
                continue
            k = N // m
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            for r in rng.sample(rs, min(2, len(rs))):
                semi.append((N, "semi", (m, k, r)))
    rng.shuffle(semi)
    cyc = [(N, "cyc", ()) for N in range(lo, hi + 1)]
    specs = base_specs + semi[:80] + cyc

    deadline = t0 + 0.9 * time_limit - 1.0
    for idx, spec in enumerate(specs):
        N = spec[0]
        if 2 * N <= best[0]:
            continue
        rem = deadline - time.monotonic()
        if rem < 0.5:
            break
        try:
            tab = _make_table(spec)
            if tab is None:
                continue
            N, T = tab
            slice_t = min(1.6, rem)
            # The table is passed as an "n m" graph: m = N*N pairs, each (T[i][j], i).
            pairs = [(T[i][j], i) for i in range(N) for j in range(N)]
            text = lib.run_c(C_SOURCE, [d, D, seed + idx, round(slice_t, 2)],
                             stdin_graph=(N, pairs), timeout=slice_t + 3)
            parts = text.split()
            if not parts or parts[0] != "OK":
                continue
            S = [int(x) for x in parts[1:1 + d]]
            if len(S) != d or len(set(S)) != d:
                continue
            edges = [(g, N + T[g][s]) for g in range(N) for s in S]
            n2 = 2 * N
            if n2 > best[0] and lib.is_valid(n2, edges, d, D):
                best = (n2, edges)
        except Exception:
            continue
    return best


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))      # K_{d,d}: valid for D >= 2
    best = fallback
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    try:
        cand = _search_bi_cayley(d, D, best, seed, t0, time_limit)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
