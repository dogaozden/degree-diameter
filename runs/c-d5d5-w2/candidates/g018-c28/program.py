"""Group-lift engine: bi-Cayley / voltage lifts over explicit finite groups.

The parent searched only metacyclic groups Z_m x| Z_k. This version builds several
non-metacyclic groups in Python (A4, S4, A5 and products with cyclic groups, the affine
group ASL(2,3), the Heisenberg group mod 5, AGL(1,11)) and also some metacyclic groups.
Each group is passed to one fixed C engine as a multiplication table. The C engine
anneals voltages on a base with K vertices per side: a left vertex (i,x) joins right
vertex (j, x*s) for each dart. Left multiplication is an automorphism, so the
diameter check needs BFS from the 2K orbit representatives only.

Safety: K_{d,d} is always the starting fallback, and every candidate is checked with
lib.is_valid before it replaces the best graph. Compile errors or C timeouts stop the
search and return the best valid graph found so far.
"""
import math
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

#define MAXN 4096
#define MAXD 16
#define MAXK 8
#define MAXG 256
#define MAXDART (MAXD * MAXK)

/* Usage: prog d D seed time_limit K N row_0 ... row_{N-1}
 * row_x holds the N entries of the multiplication table: row_x[y] = x*y.
 * Element 0 must be the identity, or the program finds it by search.
 * Output: "n m" plus edges of a valid lift, or "0 0".
 */

static int d, D, K, N, ID, nd;
static int MT[MAXG * MAXG];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Dart t = l*K + i: left i joins right perm_l(i) with voltage dS[t]. */
static int dI[MAXDART], dJ[MAXDART], dS[MAXDART];

static int adjL[MAXN][MAXD];
static int degL[MAXN];
static int visL[MAXN], qL[MAXN];
static int stampL = 0;

/* Number of vertices within distance D of src, using adjL (uniform degree d). */
static int reach_count(int src) {
    stampL++;
    int head = 0, tail = 0;
    visL[src] = stampL;
    qL[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int u = qL[head++];
            for (int i = 0; i < degL[u]; i++) {
                int v = adjL[u][i];
                if (visL[v] != stampL) {
                    visL[v] = stampL;
                    qL[tail++] = v;
                }
            }
        }
    }
    return tail;
}

static void build_adj(void) {
    int n = 2 * K * N;
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dI[t] * N + x;
            int b = (K + dJ[t]) * N + MT[x * N + dS[t]];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
}

/* Cost = 1000 * (duplicate darts) + unreached (representative, vertex) pairs. */
static long lift_cost(void) {
    int n = 2 * K * N;
    long pen = 0;
    for (int t = 0; t < nd; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    build_adj();
    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) unreached += n - reach_count(r * N + ID);
    return pen * 1000L + unreached;
}

/* Full check: every vertex reaches all others within D, and no duplicate darts. */
static int full_check(void) {
    int n = 2 * K * N;
    if (lift_cost() != 0) return 0;
    for (int v = 0; v < n; v++)
        if (reach_count(v) != n) return 0;
    return 1;
}

static void print_lift(void) {
    int n = 2 * K * N, m = nd * N;
    printf("%d %d\n", n, m);
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dI[t] * N + x;
            int b = (K + dJ[t]) * N + MT[x * N + dS[t]];
            printf("%d %d\n", a, b);
        }
}

/* One annealing run from a random lift. Returns 1 if cost 0, 0 if steps ran out,
   -1 if time ran out. */
static int anneal(double until, long steps) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(N);
        }
    }
    long c = lift_cost();
    const double T0 = 4.0, T1 = 0.05;
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 63) == 0 && now() > until) return -1;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        if (K > 1 && rnd01() < 0.2) {
            int l = rndint(d), a = rndint(K), b = rndint(K);
            if (a == b) continue;
            int t1 = l * K + a, t2 = l * K + b;
            int tmp = dJ[t1];
            dJ[t1] = dJ[t2];
            dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) c = c2;
            else {
                tmp = dJ[t1];
                dJ[t1] = dJ[t2];
                dJ[t2] = tmp;
            }
        } else {
            int t = rndint(nd);
            int old = dS[t];
            int ns = rndint(N);
            if (ns == old) continue;
            dS[t] = ns;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) c = c2;
            else dS[t] = old;
        }
    }
    return c == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    N = atoi(argv[6]);
    if (d < 1 || d > MAXD || D < 1 || K < 1 || K > MAXK || N < 1 || N > MAXG ||
        argc < 7 + N) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < N; x++) {
        const char *p = argv[7 + x];
        for (int y = 0; y < N; y++) {
            char *end;
            long v = strtol(p, &end, 10);
            if (end == p || v < 0 || v >= N) {
                printf("0 0\n");
                return 0;
            }
            MT[x * N + y] = (int)v;
            p = end;
        }
    }
    ID = -1;
    for (int e = 0; e < N && ID < 0; e++) {
        int ok = 1;
        for (int y = 0; y < N && ok; y++)
            if (MT[e * N + y] != y) ok = 0;
        if (ok) ID = e;
    }
    if (ID < 0) {
        printf("0 0\n");
        return 0;
    }
    nd = d * K;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    double until = now() + tl * 0.95;
    while (now() < until) {
        int r = anneal(until, 40000);
        if (r < 0) break;
        if (r == 1 && full_check()) {
            print_lift();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ------------------------------------------------------------ group tables

def _closure(gens, mul, e):
    """Elements of the group generated by gens (identity e first), with index map."""
    elems, idx, frontier = [e], {e: 0}, [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in idx:
                    idx[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems, idx


def _table(mul, gens, e):
    """Multiplication table (list of lists of indices) of the group generated by gens."""
    elems, idx = _closure(gens, mul, e)
    return [[idx[mul(x, y)] for y in elems] for x in elems]


def _from_op(N, mul):
    """Table of a group whose elements are the integers 0..N-1."""
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _pmul(p, q):
    """Composition of permutations: (p o q)(i) = p[q[i]]."""
    return tuple(p[i] for i in q)


def _perm_cyclic(gens_perm, n, m):
    """Permutation group on n points times cyclic Z_m."""
    ident = tuple(range(n))

    def mul(x, y):
        return (_pmul(x[0], y[0]), (x[1] + y[1]) % m)

    gens = [(g, 0) for g in gens_perm] + [(ident, 1 % m)]
    return _table(mul, gens, (ident, 0))


_A5 = [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]
_S4 = [(1, 0, 2, 3), (1, 2, 3, 0)]
_A4 = [(1, 2, 0, 3), (1, 0, 3, 2)]


def _asl23():
    """Affine group Z_3^2 x| SL(2,3), order 216. Elements (a,b,c,d,e,f): x -> M x + t."""
    p = 3

    def mul(g, h):
        a1, b1, c1, d1, e1, f1 = g
        a2, b2, c2, d2, e2, f2 = h
        return ((a1 * a2 + b1 * c2) % p, (a1 * b2 + b1 * d2) % p,
                (c1 * a2 + d1 * c2) % p, (c1 * b2 + d1 * d2) % p,
                (a1 * e2 + b1 * f2 + e1) % p, (c1 * e2 + d1 * f2 + f1) % p)

    gens = [(1, 1, 0, 1, 0, 0), (1, 0, 1, 1, 0, 0), (1, 0, 0, 1, 1, 0), (1, 0, 0, 1, 0, 1)]
    return _table(mul, gens, (1, 0, 0, 1, 0, 0))


def _agl1(p, g):
    """AGL(1,p) = Z_p x| Z_p^*, with g a primitive root mod p."""
    def mul(x, y):
        return ((x[0] + x[1] * y[0]) % p, (x[1] * y[1]) % p)

    return _table(mul, [(1, 1), (0, g)], (0, 1))


def _heis(p):
    """Heisenberg group of order p^3 over Z_p."""
    def mul(x, y):
        return ((x[0] + y[0]) % p, (x[1] + y[1]) % p, (x[2] + y[2] + x[0] * y[1]) % p)

    return _table(mul, [(1, 0, 0), (0, 1, 0)], (0, 0, 0))


def _meta(N):
    """Non-abelian metacyclic group of order N when one exists, else cyclic."""
    opts = []
    for m in range(3, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    if opts:
        m, k, r = opts[len(opts) // 2]
    else:
        m, k, r = N, 1, 1
    _, mul, _ = lib.semidirect_group(m, k, r)
    return _from_op(N, mul)


# (name, base size K per side, builder). Each candidate has 2*K*N vertices.
# Ordered so smaller targets, which are more likely to succeed, come first.
COMBOS = [
    ("A5", 3, lambda: _perm_cyclic(_A5, 5, 1)),          # 360
    ("A4xZ5", 3, lambda: _perm_cyclic(_A4, 4, 5)),       # 360
    ("meta60", 3, lambda: _meta(60)),                    # 360
    ("A4xZ15", 1, lambda: _perm_cyclic(_A4, 4, 15)),     # 360
    ("A5xZ3", 1, lambda: _perm_cyclic(_A5, 5, 3)),       # 360
    ("S4xZ4", 2, lambda: _perm_cyclic(_S4, 4, 4)),       # 384
    ("A4xZ8", 2, lambda: _perm_cyclic(_A4, 4, 8)),       # 384
    ("meta96", 2, lambda: _meta(96)),                    # 384
    ("meta176", 1, lambda: _meta(176)),                  # 352
    ("meta180", 1, lambda: _meta(180)),                  # 360
    ("meta192", 1, lambda: _meta(192)),                  # 384
    ("A4xZ16", 1, lambda: _perm_cyclic(_A4, 4, 16)),     # 384
    ("S4xZ8", 1, lambda: _perm_cyclic(_S4, 4, 8)),       # 384
    ("ASL23", 1, _asl23),                                # 432
    ("AGL11", 2, lambda: _agl1(11, 2)),                  # 440
]


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: safe fallback for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    deadline = t0 + 0.86 * time_limit - 1.0
    rows_cache = {}
    seq = 0
    while time.monotonic() < deadline - 1.5:
        ran_any = False
        stop = False
        for name, K, make in COMBOS:
            left = deadline - time.monotonic()
            if left < 1.5:
                stop = True
                break
            if name not in rows_cache:
                T = make()
                rows_cache[name] = [" ".join(map(str, row)) for row in T]
            rows = rows_cache[name]
            N = len(rows)
            n = 2 * K * N
            if n <= best[0] or n > moore:
                continue
            seq += 1
            slice_ = min(2.5, left)
            args = [d, D, int(seed) * 131 + seq, round(slice_, 2), K, N] + rows
            try:
                text = lib.run_c(C_SOURCE, args, stdin_graph=None, timeout=slice_ + 6)
                consider(lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                stop = True
                break
            ran_any = True
        if stop or not ran_any:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
