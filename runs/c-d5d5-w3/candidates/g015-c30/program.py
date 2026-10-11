"""Bi-Cayley search over many finite groups, with a verified fallback.

New construction (replaces the voltage-lift engine): a bipartite graph on two copies of a group G,
with A_g adjacent to B_{g*s} for s in a fixed set S of d distinct elements. Every vertex has degree d.
Left multiplication by G is an automorphism that preserves both sides, so the diameter is <= D iff
BFS of depth D from A_e and from B_e reaches everything. The C engine does simulated annealing over S
for one group at a time, using a multiplication table passed in by Python.

Python builds candidate groups of order in a range near the Moore bound: cyclic groups, semidirect
products Z_m x| Z_k, and direct products of small permutation groups (A4, S4, A5, PSL(2,7)) with
cyclic groups. It tries them in ascending order of order and keeps the largest valid graph. Each
output is re-checked with lib.is_valid. K_{d,d}, or a known construction for D = 3 or 4, is the fallback.
"""
import itertools
import math
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search for one group.
 * stdin : "G G*G" then G*G lines "x*G+y v" giving the multiplication table x*y = v.
 * argv  : d D seed budget_seconds
 * stdout: "OK s_1 ... s_d" (a set S with diameter <= D), or "FAIL".
 * Graph: A_g = g, B_g = G+g, A_g ~ B_{g*s} for s in S.
 * Cost = unreached (vertex from A_e) + unreached (vertex from B_e) within depth D.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXDD 64

static int G, d, D, E;
static int M[MAXG][MAXG];
static int INV[MAXG];
static int S[MAXDD], IS[MAXDD];
static int qb[2 * MAXG];
static int vis[2 * MAXG];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void set_S(int k, int v) {
    S[k] = v;
    IS[k] = INV[v];
}

static int in_S(int v) {
    for (int k = 0; k < d; k++)
        if (S[k] == v) return 1;
    return 0;
}

/* Number of vertices reached from start within D steps. */
static int reach(int start) {
    stamp++;
    int head = 0, tail = 0;
    qb[tail++] = start;
    vis[start] = stamp;
    for (int depth = 0; depth < D; depth++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = qb[head++];
            if (u < G) {
                for (int k = 0; k < d; k++) {
                    int v = G + M[u][S[k]];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qb[tail++] = v;
                    }
                }
            } else {
                int h = u - G;
                for (int k = 0; k < d; k++) {
                    int v = M[h][IS[k]];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qb[tail++] = v;
                    }
                }
            }
        }
    }
    return tail;
}

static long cost(void) {
    int a = reach(E);
    int b = reach(G + E);
    return (long)(2 * G - a) + (long)(2 * G - b);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double t_end = now() + budget;

    int nn, mm;
    if (scanf("%d %d", &nn, &mm) != 2 || nn < 1 || nn > MAXG || mm != nn * nn) {
        printf("FAIL\n");
        return 0;
    }
    G = nn;
    for (int e = 0; e < mm; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= G * G || v < 0 || v >= G) {
            printf("FAIL\n");
            return 0;
        }
        M[u / G][u % G] = v;
    }

    E = -1;
    for (int e = 0; e < G && E < 0; e++) {
        int ok = 1;
        for (int x = 0; x < G && ok; x++)
            if (M[e][x] != x) ok = 0;
        if (ok) E = e;
    }
    if (E < 0 || d < 1 || d > G || d > MAXDD || D < 1) {
        printf("FAIL\n");
        return 0;
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (M[x][y] == E) INV[x] = y;

    for (int k = 0; k < d; k++) S[k] = -1;
    for (int k = 0; k < d; k++) {
        int v;
        do { v = rndint(G); } while (in_S(v));
        set_S(k, v);
    }

    long cur = cost();
    long bestrun = cur;
    long stag = 0;
    long iter = 0;
    while (cur > 0) {
        if ((iter & 127) == 0 && now() > t_end) break;
        iter++;
        int k = rndint(d);
        int nv = rndint(G);
        if (in_S(nv)) continue;
        int old = S[k];
        set_S(k, nv);
        long c2 = cost();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / 0.8)) {
            cur = c2;
        } else {
            set_S(k, old);
        }
        if (cur < bestrun) {
            bestrun = cur;
            stag = 0;
        } else if (++stag > 4000) {
            for (int j = 0; j < d; j++) S[j] = -1;
            for (int j = 0; j < d; j++) {
                int v;
                do { v = rndint(G); } while (in_S(v));
                set_S(j, v);
            }
            cur = cost();
            bestrun = cur;
            stag = 0;
        }
    }

    if (cur == 0) {
        printf("OK");
        for (int k = 0; k < d; k++) printf(" %d", S[k]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
'''


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


# ------------------------------------------------------------ group library

def _cyc_mul(m):
    return lambda x, y: (x + y) % m


def _direct(n1, m1, n2, m2):
    """Direct product: element x = a*n2 + b with a in the first factor and b in the second."""
    return lambda x, y: m1(x // n2, y // n2) * n2 + m2(x % n2, y % n2)


def _perm_group(gens, limit=400):
    """Closure of permutation generators (tuples). Returns (order, mul) or None if order > limit."""
    k = len(gens[0])
    ident = tuple(range(k))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(p[g[i]] for i in range(k))
                if q not in index:
                    index[q] = len(elems)
                    elems.append(q)
                    nxt.append(q)
                    if len(elems) > limit:
                        return None
        frontier = nxt
    n = len(elems)
    table = [[index[tuple(elems[x][elems[y][i]] for i in range(k))] for y in range(n)]
             for x in range(n)]
    return n, (lambda x, y: table[x][y])


def _base_groups():
    """Small non-abelian permutation groups as (name, order, mul)."""
    out = []
    specs = [
        ("A4", [(1, 2, 0, 3), (1, 0, 3, 2)]),
        ("S4", [(1, 2, 3, 0), (1, 0, 2, 3)]),
        ("A5", [(1, 2, 3, 4, 0), (1, 2, 0, 3, 4)]),
    ]
    for name, gens in specs:
        g = _perm_group(gens)
        if g:
            out.append((name, g[0], g[1]))
    # PSL(2,7) acting on the projective line over GF(7); point 7 is infinity.
    inv7 = lambda t: pow(t, 5, 7)
    t1 = tuple([(t + 1) % 7 for t in range(7)] + [7])
    t2 = tuple([(2 * t) % 7 for t in range(7)] + [7])
    t3 = tuple([7] + [(7 - inv7(t)) % 7 for t in range(1, 7)] + [0])
    g = _perm_group([t1, t2, t3], limit=400)
    if g:
        out.append(("PSL27", g[0], g[1]))
    return out


def _candidates(lo, hi):
    """Groups with order in [lo, hi] as (order, name, mul), sorted by order."""
    out = []
    for n in range(lo, hi + 1):
        out.append((n, f"Z{n}", _cyc_mul(n)))
    for k in range(2, 13):
        for m in range(2, hi // k + 1):
            n = m * k
            if n < lo or n > hi:
                continue
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if math.gcd(m, k) == 1:
                rs = [r for r in rs if r != 1]
            for r in rs[:1]:
                order, mul, _ = lib.semidirect_group(m, k, r)
                out.append((order, f"Z{m}:Z{k}:{r}", mul))
    for name, h, mh in _base_groups():
        for c in range(2, hi // h + 1):
            n = h * c
            if lo <= n <= hi:
                out.append((n, f"{name}xZ{c}", _direct(h, mh, c, _cyc_mul(c))))
    out.sort(key=lambda t: t[0])
    return out


def _try_group(d, D, G, mul, seed, sl):
    """Run the C search for one group. Returns (2G, edges) if valid, else None."""
    tab = [[mul(x, y) for y in range(G)] for x in range(G)]
    pairs = [(x * G + y, tab[x][y]) for x in range(G) for y in range(G)]
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(sl, 3)],
                         stdin_graph=(G, pairs), timeout=sl + 2.0)
    except (RuntimeError, OSError, ValueError):
        return None
    tok = text.split()
    if len(tok) != d + 1 or tok[0] != "OK":
        return None
    try:
        S = [int(x) for x in tok[1:]]
    except ValueError:
        return None
    if len(set(S)) != d or any(not 0 <= s < G for s in S):
        return None
    edges = [(g, G + tab[g][s]) for g in range(G) for s in S]
    n = 2 * G
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    deadline = t0 + 0.95 * time_limit - 1.5
    if deadline - time.monotonic() < 2.0:
        return best

    lo = max(d, moore // 5)
    hi = moore // 3 + 2
    cands = _candidates(lo, hi) if lo <= hi else []

    seed_ctr = 1000 * (seed % 100000 + 1)
    stop = False
    while not stop:
        todo = [c for c in cands if 2 * c[0] > best[0]]
        if not todo:
            break
        progress = False
        for idx, (G, name, mul) in enumerate(todo):
            rem = deadline - time.monotonic()
            if rem < 0.4:
                stop = True
                break
            if 2 * G <= best[0]:
                continue
            left = len(todo) - idx
            sl = min(rem - 0.2, max(0.4, min(3.0, rem / left)))
            seed_ctr += 1
            progress = True
            res = _try_group(d, D, G, mul, seed_ctr, sl)
            if res is not None and res[0] > best[0]:
                best = res
        if not progress:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
