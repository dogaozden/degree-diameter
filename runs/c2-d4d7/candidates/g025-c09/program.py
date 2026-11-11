"""Bi-Cayley search over explicit finite groups, with a safe fallback chain.

Change from the parent: instead of voltage lifts with a few base vertices, this program searches
bi-Cayley graphs directly. The vertex set is A = G and B = G for a finite group G, with a_x
adjacent to b_{x*s} for each s in a d-element set S. Left multiplication by G is an automorphism,
so the diameter is exact from two BFS runs, one from a_e and one from b_e. Candidate groups are
non-metacyclic where possible: PSL(2,p), PGL(2,p) (p = 5, 7, 11), and direct products with Z_k.
Metacyclic semidirect products Z_m x| Z_k fill the rest.

The group multiplication table is passed to a small C engine, which runs a hill-climb over S.
The Python side rebuilds the graph and checks it with lib.is_valid. Any failure keeps the best
valid graph found so far.

Packing note: lib.run_c only accepts graphs as "n m" followed by m edge lines. The table is sent as
"N M" followed by M pairs whose flattened values are the N*N table entries (padded to even length).
The C engine reads N, M, then the first N*N values.
"""
import functools
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley search over a group given by its multiplication table (identity = 0).
 * Graph: a_x (index x) adjacent to b_{x*s} (index N + x*s) for s in S, |S| = d.
 * Left multiplication is an automorphism, so the diameter is zero-defect iff BFS from a_0 and
 * from b_0 reaches every vertex within D steps. The defect is the total number of unreached
 * vertices from both sources. Hill-climb over S with plateau moves and rare uphill moves.
 *
 * Usage: prog d D seed time_limit < input
 * input: "n m", then 2m integers; the first n*n of them are the table row by row.
 * output: "1 s1 ... sd" on success, else "0".
 */

#define MAXG 1500
#define MAXD 16

static int N, d, D;
static int *MT;
static int INV[MAXG];
static int S[MAXD];
static int inS[MAXG];
static int dist[2 * MAXG];
static int qu[2 * MAXG];
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

static int unreached(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist[v] = -1;
    int h = 0, t = 0;
    dist[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (dist[v] >= D) continue;
        if (v < N) {
            const int *row = MT + (size_t)v * N;
            for (int i = 0; i < d; i++) {
                int u = N + row[S[i]];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    qu[t++] = u;
                }
            }
        } else {
            int y = v - N;
            const int *row = MT + (size_t)y * N;
            for (int i = 0; i < d; i++) {
                int u = row[INV[S[i]]];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    qu[t++] = u;
                }
            }
        }
    }
    return V - t;
}

static int cost(void) { return unreached(0) + unreached(N); }

static int try_group(double until, int *out) {
    if (N <= d) return 0;
    while (now() < until) {
        memset(inS, 0, sizeof(int) * N);
        for (int i = 0; i < d; i++) {
            int e;
            do { e = rndint(N); } while (inS[e]);
            inS[e] = 1;
            S[i] = e;
        }
        int c = cost();
        int stall = 0;
        for (long it = 0;; it++) {
            if (c == 0) {
                memcpy(out, S, sizeof(int) * d);
                return 1;
            }
            if (stall > 3000) break;
            if ((it & 127) == 0 && now() > until) return 0;
            int i = rndint(d);
            int old = S[i];
            int e;
            do { e = rndint(N); } while (inS[e]);
            inS[old] = 0;
            inS[e] = 1;
            S[i] = e;
            int nc = cost();
            if (nc < c) {
                c = nc;
                stall = 0;
            } else if (nc == c || rnd01() < 0.02) {
                c = nc;
                stall++;
            } else {
                inS[e] = 0;
                inS[old] = 1;
                S[i] = old;
                stall++;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double until = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n, m;
    if (d < 1 || d > MAXD || D < 1) { printf("0\n"); return 0; }
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXG || m < 0) { printf("0\n"); return 0; }
    N = n;
    long need = (long)N * N;
    if (2L * m < need || d >= N) { printf("0\n"); return 0; }
    MT = malloc(sizeof(int) * (size_t)need);
    if (!MT) { printf("0\n"); return 0; }
    for (long i = 0; i < need; i++) {
        if (scanf("%d", &MT[i]) != 1) { printf("0\n"); return 0; }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MT[(size_t)x * N + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) { printf("0\n"); return 0; }
    }

    int out[MAXD];
    if (try_group(until, out)) {
        printf("1");
        for (int i = 0; i < d; i++) printf(" %d", out[i]);
        printf("\n");
    } else {
        printf("0\n");
    }
    return 0;
}
'''


MAX_ORDER = 720
SLICE = 1.5
BASE_SPECS = [("PSL", 5), ("PGL", 5), ("PSL", 7), ("PGL", 7), ("PSL", 11)]
_BASE_CACHE = {}


def _spec_order(spec):
    kind, p = spec
    o = p * (p * p - 1) // 2
    return o if kind == "PSL" else 2 * o


def _perm_table(kind, p):
    """Multiplication table of PSL(2,p) or PGL(2,p) acting on P^1(F_p); identity has index 0."""
    deg = p + 1
    inf = p
    t = tuple((x + 1) % p if x < p else inf for x in range(deg))

    def sinv(x):
        if x == inf:
            return 0
        if x == 0:
            return inf
        return (-pow(x, p - 2, p)) % p

    gens = [t, tuple(sinv(x) for x in range(deg))]
    if kind == "PGL":
        c = next(c for c in range(2, p) if all(pow(c, e, p) != 1 for e in range(1, p - 1)))
        gens.append(tuple((c * x) % p if x < p else inf for x in range(deg)))
    ident = tuple(range(deg))
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        g = elems[i]
        i += 1
        for h in gens:
            x = tuple(h[y] for y in g)
            if x not in index:
                index[x] = len(elems)
                elems.append(x)
    N = len(elems)
    T = [0] * (N * N)
    for i, a in enumerate(elems):
        for j, b in enumerate(elems):
            T[i * N + j] = index[tuple(a[y] for y in b)]
    return N, T


def _base(spec):
    if spec not in _BASE_CACHE:
        _BASE_CACHE[spec] = _perm_table(*spec)
    return _BASE_CACHE[spec]


def _prod_table(NG, TG, k):
    """Direct product of a group table with Z_k; element g*k+c."""
    N = NG * k
    T = [0] * (N * N)
    for g in range(NG):
        for c in range(k):
            x = g * k + c
            for h in range(NG):
                tgh = TG[g * NG + h]
                for e in range(k):
                    T[x * N + h * k + e] = tgh * k + (c + e) % k
    return N, T


def _base_product(spec, k):
    NG, TG = _base(spec)
    if k == 1:
        return NG, TG
    return _prod_table(NG, TG, k)


def _semi_table(m, k, r):
    mul = lib.semidirect_group(m, k, r)[1]
    N = m * k
    return N, [mul(x, y) for x in range(N) for y in range(N)]


def _candidate_groups(N, rng):
    """Thunks building candidate group tables of order N; non-metacyclic groups come first."""
    thunks = []
    for spec in BASE_SPECS:
        o = _spec_order(spec)
        if N % o == 0:
            thunks.append(functools.partial(_base_product, spec, N // o))
    semis = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            rlist = [0]
        else:
            rlist = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rlist)
        for r in rlist[:2]:
            semis.append((m, k, r))
    rng.shuffle(semis)
    thunks += [functools.partial(_semi_table, m, k, r) for m, k, r in semis[:6]]
    return thunks[:6]


def _pack(N, T):
    flat = list(T)
    if len(flat) % 2:
        flat.append(0)
    return N, [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


def _try_group(d, D, seed, table, slice_s):
    NG, T = table
    text = lib.run_c(C_SOURCE, [d, D, seed, slice_s], stdin_graph=_pack(NG, T),
                     timeout=slice_s + 10)
    parts = text.split()
    if len(parts) < 1 + d or parts[0] != "1":
        return None
    S = [int(x) for x in parts[1:1 + d]]
    edges = []
    for x in range(NG):
        for s in S:
            edges.append((x, NG + T[x * NG + s]))
    return 2 * NG, edges


# ---------------------------------------------------------------- algebraic starts

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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
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
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
    return out


# ---------------------------------------------------------------- main entry

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

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d > 15:
        return best

    deadline = t0 + 0.85 * time_limit - 2.0
    rng = random.Random(seed * 7919 + 17)
    N_hi = min(moore // 2, MAX_ORDER)
    N = 1
    while True:
        N = max(N, best[0] // 2 + 1)
        if N > N_hi or time.monotonic() > deadline - 0.5:
            break
        if N > d:
            for make in _candidate_groups(N, rng):
                left = deadline - time.monotonic()
                slice_s = min(SLICE, left - 0.2)
                if slice_s < 0.3:
                    break
                try:
                    table = make()
                    got = _try_group(d, D, seed * 1000003 + N, table, slice_s)
                    if got is not None and got[0] > best[0] and lib.is_valid(got[0], got[1], d, D):
                        best = got
                        break
                except Exception:
                    continue
        N += 1
    return best
