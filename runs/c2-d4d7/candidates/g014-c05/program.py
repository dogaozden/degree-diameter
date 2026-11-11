"""Bi-Cayley search for bipartite degree-diameter graphs.

Construction: pick a finite group G of order N and a connection set S = {s_1..s_d} in G.
The graph has vertices A = {a_g} and B = {b_h} (g, h in G), with a_g ~ b_h iff g^{-1}h in S.
Left multiplication by G is an automorphism acting regularly on A and on B, so the diameter is
exact after two BFS runs, from a_e and from b_e. The engine searches over groups (metacyclic
Z_m x| Z_k, including cyclic and abelian products) and connection sets, using simulated
annealing on the number of vertices not reached within distance D. It grows N while it succeeds.

Fallback chain: K_{d,d}, then the algebraic starts (PG(2,q), W(q), H(3)). Every output is
checked with lib.is_valid before it is used.
"""
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

#define MAXG 1200
#define MAXD 32
#define MAXV (2 * MAXG)
#define MAXCAND 4096
#define MAXEDGE (MAXG * MAXD)
#define STEPS 8000

static int d, D;
static double t_end;

static int GN;
static int GT[MAXG * MAXG];
static int INV[MAXG];
static int rp[MAXG];
static int cm[MAXCAND], ck[MAXCAND], cr[MAXCAND], ncand;
static int S[MAXD], Sinv[MAXD];
static int vis[MAXV], dd[MAXV], qb[MAXV];
static int vstamp = 0;
static int oeu[MAXEDGE], oev[MAXEDGE];
static int ne = 0, bestN = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Candidate groups of order N: Z_m x|_r Z_k with m*k = N, r^k = 1 mod m, gcd(r,m) = 1. */
static void enum_groups(int N) {
    ncand = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ncand < MAXCAND) { cm[ncand] = 1; ck[ncand] = k; cr[ncand] = 0; ncand++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcdi(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ncand < MAXCAND) { cm[ncand] = m; ck[ncand] = k; cr[ncand] = r; ncand++; }
        }
    }
}

/* Element a*k+b, product (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Identity is 0. */
static void build_group(int m, int k, int r) {
    int N = m * k;
    GN = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int aa = (int)(((long)a + (long)rp[b] * c) % m);
            GT[x * N + y] = aa * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { INV[x] = y; break; }
}

/* BFS in the bi-Cayley graph from src; returns the number of vertices NOT within distance D. */
static int bfs_unreached(int src) {
    int N = GN, V = 2 * N;
    vstamp++;
    int head = 0, tail = 0, reached = 1;
    vis[src] = vstamp;
    dd[src] = 0;
    qb[tail++] = src;
    while (head < tail) {
        int v = qb[head++];
        if (dd[v] >= D) continue;
        if (v < N) {
            int g = v;
            for (int i = 0; i < d; i++) {
                int u = N + GT[g * N + S[i]];
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    dd[u] = dd[v] + 1;
                    qb[tail++] = u;
                    reached++;
                }
            }
        } else {
            int h = v - N;
            for (int i = 0; i < d; i++) {
                int u = GT[h * N + Sinv[i]];
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    dd[u] = dd[v] + 1;
                    qb[tail++] = u;
                    reached++;
                }
            }
        }
    }
    return V - reached;
}

/* Exact: left translations act transitively on A and on B, so these two sources suffice. */
static int cost(void) {
    return bfs_unreached(0) + bfs_unreached(GN);
}

static int in_S(int x) {
    for (int i = 0; i < d; i++) if (S[i] == x) return 1;
    return 0;
}

static int attempt(long steps, double until) {
    int N = GN;
    if (N <= d + 1) return 0;
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(N); } while (({ int dup = 0; for (int j = 0; j < i; j++) if (S[j] == x) dup = 1; dup; }));
        S[i] = x;
    }
    for (int i = 0; i < d; i++) Sinv[i] = INV[S[i]];
    int cur = cost();
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        int i = rndint(d);
        int old = S[i];
        int x;
        do { x = rndint(N); } while (in_S(x));
        S[i] = x;
        Sinv[i] = INV[x];
        int c = cost();
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / 0.5)) {
            cur = c;
        } else {
            S[i] = old;
            Sinv[i] = INV[old];
        }
    }
    return cur == 0;
}

static void save_found(int N) {
    ne = 0;
    bestN = N;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) {
            oeu[ne] = g;
            oev[ne] = N + GT[g * N + S[i]];
            ne++;
        }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = atol(argv[5]);

    double t0 = now();
    t_end = t0 + limit * 0.95;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    {
        char buf[4096];
        while (fread(buf, 1, sizeof buf, stdin) > 0) {}
    }

    long moore = moore_bound();
    if (d < 2 || D < 2 || d > MAXD || start_n >= moore) {
        printf("0 0\n");
        return 0;
    }

    long N = start_n / 2 + 1;
    if (N < d + 2) N = d + 2;
    long curN = -1;

    while (now() < t_end) {
        if (2 * N > moore || N > MAXG) break;
        if (N != curN) {
            enum_groups((int)N);
            curN = N;
        }
        if (ncand == 0) { N++; continue; }
        int c = rndint(ncand);
        build_group(cm[c], ck[c], cr[c]);
        if (attempt(STEPS, t_end)) {
            save_found((int)N);
            N++;
        }
    }

    if (ne == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", 2 * bestN, ne);
        for (int i = 0; i < ne; i++) printf("%d %d\n", oeu[i], oev[i]);
    }
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
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

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.92 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
