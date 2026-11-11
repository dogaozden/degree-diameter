"""Bi-Cayley (Haar-type) search for bipartite degree-diameter graphs.

Construction: for a finite group G of order N and a connection set S of d distinct elements,
the graph on A-side g and B-side h has edges A_g ~ B_{g*s} for s in S. It is bipartite and
d-regular with 2N vertices. Left multiplication by G is an automorphism that is transitive on
each side, so the diameter only has to be checked by BFS from A_e and B_e.

G is a semidirect product Z_m x|_r Z_k, which includes nonabelian groups for most orders.
The C engine searches upward from a target order. For each order it runs simulated annealing
on S, with cost = number of vertices unreached within D from A_e and B_e, and it tries random
groups of that order. Every solution is printed as a graph. Python validates it with lib.is_valid
and keeps the best valid graph, starting from the algebraic starts (hexagon, GQ, projective plane).
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64
#define MAXCAND 200000
#define NCAP 2400
#define STEPS 30000
#define ABEL(j) (cm[j] == 1 || cr[j] == 1)

static int d, D;
static int N;
static double t_end;

static int *mt = NULL, *iv = NULL, *mark = NULL, *qbuf = NULL;
static int capN = 0;
static int stamp = 0;
static int Sg[MAXD], Si[MAXD];
static int cm[MAXCAND], ck[MAXCAND], cr[MAXCAND];
static int eu[NCAP * MAXD], ev[NCAP * MAXD];
static int bestN = 0, bestM = 0;

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

/* Enumerate semidirect groups Z_m x|_r Z_k of order n. Returns count; *nonab = count with r != 1. */
static int enum_groups(int n, int *nonab) {
    int c = 0;
    *nonab = 0;
    for (int m = 1; m <= n && c < MAXCAND; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            cm[c] = 1; ck[c] = k; cr[c] = 0; c++;
            continue;
        }
        for (int r = 1; r < m && c < MAXCAND; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cm[c] = m; ck[c] = k; cr[c] = r;
            if (r != 1) (*nonab)++;
            c++;
        }
    }
    return c;
}

/* Build multiplication and inverse tables for Z_m x|_r Z_k (element a*k+b). */
static void setup_group(int n, int m, int k, int r) {
    N = n;
    if (capN < n) {
        free(mt); free(iv); free(mark); free(qbuf);
        mt = malloc(sizeof(int) * (size_t)n * n);
        iv = malloc(sizeof(int) * (size_t)n);
        mark = calloc((size_t)2 * n, sizeof(int));
        qbuf = malloc(sizeof(int) * (size_t)2 * n);
        capN = n;
    }
    int *rp = malloc(sizeof(int) * (size_t)k);
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            mt[x * n + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    free(rp);
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (mt[x * n + y] == 0) { iv[x] = y; break; }
}

/* Number of vertices within distance D of src in the bi-Cayley graph. */
static int reach_count(int src) {
    if (++stamp == 0x7ffffff0) {
        memset(mark, 0, sizeof(int) * 2 * (size_t)capN);
        stamp = 1;
    }
    int head = 0, tail = 0;
    mark[src] = stamp;
    qbuf[tail++] = src;
    for (int depth = 0; depth < D; depth++) {
        if (head == tail) break;
        int lvl_end = tail;
        for (; head < lvl_end; head++) {
            int v = qbuf[head];
            if (v < N) {
                int base = v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + mt[base + Sg[i]];
                    if (mark[u] != stamp) { mark[u] = stamp; qbuf[tail++] = u; }
                }
            } else {
                int base = (v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = mt[base + Si[i]];
                    if (mark[u] != stamp) { mark[u] = stamp; qbuf[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of (source, vertex) pairs at distance > D, sources A_e and B_e. */
static long cost(void) {
    long c = 2L * N - reach_count(0);
    c += 2L * N - reach_count(N);
    return c;
}

/* Simulated annealing over the connection set S. Returns 1 if cost reaches 0. */
static int anneal(double until, long steps) {
    for (int i = 0; i < d; i++) {
        int x, ok;
        do {
            x = rndint(N);
            ok = 1;
            for (int j = 0; j < i; j++) if (Sg[j] == x) ok = 0;
        } while (!ok);
        Sg[i] = x;
        Si[i] = iv[x];
    }
    long cur = cost();
    double T = 4.0;
    for (long it = 0; it < steps && cur > 0; it++) {
        if ((it & 255) == 0 && now() > until) return 0;
        int i = rndint(d);
        int x = rndint(N), clash = 0;
        for (int j = 0; j < d; j++) if (Sg[j] == x) { clash = 1; break; }
        if (clash) continue;
        int old = Sg[i], oldi = Si[i];
        Sg[i] = x;
        Si[i] = iv[x];
        long nc = cost();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            Sg[i] = old;
            Si[i] = oldi;
        }
        T *= 0.9995;
        if (T < 0.4) T = 4.0;
    }
    return cur == 0;
}

static void store_solution(void) {
    bestN = N;
    bestM = 0;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) {
            eu[bestM] = g;
            ev[bestM] = N + mt[g * N + Sg[i]];
            bestM++;
        }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit target_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long target = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    long Nmax = moore_bound() / 2;
    if (Nmax > NCAP) Nmax = NCAP;
    if (target < d) target = d;

    for (long Nt = target; Nt <= Nmax && now() < t_end; Nt++) {
        int n = (int)Nt;
        double rem = t_end - now();
        double slice_end = now() + 0.3 * rem;
        if (slice_end > t_end) slice_end = t_end;
        int ok = 0;
        while (!ok && now() < slice_end) {
            int nonab = 0;
            int c = enum_groups(n, &nonab);
            if (c == 0) break;
            int j = -1;
            for (int t = 0; t < 64; t++) {
                int c2 = rndint(c);
                if (nonab > 0 && rndint(10) < 7 && ABEL(c2)) continue;
                j = c2;
                break;
            }
            if (j < 0) j = rndint(c);
            setup_group(n, cm[j], ck[j], cr[j]);
            ok = anneal(slice_end, STEPS);
            if (ok) store_solution();
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", 2 * bestN, bestM);
        for (int i = 0; i < bestM; i++) printf("%d %d\n", eu[i], ev[i]);
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    target = best[0] // 2 + 1  # bi-Cayley graph of order 2N beats best when N > best[0] / 2
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), target],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
