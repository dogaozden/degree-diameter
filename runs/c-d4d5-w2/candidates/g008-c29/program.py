"""Bi-Cayley (Haar-type) search engine.

Construction: for a group G of order N and a d-subset S of G, the bipartite graph has
parts A = {A_x} and B = {B_y}, x, y in G, with edges A_x ~ B_{xs} for s in S. Left
multiplication is an automorphism, so the diameter test needs only two BFS runs, from A_e
and from B_e. Groups are semidirect products Z_m x| Z_k (r^k = 1 mod m), searched at
random, with simulated-annealing swaps on S. The Python side keeps the best algebraic start
and validates every output with lib.is_valid, so a failed search still returns a valid graph.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bi-Cayley search: prog d D seed time_limit.  Prints the largest valid graph found as
 * "n m" plus edges, or "0 0". Vertices A_x = x, B_y = N + y, group order N = ORD.
 * Edges A_x ~ B_{x*s} for s in S (|S| = d, distinct). */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1200
#define MAXDEG 64

typedef struct { int m, k, r; } GDesc;

static int d, D;
static double t_end;
static int ORD;
static int mt[MAXG * MAXG];
static int ginv[MAXG];
static int S[MAXDEG], Sinv[MAXDEG];
static unsigned char inS[MAXG];
static int dist_[2 * MAXG], q_[2 * MAXG];
static GDesc gl[8192];
static int ng;

static int bestN = 0, bestM, bestK, bestR;
static int bestS[MAXDEG];

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

/* All semidirect groups Z_m x|_r Z_k of order n. */
static void list_groups(int n) {
    ng = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ng < 8192) { gl[ng].m = 1; gl[ng].k = k; gl[ng].r = 0; ng++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ng < 8192) { gl[ng].m = m; gl[ng].k = k; gl[ng].r = r; ng++; }
        }
    }
}

/* Multiplication table for the group with element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void build_group(int m, int k, int r) {
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < ORD; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < ORD; y++) {
            int c = y / k, e = y % k;
            mt[x * ORD + y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < ORD; x++)
        for (int y = 0; y < ORD; y++)
            if (mt[x * ORD + y] == 0) { ginv[x] = y; break; }
}

/* Number of vertices NOT within distance D of src. */
static int unreached(int src) {
    int nv = 2 * ORD;
    for (int v = 0; v < nv; v++) dist_[v] = -1;
    int head = 0, tail = 0;
    q_[tail++] = src;
    dist_[src] = 0;
    while (head < tail) {
        int v = q_[head++];
        if (dist_[v] >= D) continue;
        int nd2 = dist_[v] + 1;
        if (v < ORD) {
            const int *row = mt + v * ORD;
            for (int i = 0; i < d; i++) {
                int u = ORD + row[S[i]];
                if (dist_[u] < 0) { dist_[u] = nd2; q_[tail++] = u; }
            }
        } else {
            const int *row = mt + (v - ORD) * ORD;
            for (int i = 0; i < d; i++) {
                int u = row[Sinv[i]];
                if (dist_[u] < 0) { dist_[u] = nd2; q_[tail++] = u; }
            }
        }
    }
    return nv - tail;
}

static int cost(void) { return unreached(0) + unreached(ORD); }

/* Anneal the d-subset S over the current group. Returns 1 when the graph has diameter <= D. */
static int climb(double until, long maxsteps) {
    for (int i = 0; i < ORD; i++) inS[i] = 0;
    for (int i = 0; i < d; i++) {
        int g;
        do g = rndint(ORD); while (inS[g]);
        S[i] = g;
        inS[g] = 1;
        Sinv[i] = ginv[g];
    }
    int c = cost();
    double T = 0.7;
    for (long st = 0; st < maxsteps; st++) {
        if (c == 0) return 1;
        if ((st & 255) == 0 && now() > until) return 0;
        int i = rndint(d), g = rndint(ORD);
        if (inS[g]) continue;
        int old = S[i];
        inS[old] = 0;
        S[i] = g;
        inS[g] = 1;
        Sinv[i] = ginv[g];
        int nc = cost();
        if (nc <= c || rnd01() < exp((double)(c - nc) / T)) {
            c = nc;
        } else {
            inS[g] = 0;
            S[i] = old;
            inS[old] = 1;
            Sinv[i] = ginv[old];
        }
    }
    return c == 0;
}

/* Try to find a valid bi-Cayley graph with group order n before 'until'. */
static int attempt(int n, double until) {
    if (n < d) return 0;
    list_groups(n);
    if (ng == 0) return 0;
    while (now() < until) {
        GDesc g = gl[rndint(ng)];
        ORD = n;
        build_group(g.m, g.k, g.r);
        if (climb(until, 60000)) {
            bestN = n;
            bestM = g.m;
            bestK = g.k;
            bestR = g.r;
            memcpy(bestS, S, sizeof(int) * d);
            return 1;
        }
    }
    return 0;
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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    long hi = moore_bound() / 2;
    if (hi > MAXG) hi = MAXG;

    double slice = 0.05;
    while (now() < t_end) {
        int lo = bestN ? bestN + 1 : d;
        if (lo > hi) break;
        for (long N0 = hi; N0 >= lo && now() < t_end; N0--) {
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (attempt((int)N0, until)) break;
        }
        slice *= 2;
    }

    if (bestN > 0) {
        ORD = bestN;
        build_group(bestM, bestK, bestR);
        printf("%d %d\n", 2 * bestN, bestN * d);
        for (int x = 0; x < ORD; x++)
            for (int i = 0; i < d; i++)
                printf("%d %d\n", x, ORD + mt[x * ORD + bestS[i]]);
    } else {
        printf("0 0\n");
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=None, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
