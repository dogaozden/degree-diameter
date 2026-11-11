"""Haar-graph group search for the degree-diameter target, with the best known algebraic start as fallback.

Construction: for a finite group G of order N and a connection set S = {s_1..s_d} (distinct),
the Haar graph H(G, S) has parts A = {a_x} and B = {b_y}, with a_x ~ b_{x s} for s in S.
It is bipartite, d-regular, and has 2N vertices. Left multiplication by G is an automorphism,
so the diameter test needs only two BFS runs, from a_e and b_e. Groups are semidirect products
Z_m x|_r Z_k with N = m*k. Non-abelian groups give far more room than cyclic or abelian ones.

The C engine ratchets upward: it samples N in a window just above the current bar, hill-climbs S
on the number of vertices left unreached within D from the two sources, and verifies every hit
with an exact bitset all-pairs check. Python keeps the best of the algebraic start (projective
plane or split Cayley hexagon H(q)) and the search output, and checks everything with lib.is_valid.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Haar-graph search over semidirect groups Z_m x|_r Z_k.
 * Usage:  prog d D seed time_limit lo_N
 * Finds a d-regular bipartite Haar graph H(G,S) with 2N > 2*lo_N-1 vertices (N >= lo_N) and
 * diameter <= D. Prints "V E" and the edge list for the largest verified graph, or "0 0".
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXV (2 * MAXN)
#define MAXW (MAXV / 64)
#define MAXD 16
#define STEPS 1500
#define RESTARTS 3
#define WINDOW 24

static int d, D;
static double t_end;

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

/* ---------------- group Z_m x|_r Z_k, element a*k+b ---------------- */
static int gm, gk, NG;
static int rp[MAXN];
static int S[MAXD], Si[MAXD];
static int dist_[MAXV], qu[MAXV], mark_[MAXV];
static int stamp_ = 0;

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)((a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    long t = (long)rp[nb] * a % gm;
    int na = (int)((gm - t) % gm);
    return na * gk + nb;
}

/* Choose a random semidirect group of order N: random divisor m, then random valid r. */
static int pick_group(int N) {
    static int divs[MAXN];
    static int rlist[MAXN];
    int nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0) divs[nd++] = m;
    int m = divs[rndint(nd)];
    int k = N / m;
    int nr = 0;
    if (m == 1) {
        rlist[nr++] = 0;
    } else {
        for (int r = 1; r < m; r++)
            if (gcdi(r, m) == 1 && powmod(r, k, m) == 1 % m) rlist[nr++] = r;
    }
    if (nr == 0) return 0;
    int r = rlist[rndint(nr)];
    gm = m;
    gk = k;
    NG = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    return 1;
}

static void random_S(int N) {
    for (int i = 0; i < d; i++) {
        int g, dup;
        do {
            g = rndint(N);
            dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == g) { dup = 1; break; }
        } while (dup);
        S[i] = g;
        Si[i] = ginv(g);
    }
}

/* Number of vertices within distance D of src (src included). Vertices: A = 0..N-1, B = N..2N-1. */
static int reach_from(int src, int N) {
    stamp_++;
    int head = 0, tail = 0;
    mark_[src] = stamp_;
    dist_[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        if (dist_[v] >= D) continue;
        for (int i = 0; i < d; i++) {
            int u = (v < N) ? N + gmul(v, S[i]) : gmul(v - N, Si[i]);
            if (mark_[u] != stamp_) {
                mark_[u] = stamp_;
                dist_[u] = dist_[v] + 1;
                qu[tail++] = u;
            }
        }
    }
    return tail;
}

/* Vertex transitivity on each side means two BFS runs decide the whole diameter. */
static long objective(int N) {
    int V = 2 * N;
    return (long)(V - reach_from(0, N)) + (long)(V - reach_from(N, N));
}

static int search_group(int N, double until) {
    for (int rst = 0; rst < RESTARTS; rst++) {
        if (now() > until) return 0;
        random_S(N);
        long f = objective(N);
        double T = 1.0;
        for (int it = 0; it < STEPS && f > 0; it++) {
            if ((it & 63) == 0 && now() > until) return 0;
            int i = rndint(d), g = rndint(N), dup = 0;
            for (int j = 0; j < d; j++)
                if (S[j] == g) { dup = 1; break; }
            if (dup) continue;
            int old = S[i], oldi = Si[i];
            S[i] = g;
            Si[i] = ginv(g);
            long nf = objective(N);
            if (nf <= f || rnd01() < exp(-(double)(nf - f) / T)) f = nf;
            else { S[i] = old; Si[i] = oldi; }
            T *= 0.998;
            if (T < 0.3) T = 0.3;
        }
        if (f == 0) return 1;
    }
    return 0;
}

/* ---------------- exact verification ---------------- */
static int TU[MAXN * MAXD], TV[MAXN * MAXD], tne;
static int BU[MAXN * MAXD], BV[MAXN * MAXD], bne;
static int adjv[MAXV][MAXD], degv[MAXV];
static uint64_t BA[MAXV * MAXW], BB[MAXV * MAXW];

static int full_check(int V) {
    int W = (V + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)V * W);
    for (int v = 0; v < V; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < V; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < degv[v]; i++) {
                const uint64_t *s = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < V; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        if (c != V) return 0;
    }
    return 1;
}

static int build_and_check(int N) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) degv[v] = 0;
    tne = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            int w = N + gmul(x, S[i]);
            if (degv[x] >= d || degv[w] >= d) return 0;
            adjv[x][degv[x]++] = w;
            adjv[w][degv[w]++] = x;
            TU[tne] = x;
            TV[tne] = w;
            tne++;
        }
    return full_check(V);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit lo_N\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long hiN = moore / 2;
    if (hiN > MAXN) hiN = MAXN;
    long loN = lo;
    if (loN < d) loN = d;

    int bestV = 0;
    bne = 0;
    while (now() < t_end && loN <= hiN) {
        long N = loN + rndint(WINDOW);
        if (N > hiN) N = hiN;
        if (N < d) continue;
        if (!pick_group((int)N)) continue;
        if (!search_group((int)N, t_end)) continue;
        if (build_and_check((int)N)) {
            memcpy(BU, TU, sizeof(int) * tne);
            memcpy(BV, TV, sizeof(int) * tne);
            bne = tne;
            bestV = 2 * (int)N;
            loN = N + 1;
        }
    }

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestV, bne);
    for (int i = 0; i < bne; i++) printf("%d %d\n", BU[i], BV[i]);
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
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


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
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

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best
    lo = best[0] // 2 + 1  # a Haar graph must have more than half the current order
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
