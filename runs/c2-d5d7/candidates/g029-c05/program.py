"""Bi-Cayley voltage search for the d=5, D=7 target, with a compact C engine.

Changes from the parent:
  * The C engine is a new, smaller program. It searches only bi-Cayley lifts over
    semidirect products Z_m x| Z_k. Each candidate is an orbit-reduced BFS objective
    (sources a_e and b_e, valid by vertex-transitivity on each side), minimised by
    annealed voltage moves with elite restarts.
  * Search starts above the incumbent order passed in by Python. The C engine no longer
    reads a start graph from stdin. It prints only a graph it has verified by the
    orbit objective; otherwise it prints "0 0" and Python keeps its best algebraic start.
  * Algebraic starts are kept as fallbacks: the incidence graph of H(4) (2730 vertices,
    diameter 6) for d=5 D>=6, PG(2,q) incidence graphs, and K_{d,d}.

This is an untested change. Python validates every returned graph with lib.is_valid,
so a bad C result cannot reduce the score below the fallback.
"""
import itertools
import time

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

#define MAXH 2048
#define MAXD 8
#define MAXV (2 * MAXH)

static int d, D;
static int NN;
static int MT[MAXH * MAXH];
static int INV[MAXH];
static int RP[MAXH];

typedef struct { int m, k, r; } Grp;

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
    long s = 0, p = 1;
    if (D <= 0 || d <= 0) return 1;
    if (d == 2) return 2L * D;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Choose a uniformly random admissible Z_m x| Z_k with r^k = 1 mod m, m*k = N. */
static int pick_group(int N, Grp *G) {
    long cnt = 0;
    int found = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)(cnt < 2000000000L ? cnt : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
                found = 1;
            }
        }
    }
    return found;
}

/* Element x = a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is 0. */
static int gm(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)RP[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static void setup(const Grp *G) {
    int N = G->m * G->k;
    NN = N;
    RP[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) RP[b] = (int)((long)RP[b - 1] * G->r % G->m);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = gm(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* Vertices: a_x = x (side A), b_x = N + x (side B).
 * Edges: a_x -- b_{x*g_t}, t = 0..d-1, with g_0 = 0 (identity) and distinct g_t.
 * Left multiplication is an automorphism transitive on each side, so BFS from a_e and b_e
 * decides the diameter. Returns the number of (source, vertex) pairs unreached within D. */
static int dist_[MAXV], stamp_[MAXV], qu[MAXV];
static int stampc = 0;

static long eval_bad(const int *g) {
    int N = NN, V = 2 * N;
    int inv[MAXD];
    long total = 0;
    for (int t = 0; t < d; t++) inv[t] = INV[g[t]];
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stampc++;
        stamp_[src] = stampc;
        dist_[src] = 0;
        qu[tail++] = src;
        while (head < tail) {
            int v = qu[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            for (int t = 0; t < d; t++) {
                int u;
                if (v < N) u = N + MT[v * N + g[t]];
                else u = MT[(v - N) * N + inv[t]];
                if (stamp_[u] != stampc) {
                    stamp_[u] = stampc;
                    dist_[u] = dv + 1;
                    qu[tail++] = u;
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static int clash(const int *g, int t, int nv) {
    for (int i = 0; i < t; i++) if (g[i] == nv) return 1;
    return 0;
}

static int used_except(const int *g, int t, int nv) {
    for (int i = 0; i < d; i++) if (i != t && g[i] == nv) return 1;
    return 0;
}

/* Annealed voltage hill-climb; g[0] = 0 is fixed. */
static long climb(int *g, int *bestg, long steps, double until) {
    long bad = eval_bad(g);
    long bestb = bad;
    memcpy(bestg, g, sizeof(int) * d);
    double T = 2.0;
    double alpha = pow(0.1, 1.0 / (double)steps);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = g[t], nv;
        do { nv = rndint(NN); } while (used_except(g, t, nv));
        g[t] = nv;
        long nb = eval_bad(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) {
                bestb = bad;
                memcpy(bestg, g, sizeof(int) * d);
            }
        } else {
            g[t] = old;
        }
        T *= alpha;
        if (T < 0.2) T = 0.2;
    }
    return bestb;
}

static int OUTN = 0, OUTM = 0;
static int OU[MAXH * MAXD], OV[MAXH * MAXD];

static void build_out(int N, const int *g) {
    OUTN = 2 * N;
    OUTM = 0;
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++) {
            OU[OUTM] = x;
            OV[OUTM] = N + MT[x * N + g[t]];
            OUTM++;
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double lim = atof(argv[4]);
    long startn = argc > 5 ? atol(argv[5]) : 0;
    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double until = now() + lim * 0.95;
    long moore = moore_bound();
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXH) Nmax_l = MAXH;
    int Nmax = (int)Nmax_l;
    long Nlo_l = startn / 2 + 1;
    if (Nlo_l < d + 1) Nlo_l = d + 1;
    int Nlo = (int)Nlo_l;

    int gv[MAXD], bestgv[MAXD];
    Grp G;
    while (now() < until && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > 200) span = 200;
        double u = rnd01();
        int N = Nlo + (int)(u * sqrt(u) * span);
        if (N > Nmax) N = Nmax;
        int found = 0;
        for (int grp = 0; grp < 4 && now() < until && !found; grp++) {
            if (!pick_group(N, &G)) break;
            setup(&G);
            for (int att = 0; att < 4 && now() < until && !found; att++) {
                gv[0] = 0;
                for (int t = 1; t < d; t++) {
                    int nv;
                    do { nv = rndint(N); } while (clash(gv, t, nv));
                    gv[t] = nv;
                }
                if (climb(gv, bestgv, 3000, until) == 0) {
                    build_out(N, bestgv);
                    Nlo = N + 1;
                    found = 1;
                }
            }
        }
    }

    if (OUTM > 0) {
        printf("%d %d\n", OUTN, OUTM);
        for (int i = 0; i < OUTM; i++) printf("%d %d\n", OU[i], OV[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    The caller validates the result with lib.is_valid.
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 8 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.92 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
