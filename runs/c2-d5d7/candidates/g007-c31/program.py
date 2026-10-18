"""Multi-base lift search for the weakest cases (d = 5, D = 7 is the target).

Previous version: bi-Cayley graphs, one base vertex per side, over semidirect groups Z_m x|_r Z_k.

This version is a bolder change. The C engine searches k-base voltage lifts with k in {1, 2, 3}:
- Base: k vertices on each side. The base multigraph is the sum of d permutation matrices sigma_t,
  with sigma_0 = identity. Dart (i, t) joins a_i to b_{sigma_t(i)}.
- Lift: a_{i,x} is adjacent to b_{sigma_t(i), x*g_{i,t}} for t = 0..d-1, where G is a semidirect
  product Z_m x|_r Z_k of order N. Each side has d neighbours per vertex, and the graph has 2kN vertices.
- Simplicity: darts from the same base vertex to the same base vertex carry distinct voltages.
- Diameter: left multiplication by G is an automorphism whose orbits are the k fibres on each side.
  So diameter <= D holds iff BFS from a_{i,e} (i < k) and from b_{j,e} (j < k) reaches everything
  within D. The annealing penalty is the total number of unreached (source, vertex) pairs.

k = 1 reproduces the bi-Cayley search. The start graph (H(q) incidence, PG(2,q), W(q)) is the fallback,
and the C engine only replaces it with a strictly larger valid lift.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" (only n is used as the threshold; edges are not read).
 * stdout:  "V E" then E lines "u v" for a valid lift with V > n, or "0 0" if none found.
 *
 * Vertices: a_{i,x} = i*N + x (side A), b_{j,y} = K*N + j*N + y (side B),
 *           i, j < K, x, y in G, |G| = N.
 * Edges:    a_{i,x} -- b_{sig[t][i], x * g[i][t]} for t = 0..d-1, sig[0] = identity.
 * Simplicity: for fixed (i, target), the voltages of the darts are pairwise distinct.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 2048
#define MAXK 3
#define MAXD 16
#define MAXV (2 * MAXK * MAXH)
#define MAXE (MAXD * MAXV)
#define MAXCAND 512
#define STEPS 10000
#define SPAN 30
#define RESTARTS 4

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;

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

/* Groups Z_m x|_r Z_k with m*k = N, gcd(r,m)=1, r^k = 1 mod m. */
static int enum_groups(int N, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static Grp pick_group(const Grp *c, int cnt) {
    for (int tries = 0; tries < 8; tries++) {
        Grp g = c[rndint(cnt)];
        if (g.m > 1 && g.r != 1) return g;
    }
    return c[rndint(cnt)];
}

/* Group multiplication table, inverses, and powers of r for the current group. */
static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int RP[MAXH];
static int NN;

static void setup_group(int N, Grp G) {
    NN = N;
    int m = G.m, k = G.k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

/* Base structure: K base vertices per side, d darts; dart t joins a_i to b_{sig[t][i]}. */
static int KB;
static int sig[MAXD][MAXK];
static int sinv[MAXD][MAXK];
static int gv[MAXK][MAXD];

static void init_perms(void) {
    for (int t = 0; t < d; t++) {
        int p[MAXK];
        for (int i = 0; i < KB; i++) p[i] = i;
        if (t > 0) {
            for (int i = KB - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
            }
        }
        for (int i = 0; i < KB; i++) {
            sig[t][i] = p[i];
            sinv[t][p[i]] = i;
        }
    }
}

/* Neighbour number t of vertex v in the lift. */
static inline int nbr(int v, int t) {
    int N = NN;
    if (v < KB * N) {
        int i = v / N, x = v - i * N;
        return KB * N + sig[t][i] * N + MTAB[(size_t)x * N + gv[i][t]];
    } else {
        int w = v - KB * N;
        int j = w / N, y = w - j * N;
        int i = sinv[t][j];
        return i * N + MTAB[(size_t)y * N + INVT[gv[i][t]]];
    }
}

static int stampv[MAXV];
static int distv[MAXV];
static int qv[MAXV];
static int stamp_ = 0;

/* Number of (source, vertex) pairs at distance > D; sources are the identity of each fibre. */
static long eval_bad(void) {
    int N = NN, V = 2 * KB * N;
    long total = 0;
    for (int s = 0; s < 2 * KB; s++) {
        int src = (s < KB) ? s * N : KB * N + (s - KB) * N;
        int head = 0, tail = 0;
        stamp_++;
        stampv[src] = stamp_;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            for (int t = 0; t < d; t++) {
                int u = nbr(v, t);
                if (stampv[u] != stamp_) {
                    stampv[u] = stamp_;
                    distv[u] = dv + 1;
                    qv[tail++] = u;
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Voltage nv for dart (i, t) is ok if no other dart from i to the same fibre has it. */
static int valid_all(int i, int t, int nv) {
    for (int s = 0; s < d; s++)
        if (s != t && sig[s][i] == sig[t][i] && gv[i][s] == nv) return 0;
    return 1;
}

static int valid_prefix(int i, int t, int nv) {
    for (int s = 0; s < t; s++)
        if (sig[s][i] == sig[t][i] && gv[i][s] == nv) return 0;
    return 1;
}

static int simple_ok(void) {
    for (int i = 0; i < KB; i++)
        for (int t = 0; t < d; t++)
            for (int s = 0; s < t; s++)
                if (sig[s][i] == sig[t][i] && gv[i][s] == gv[i][t]) return 0;
    return 1;
}

static void init_voltages(void) {
    for (int i = 0; i < KB; i++)
        for (int t = 0; t < d; t++) {
            if (KB == 1 && t == 0) { gv[i][t] = 0; continue; }
            int nv = 0, tries = 0;
            do { nv = rndint(NN); tries++; } while (!valid_prefix(i, t, nv) && tries < 100000);
            gv[i][t] = nv;
        }
}

/* Annealed hill-climb on voltages; leaves gv at the last accepted state. */
static long climb(double until, double T0) {
    long bad = eval_bad();
    double T = T0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int i = rndint(KB);
        int t = (KB == 1) ? 1 + rndint(d - 1) : rndint(d);
        int old = gv[i][t], nv = 0, tries = 0;
        do { nv = rndint(NN); tries++; } while (!valid_all(i, t, nv) && tries < 1000);
        if (tries >= 1000) continue;
        gv[i][t] = nv;
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else gv[i][t] = old;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) sn = 0;
    if (sn < 0) sn = 0;

    static int OU[MAXE], OV[MAXE];
    static Grp cand[MAXCAND];
    int found = 0, bestV = 0, ne = 0;
    long B = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        while (now() < t_end) {
            int k = 1 + rndint(MAXK);
            long Nlo = (B + 1 + 2L * k - 1) / (2L * k);
            if (Nlo < d + 1) Nlo = d + 1;
            long Nmax = moore / (2L * k);
            if (Nmax > MAXH) Nmax = MAXH;
            if (Nlo > Nmax) {
                int any = 0;
                for (int kk = 1; kk <= MAXK; kk++) {
                    long lo = (B + 1 + 2L * kk - 1) / (2L * kk);
                    if (lo < d + 1) lo = d + 1;
                    long hi = moore / (2L * kk);
                    if (hi > MAXH) hi = MAXH;
                    if (lo <= hi) any = 1;
                }
                if (!any) break;
                continue;
            }
            long span = Nmax - Nlo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(Nlo + rndint((int)span));
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            KB = k;
            init_perms();

            long bad = 1;
            for (int rs = 0; rs < RESTARTS && bad > 0 && now() < t_end; rs++) {
                init_voltages();
                bad = climb(t_end, rs == 0 ? 2.0 : 1.0);
            }
            if (bad == 0 && simple_ok()) {
                int V = 2 * k * N;
                if (V > B) {
                    found = 1;
                    bestV = V;
                    B = V;
                    ne = 0;
                    for (int i = 0; i < k; i++)
                        for (int x = 0; x < N; x++)
                            for (int t = 0; t < d; t++) {
                                OU[ne] = i * N + x;
                                OV[ne] = k * N + sig[t][i] * N + MTAB[(size_t)x * N + gv[i][t]];
                                ne++;
                            }
                }
            }
        }
    }

    if (found) {
        printf("%d %d\n", bestV, ne);
        for (int i = 0; i < ne; i++) printf("%d %d\n", OU[i], OV[i]);
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

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=(best[0], []), timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
