"""Bi-Cayley search: a different family from the lift search.

Each candidate is a bi-Cayley graph over a semidirect product Z_M x| Z_K of order G:
vertices A_x and B_y (x, y in G), with A_x adjacent to B_{x*s} for each s in a connection
set S of size d. Left multiplication is an automorphism, so the diameter is at most D iff
BFS from A_e and from B_e reaches everything within D steps. Simulated annealing moves
elements of S to minimise the unreached-pair count. The target group order rises one step
at a time after each success. Every C result is re-checked in C and then in Python. If the
search finds nothing, the Python known constructions or K_{d,d} are returned.
"""
import itertools
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

#define MAXG 512
#define MAXD 32
#define MAXV (2 * MAXG)

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

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------ group Z_M x| Z_K2 */

/* Element a*K2+b, (a,b)(c,e) = (a + r^b c mod M, b+e mod K2). Identity is 0. */
static int GM, GK2, G;
static int RP[MAXG];
static int GMUL[MAXG][MAXG];
static int GINV[MAXG];

static int gmul_raw(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

static void set_group(int M, int K2, int r) {
    GM = M;
    GK2 = K2;
    G = M * K2;
    RP[0] = 1 % M;
    for (int b = 1; b < K2; b++) RP[b] = (int)((long)RP[b - 1] * r % M);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++) GMUL[x][y] = gmul_raw(x, y);
    for (int x = 0; x < G; x++) {
        GINV[x] = 0;
        for (int y = 0; y < G; y++)
            if (GMUL[x][y] == 0) { GINV[x] = y; break; }
    }
}

/* Random semidirect structure of order Gt (cyclic if nothing else is found quickly). */
static void sample_group(int Gt, int *M, int *K2, int *r) {
    int divs[MAXG], nd = 0;
    for (int m = 1; m <= Gt; m++)
        if (Gt % m == 0) divs[nd++] = m;
    for (int t = 0; t < 300; t++) {
        int mm = divs[rndint(nd)];
        int k2 = Gt / mm;
        if (mm == 1) { *M = 1; *K2 = k2; *r = 0; return; }
        int rr = 1 + rndint(mm - 1);
        if (gcd(rr, mm) != 1) continue;
        if (powmod(rr, k2, mm) != 1 % mm) continue;
        *M = mm; *K2 = k2; *r = rr;
        return;
    }
    *M = Gt; *K2 = 1; *r = 1 % Gt;
}

/* ------------------------------------------------------------ connection set */

static int S[MAXD], SI[MAXD];
static unsigned char inS[MAXG];

/* BFS from src in the bi-Cayley graph; returns the number of vertices NOT within distance D. */
static int QU[MAXV];
static int VIS[MAXV];
static int vst = 0;

static int bfs_unreached(int src) {
    int N = 2 * G;
    vst++;
    int head = 0, tail = 0;
    VIS[src] = vst;
    QU[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int u = QU[head++];
            if (u < G) {
                for (int i = 0; i < d; i++) {
                    int v = G + GMUL[u][S[i]];
                    if (VIS[v] != vst) { VIS[v] = vst; QU[tail++] = v; }
                }
            } else {
                int y = u - G;
                for (int i = 0; i < d; i++) {
                    int v = GMUL[y][SI[i]];
                    if (VIS[v] != vst) { VIS[v] = vst; QU[tail++] = v; }
                }
            }
        }
    }
    return N - tail;
}

/* Two sources suffice: A_e and B_e (left multiplication acts transitively on each side). */
static long cost_eval(void) {
    return (long)bfs_unreached(0) + (long)bfs_unreached(G);
}

static int verify_full(void) {
    for (int s = 0; s < 2 * G; s++)
        if (bfs_unreached(s) != 0) return 0;
    return 1;
}

/* One simulated-annealing run on S for the current group. Returns 1 if cost reaches 0. */
static int anneal(long steps, double T0) {
    memset(inS, 0, sizeof(unsigned char) * (size_t)G);
    for (int i = 0; i < d; i++) {
        int g;
        do { g = rndint(G); } while (inS[g]);
        S[i] = g;
        inS[g] = 1;
        SI[i] = GINV[g];
    }
    long cost = cost_eval();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) break;
        int i = rndint(d);
        int nv = rndint(G);
        if (inS[nv]) continue;
        int old = S[i];
        inS[old] = 0;
        S[i] = nv;
        inS[nv] = 1;
        SI[i] = GINV[nv];
        long c2 = cost_eval();
        double T = T0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            inS[nv] = 0;
            S[i] = old;
            inS[old] = 1;
            SI[i] = GINV[old];
        }
    }
    return cost == 0;
}

/* ------------------------------------------------------------ best result */

static int bestG = 0;
static int BEM = 0;
static int BEU[MAXG * MAXD];
static int BEV[MAXG * MAXD];

static void record_best(void) {
    bestG = G;
    BEM = 0;
    for (int x = 0; x < G; x++)
        for (int i = 0; i < d; i++) {
            BEU[BEM] = x;
            BEV[BEM] = G + GMUL[x][S[i]];
            BEM++;
        }
}

/* ------------------------------------------------------------ main */

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
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long maxG = moore / 2;          /* each side has G vertices */
    if (maxG > MAXG) maxG = MAXG;
    if (maxG < d) { printf("0 0\n"); return 0; }
    long lowG = moore / 4;          /* start the ladder near the record scale */

    int fails = 0;
    while (now() < t_end && bestG < maxG) {
        int Gt;
        if (bestG + 1 < lowG) Gt = bestG + 1 + rndint((int)(lowG - bestG));
        else Gt = bestG + 1;
        if (Gt < d) Gt = d;
        if (Gt > maxG) Gt = (int)maxG;

        int M, K2, r;
        sample_group(Gt, &M, &K2, &r);
        set_group(M, K2, r);

        long steps = 40000 + (long)fails * 4000;
        if (steps > 400000) steps = 400000;
        if (anneal(steps, 3.0) && verify_full()) {
            record_best();
            fails = 0;
        } else {
            fails++;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestG, BEM);
    for (int e = 0; e < BEM; e++) printf("%d %d\n", BEU[e], BEV[e]);
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

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
