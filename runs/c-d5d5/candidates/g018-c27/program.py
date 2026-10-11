"""Bi-Cayley search: an orbit-checked search over bipartite Cayley-type graphs.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.
The C engine works on a different family from the lift search: a bipartite graph on A_g, B_h
(g, h in a finite group G) with A_g adjacent to B_{g s} for s in a connection set S of size d.
Left multiplication is an automorphism that is transitive on each side, so the diameter is <= D
iff a BFS of depth D from A_e and from B_e reaches every vertex. Groups are semidirect products
Z_m x| Z_k2 (r = 1 gives the abelian groups). S is annealed to minimise unreached pairs.
The engine tries group orders 2|G| just above the start's order, and climbs one step per success.
Every output is re-checked in Python with lib.is_valid, and the start graph is kept as fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (only n is used); anything after it is discarded.
 * stdout:  "n m" then edges of a valid bi-Cayley graph with n > start n, or "0 0" if none.
 *
 * Graph: vertices A_g = g and B_h = G + h for g, h in a group of order G.
 *        Edge A_g -- B_{g*s} for each s in S, |S| = d, S a set of distinct group elements.
 * Check: BFS of depth D from A_e and from B_e reaches everything (transitivity on each side).
 * Search: simulated annealing over S inside random groups of order G.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXD 32
#define MAXV (2 * MAXG)
#define MAXCAND 16384

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

static int gcd_int(int a, int b) {
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK2, GORD;
static int RP[MAXG];
static int INV[MAXG];

static void set_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

/* Fills INV for the current group. Returns 0 if some element has no inverse (bad group). */
static int compute_inv(void) {
    for (int x = 0; x < GORD; x++) {
        INV[x] = -1;
        for (int y = 0; y < GORD; y++)
            if (gmul(x, y) == 0) { INV[x] = y; break; }
        if (INV[x] < 0) return 0;
    }
    return 1;
}

static int CM[MAXCAND], CK[MAXCAND], CR[MAXCAND];

/* All semidirect groups Z_m x| Z_k2 of order G (m*k2 = G) with valid r. Returns count. */
static int enum_groups(int G) {
    int cnt = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        if (m == 1) {
            if (cnt < MAXCAND) { CM[cnt] = 1; CK[cnt] = k2; CR[cnt] = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_int(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            if (cnt < MAXCAND) { CM[cnt] = m; CK[cnt] = k2; CR[cnt] = r; cnt++; }
        }
    }
    return cnt;
}

/* ------------------------------------------------------------ bi-Cayley state */

static int NG;                      /* group order; the graph has 2*NG vertices */
static int S[MAXD];                 /* connection set, distinct group elements */
static int ADJ[MAXV][MAXD];
static int VIS[MAXV];
static int VST = 0;
static int QU[MAXV];

static int in_S(int x, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Recomputes adjacency entries for connection element i. */
static void set_adj_elem(int i) {
    for (int g = 0; g < NG; g++) {
        ADJ[g][i] = NG + gmul(g, S[i]);
        ADJ[NG + g][i] = gmul(g, INV[S[i]]);
    }
}

/* Unreached vertices from src within distance D. */
static long reach_cost(int src) {
    if (VST >= 1000000000) { memset(VIS, 0, sizeof(VIS)); VST = 0; }
    VST++;
    int head = 0, tail = 0;
    VIS[src] = VST;
    QU[tail++] = src;
    for (int depth = 0; depth < D; depth++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = QU[head++];
            for (int i = 0; i < d; i++) {
                int v = ADJ[u][i];
                if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
            }
        }
    }
    return (long)(2 * NG - tail);
}

static long cost_eval(void) {
    return reach_cost(0) + reach_cost(NG);
}

/* One annealing run over S inside the current group. Returns 1 with S valid on success. */
static int anneal(long steps) {
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(NG); } while (in_S(x, i));
        S[i] = x;
    }
    for (int i = 0; i < d; i++) set_adj_elem(i);
    long cost = cost_eval();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) return 0;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        int i = rndint(d);
        int nv = rndint(NG);
        if (in_S(nv, d)) continue;
        int old = S[i];
        S[i] = nv;
        set_adj_elem(i);
        long c2 = cost_eval();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            S[i] = old;
            set_adj_elem(i);
        }
    }
    return cost == 0;
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.85;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Read the start order, then consume the rest of stdin. */
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = 0;
    {
        int ch;
        while ((ch = getchar()) != EOF) { }
    }

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    int Gcur = n0 / 2 + 1;
    if (Gcur < d) Gcur = d;

    int bestG = 0, bestM = 0, bestK2 = 0, bestR = 0;
    int bestS[MAXD];
    int fails = 0;

    while (now() < t_end) {
        if (Gcur > MAXG || 2L * Gcur > moore) break;
        NG = Gcur;
        int nc = enum_groups(NG);
        if (nc == 0) { Gcur++; continue; }
        int c = rndint(nc);
        set_group(CM[c], CK[c], CR[c]);
        if (!compute_inv()) { fails++; continue; }
        long steps = 20000 + (long)fails * 2000;
        if (steps > 400000) steps = 400000;
        if (anneal(steps)) {
            bestG = NG;
            bestM = CM[c];
            bestK2 = CK[c];
            bestR = CR[c];
            for (int i = 0; i < d; i++) bestS[i] = S[i];
            Gcur++;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }

    set_group(bestM, bestK2, bestR);
    NG = bestG;
    long m = (long)NG * d;
    printf("%d %ld\n", 2 * NG, m);
    for (int g = 0; g < NG; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, NG + gmul(g, bestS[i]));
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

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
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
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
