"""Lift-search program for bipartite graphs with max degree d and diameter D.

Bold change: for the weakest target (d=11, D=4) the search no longer grows the
generalized-quadrangle graph by cover/twin steps. It searches voltage lifts of
small bipartite base graphs over abelian groups Z_A x Z_B. For a lift, the
diameter check only needs BFS from the 2K base vertices with group coordinate 0,
because the group acts by automorphisms. The C annealer minimises the number of
unreachable pairs from those sources. Every candidate is checked with lib.is_valid.
The fallback is the generalized quadrangle W(q) (or K_{d,d}), which is always valid.
"""
import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 12
#define DMAX 32
#define NMAX 12000

static int d, D, K, A, B, G, NN;
static int sig[DMAX][KMAX];
static int inv_[DMAX][KMAX];
static int vol[DMAX][KMAX];
static int stampA[NMAX];
static int curStamp = 0;
static int qv[NMAX], qdist[NMAX];
static int eu[NMAX * DMAX], ev[NMAX * DMAX];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

/* Group Z_A x Z_B, element x1*B + x2. */
static int gadd(int x, int g) {
    int x1 = x / B, x2 = x % B, g1 = g / B, g2 = g % B;
    return ((x1 + g1) % A) * B + (x2 + g2) % B;
}

static int gneg(int g) {
    int g1 = g / B, g2 = g % B;
    return ((A - g1) % A) * B + (B - g2) % B;
}

static void rebuild_inv(int j) {
    for (int i = 0; i < K; i++) inv_[j][sig[j][i]] = i;
}

/* Lift: A-vertex (i,x) joins B-vertex (K+sig[j][i], x+vol[j][i]) for each dart j.
   Vertex id = base*G + x; base < K is the A side, base >= K the B side.
   Returns the number of (source, target) pairs at distance > D, over sources (b,0). */
static long long cost_eval(void) {
    long long bad = 0;
    for (int s = 0; s < 2 * K; s++) {
        curStamp++;
        int src = s * G;
        int qh = 0, qt = 0;
        qv[qt] = src;
        qdist[qt] = 0;
        qt++;
        stampA[src] = curStamp;
        while (qh < qt) {
            int u = qv[qh], du = qdist[qh];
            qh++;
            if (du >= D) continue;
            int b = u / G;
            int x = u - b * G;
            if (b < K) {
                for (int j = 0; j < d; j++) {
                    int v = (K + sig[j][b]) * G + gadd(x, vol[j][b]);
                    if (stampA[v] != curStamp) {
                        stampA[v] = curStamp;
                        qv[qt] = v;
                        qdist[qt] = du + 1;
                        qt++;
                    }
                }
            } else {
                int bb = b - K;
                for (int j = 0; j < d; j++) {
                    int i = inv_[j][bb];
                    int v = i * G + gadd(x, gneg(vol[j][i]));
                    if (stampA[v] != curStamp) {
                        stampA[v] = curStamp;
                        qv[qt] = v;
                        qdist[qt] = du + 1;
                        qt++;
                    }
                }
            }
        }
        bad += NN - qt;
    }
    return bad;
}

static void output_graph(void) {
    int m = 0;
    for (int i = 0; i < K; i++) {
        for (int x = 0; x < G; x++) {
            int u = i * G + x;
            int nbr[DMAX];
            int cnt = 0;
            for (int j = 0; j < d; j++) {
                int v = (K + sig[j][i]) * G + gadd(x, vol[j][i]);
                int dup = 0;
                for (int t = 0; t < cnt; t++)
                    if (nbr[t] == v) { dup = 1; break; }
                if (!dup) {
                    nbr[cnt++] = v;
                    eu[m] = u;
                    ev[m] = v;
                    m++;
                }
            }
        }
    }
    printf("%d %d\n", NN, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", eu[e], ev[e]);
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    A = atoi(argv[6]);
    B = atoi(argv[7]);
    if (d < 1 || d > DMAX || D < 1 || K < 1 || K > KMAX || A < 1 || B < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = A * B;
    NN = 2 * K * G;
    if (G < 2 || NN > NMAX) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    for (int j = 0; j < d; j++) {
        for (int i = 0; i < K; i++) sig[j][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rnd(i + 1);
            int t = sig[j][i];
            sig[j][i] = sig[j][r];
            sig[j][r] = t;
        }
        for (int i = 0; i < K; i++) vol[j][i] = rnd(G);
        rebuild_inv(j);
    }

    long long cur = cost_eval();
    if (cur == 0) {
        output_graph();
        return 0;
    }
    double c0 = (double)cur;
    clock_t t0 = clock();
    while (cur > 0) {
        double frac = ((double)(clock() - t0)) / CLOCKS_PER_SEC / tl;
        if (frac >= 1.0) break;
        double T = (0.01 * c0 + 2.0) * (1.0 - frac) + 0.05;
        int j = rnd(d);
        if (rnd(10) < 7) {
            int i = rnd(K);
            int old = vol[j][i];
            int nw = rnd(G - 1);
            if (nw >= old) nw++;
            vol[j][i] = nw;
            long long c2 = cost_eval();
            double dl = (double)(c2 - cur);
            if (dl <= 0 || rnd01() < exp(-dl / T)) cur = c2;
            else vol[j][i] = old;
        } else {
            int i1 = rnd(K), i2 = rnd(K);
            if (i1 == i2) continue;
            int t = sig[j][i1];
            sig[j][i1] = sig[j][i2];
            sig[j][i2] = t;
            rebuild_inv(j);
            long long c2 = cost_eval();
            double dl = (double)(c2 - cur);
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                cur = c2;
            } else {
                t = sig[j][i1];
                sig[j][i1] = sig[j][i2];
                sig[j][i2] = t;
                rebuild_inv(j);
            }
        }
    }
    if (cur == 0) output_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pick_group(G, rng):
    """Return (A, B) with A * B = G: cyclic (A = 1) half the time, else Z_A x Z_B."""
    if rng.random() < 0.5:
        return 1, G
    divs = [a for a in range(2, G + 1) if G % a == 0 and a * a <= G]
    if not divs:
        return 1, G
    A = rng.choice(divs)
    return A, G // A


def _lift_attempt(d, D, seed, k, A, B, budget):
    """Run the C lift annealer once; return (n, edges), with n = 0 on failure."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", k, A, B],
                    stdin_graph=None, timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def _lift_search(d, D, rng, deadline, best_n_fn, consider):
    """Round-robin over base sizes k; each step asks for a lift just above the current best order."""
    ks = (2, 3, 4, 5, 6)
    gstate = {k: 1 for k in ks}
    i = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.5:
            break
        k = ks[i % len(ks)]
        i += 1
        G = max(gstate[k], best_n_fn() // (2 * k) + 1, 2)
        if 2 * k * G > 6000:
            break
        A, B = _pick_group(G, rng)
        budget = min(remaining - 0.5, 4.0)
        try:
            n, e = _lift_attempt(d, D, rng.randrange(1 << 30), k, A, B, budget)
        except (RuntimeError, ValueError):
            n, e = 0, []
        if n > 0 and n > best_n_fn():
            consider(n, e)
            gstate[k] = G + 1
        else:
            gstate[k] = G


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 4 and d >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            deadline = start + 0.85 * tl - 1.0
            _lift_search(d, D, rng, deadline, lambda: best[0], consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
