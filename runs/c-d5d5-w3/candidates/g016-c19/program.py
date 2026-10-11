"""Bi-lift search over small base graphs (new construction), with a safe known-start fallback.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.
C searches for voltage lifts of a base with kb vertices per side (kb in {1,2,3}, d darts per base
vertex) over a random semidirect group Z_m x| Z_k of order N. The lift has 2*kb*N vertices.
Left multiplication is an automorphism, so diameter <= D iff a BFS of depth D from each of the
2*kb class representatives reaches every vertex. Annealing moves change dart voltages and swap
the B-endpoints of two darts, which keeps all degrees at d. Each success raises the target order.
Python re-checks the output with lib.is_valid and keeps the start graph if anything fails.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-lift search over semidirect groups.
 *
 * Usage:   prog d D seed time_limit start_total
 * stdout:  "n m" then m lines "u v" for the largest valid lift found, or "0 0".
 *
 * Base: kb A-vertices and kb B-vertices, ND = d*kb darts. Dart t = (DI[t], DJ[t], DS[t])
 * joins A_{i,x} to B_{j, x*s}. Each A_i has exactly d darts, and each B_j has exactly d darts
 * because layer l uses a permutation of the B indices.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXV 8192
#define MAXDEG 32
#define MAXD 96
#define MAXE 131072
#define BIGCOST 1000000000L

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

/* ------------------------------------------------------------ group Z_m x| Z_k, order N */

static int N;
static int MUL[MAXG][MAXG];
static int INV[MAXG];

/* Element (a,b) is coded a*k+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static void build_group(int m, int k, int r) {
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MUL[x][y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MUL[x][y] == 0) { INV[x] = y; break; }
}

/* Random semidirect group of order n. Returns 0 if no valid r was found. */
static int sample_group(int n, int *om, int *ok, int *orr) {
    int divs[64], nd = 0;
    for (int m = 1; m <= n && nd < 64; m++)
        if (n % m == 0) divs[nd++] = m;
    int m = divs[rndint(nd)];
    int k = n / m;
    if (m == 1) { *om = 1; *ok = k; *orr = 0; return 1; }
    if (k == 1) { *om = m; *ok = 1; *orr = 1 % m; return 1; }
    for (int t = 0; t < 400; t++) {
        int r = 1 + rndint(m - 1);
        if (gcd(r, m) != 1) continue;
        if (powmod(r, k, m) != 1 % m) continue;
        *om = m; *ok = k; *orr = r;
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ lift state */

static int KB, ND;
static int DI[MAXD], DJ[MAXD], DS[MAXD];
static int LADJ[MAXV][MAXDEG];
static int LDEG[MAXV];
static int VIS[MAXV], VST = 0;
static int QU[MAXV];

/* Recorded best lift (its edge list is stored at success time, since MUL changes later). */
static int BNV = 0, BCNT = 0;
static int BEU[MAXE], BEV[MAXE];

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_adj(void) {
    int NV = 2 * KB * N;
    for (int v = 0; v < NV; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++) {
            int a = DI[t] * N + x;
            int b = (KB + DJ[t]) * N + MUL[x][DS[t]];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_adj();
    int NV = 2 * KB * N;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * N;
        VST++;
        int h = 0, t = 0;
        VIS[src] = VST;
        QU[t++] = src;
        for (int depth = 0; depth < D && h < t; depth++) {
            int end = t;
            while (h < end) {
                int u = QU[h++];
                for (int i = 0; i < LDEG[u]; i++) {
                    int v = LADJ[u][i];
                    if (VIS[v] != VST) { VIS[v] = VST; QU[t++] = v; }
                }
            }
        }
        total += NV - t;
    }
    return total;
}

static void init_lift(int kb) {
    KB = kb;
    ND = d * kb;
    int perm[8];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < kb; i++) {
            int t = l * kb + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(N);
        }
    }
}

/* Anneal voltages and B-endpoint swaps. Returns the final cost (0 means success). */
static long anneal(long steps) {
    long c = orbit_cost();
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND), old = DS[t], nv = rndint(N);
            if (nv == old) continue;
            DS[t] = nv;
            long c2 = orbit_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else DS[t] = old;
        } else {
            if (ND < 2) continue;
            int t1 = rndint(ND), t2 = rndint(ND);
            if (t1 == t2 || DJ[t1] == DJ[t2]) continue;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = orbit_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    return c;
}

/* Store the current successful lift (uses MUL for the current group). */
static void record(void) {
    BNV = 2 * KB * N;
    BCNT = 0;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++) {
            if (BCNT >= MAXE) return;
            BEU[BCNT] = DI[t] * N + x;
            BEV[BCNT] = (KB + DJ[t]) * N + MUL[x][DS[t]];
            BCNT++;
        }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_total\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int total = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXDEG) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    int fails = 0;
    while (now() < t_end) {
        if (total + 2 > moore) break;
        int goal = total + 2 + 2 * (fails / 10 < 20 ? fails / 10 : 20);
        if (goal > moore) goal = total + 2;
        int kb = 1 + rndint(3);
        int Nn = (goal + 2 * kb - 1) / (2 * kb) + rndint(3);
        if (Nn < 2 || Nn > MAXG || 2L * kb * Nn > MAXV || 2L * kb * Nn > moore) {
            fails++;
            continue;
        }
        int gm, gk, gr;
        N = Nn;
        if (!sample_group(N, &gm, &gk, &gr)) { fails++; continue; }
        build_group(gm, gk, gr);
        init_lift(kb);
        long steps = 4000 + rndint(8000) + (long)(fails / 30) * 3000;
        if (steps > 60000) steps = 60000;
        if (anneal(steps) == 0) {
            int nv = 2 * kb * N;
            if (nv > total) {
                record();
                total = nv;
                fails = 0;
                continue;
            }
        }
        fails++;
    }

    if (BCNT > 0) {
        printf("%d %d\n", BNV, BCNT);
        for (int e = 0; e < BCNT; e++) printf("%d %d\n", BEU[e], BEV[e]);
    } else {
        printf("0 0\n");
    }
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

    # Safe fallback: K_{d,d} (valid for D >= 2), or a known construction when available.
    best = lib.haar_graph(d, range(d))
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.95 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 2.5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
