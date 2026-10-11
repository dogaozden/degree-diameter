"""Bi-Cayley / voltage-lift search with exhaustive group enumeration.

Strategy change: instead of growing a start graph by repairs, this version searches directly
for regular bipartite lifts of order 2pN with p in {1,2,3}. The group is drawn uniformly from
ALL semidirect products Z_m x|_r Z_k of order N (not just a few), the base is a random
d-regular bipartite multigraph on p+p vertices, and the voltages are annealed against an exact
orbit-reduced diameter objective. Only BFS from the 2p fibre representatives is needed.

Safe fallback: the algebraic starts (PG(2,q), Araujo-Pardo-Lopez, W(q), K_{d,d}) are validated
first. The C result is accepted only if it is larger and passes lib.is_valid.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Lift search for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" then m lines "u v", or "0 0".
 * stdout: "n m" then m lines "u v" for the largest graph found (at least the start).
 *
 * A lift of order 2pN: base multigraph on p+p vertices (d-regular), darts (i,j,g) with
 * g in Z_m x|_r Z_k. Vertex (i,x) joins (p+j, x*g). Distances from (a,x) equal distances
 * from (a,e) to (b, x^-1 y), so BFS from the 2p fibre representatives decides diameter <= D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXGN 1024
#define MAXV 4096
#define MAXD 32
#define MAXP 3
#define MAXND (MAXP * MAXD)
#define MAXE 300000
#define MAXGL 4096

static int d, D;
static long moore;
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

/* Best graph so far (start or found lift). */
static int best_n = 0, best_m = 0;
static int BU[MAXE], BV[MAXE];
static int TU[MAXE], TV[MAXE];

static void read_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m <= 0 || m > MAXE) return;
    for (int e = 0; e < m; e++) {
        if (scanf("%d %d", &BU[e], &BV[e]) != 2) return;
        if (BU[e] < 0 || BV[e] < 0 || BU[e] >= n || BV[e] >= n) return;
    }
    best_n = n;
    best_m = m;
}

static void print_best(void) {
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", BU[e], BV[e]);
}

/* ---------------- groups Z_m x|_r Z_k, element a*k+b ---------------- */
static int MT[MAXGN][MAXGN];
static int rpw[MAXGN];
static int NN;      /* current group order */
static int P_;      /* current base half-size p */

typedef struct { int m, k, r; } GDesc;
static GDesc GL[MAXGL];
static int ngl;

static void enum_groups(int N) {
    ngl = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ngl < MAXGL) { GL[ngl].m = 1; GL[ngl].k = k; GL[ngl].r = 0; ngl++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngl < MAXGL) { GL[ngl].m = m; GL[ngl].k = k; GL[ngl].r = r; ngl++; }
        }
    }
}

static void build_table(int m, int k, int r, int N) {
    rpw[0] = 1 % m;
    for (int b = 1; b < k; b++) rpw[b] = (int)((long)rpw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((((long)a + (long)rpw[b] * c) % m) * k + (b + e) % k);
        }
    }
}

/* ---------------- darts and adjacency ---------------- */
static int ND;
static int DI[MAXND], DJ[MAXND], DG[MAXND];
static int NBR[MAXV][MAXD];
static int CNT[MAXV];
static int NV;
static int DIST[MAXV], QU[MAXV];

static int clash(int t, int g) {
    for (int u = 0; u < ND; u++)
        if (u != t && DI[u] == DI[t] && DJ[u] == DJ[t] && DG[u] == g) return 1;
    return 0;
}

/* Random d-regular bipartite base on p+p vertices, sum of d permutations; voltages distinct
 * within each (i,j) pair. Needs NN >= d. */
static void make_darts(int p) {
    ND = 0;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            DI[ND] = i; DJ[ND] = perm[i]; DG[ND] = -1; ND++;
        }
    }
    for (int t = 0; t < ND; t++) {
        int g;
        do { g = rndint(NN); } while (clash(t, g));
        DG[t] = g;
    }
}

static void build_adj(void) {
    int p = P_, N = NN;
    NV = 2 * p * N;
    for (int v = 0; v < NV; v++) CNT[v] = 0;
    for (int t = 0; t < ND; t++) {
        int i = DI[t], j = DJ[t], g = DG[t];
        for (int x = 0; x < N; x++) {
            int u = i * N + x;
            int v = (p + j) * N + MT[x][g];
            NBR[u][CNT[u]++] = v;
            NBR[v][CNT[v]++] = u;
        }
    }
}

/* Vertices at distance > D from src. */
static long bfs_bad(int src) {
    for (int v = 0; v < NV; v++) DIST[v] = -1;
    int h = 0, tl = 0;
    DIST[src] = 0;
    QU[tl++] = src;
    while (h < tl) {
        int v = QU[h++];
        if (DIST[v] >= D) continue;
        for (int k = 0; k < d; k++) {
            int u = NBR[v][k];
            if (DIST[u] < 0) {
                DIST[u] = DIST[v] + 1;
                QU[tl++] = u;
            }
        }
    }
    return NV - tl;
}

static long orbit_bad(void) {
    long s = 0;
    for (int a = 0; a < 2 * P_; a++) s += bfs_bad(a * NN);
    return s;
}

/* Anneal voltages until orbit_bad == 0 or limits reached. Returns remaining bad count. */
static long sa_run(double until, long maxsteps) {
    build_adj();
    long bad = orbit_bad();
    double T = 2.0;
    for (long s = 0; s < maxsteps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(ND);
        int old = DG[t];
        int g = rndint(NN);
        if (g == old || clash(t, g)) continue;
        DG[t] = g;
        build_adj();
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            DG[t] = old;
            build_adj();
        }
        T *= 0.9995;
        if (T < 0.2) T = 2.0;
    }
    return bad;
}

/* Store the current lift (must have bad == 0) if it beats the best order. */
static void store_lift(void) {
    int p = P_, N = NN, m = 0;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++) {
            TU[m] = DI[t] * N + x;
            TV[m] = (p + DJ[t]) * N + MT[x][DG[t]];
            m++;
        }
    int n = 2 * p * N;
    if (n > best_n) {
        best_n = n;
        best_m = m;
        memcpy(BU, TU, sizeof(int) * (size_t)m);
        memcpy(BV, TV, sizeof(int) * (size_t)m);
    }
}

/* Repeatedly pick a random group of a target order just above the best and try to lift. */
static void lift_search(double until) {
    while (now() < until) {
        long target = (long)best_n + 2;
        if (target > moore) return;
        int r = rndint(10);
        int p = r < 6 ? 1 : (r < 9 ? 2 : 3);
        long Nmin = (target + 2L * p - 1) / (2L * p);
        if (Nmin < d) Nmin = d;
        long Nl = Nmin + rndint(3);
        if (2L * p * Nl > moore || Nl > MAXGN || 2L * p * Nl > MAXV) {
            p = 1;
            Nl = Nmin + rndint(2);
            if (2L * Nl > moore || Nl > MAXGN || Nl < d) continue;
        }
        P_ = p;
        NN = (int)Nl;
        enum_groups(NN);
        if (ngl == 0) continue;
        GDesc G = GL[rndint(ngl)];
        build_table(G.m, G.k, G.r, NN);
        double att = now() + 3.0;
        if (att > until) att = until;
        int ok = 0;
        for (int a = 0; a < 4 && !ok && now() < att; a++) {
            make_darts(p);
            if (sa_run(att, 150000) == 0) {
                store_lift();
                ok = 1;
            }
        }
    }
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start();
    if (d < 1 || d > MAXD || D < 2) {
        if (best_n == 0) { printf("0 0\n"); return 0; }
        print_best();
        return 0;
    }
    moore = moore_bound();
    if (best_n < moore) lift_search(t_end);
    if (best_n == 0) { printf("0 0\n"); return 0; }
    print_best();
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
