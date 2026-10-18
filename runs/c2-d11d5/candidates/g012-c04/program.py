"""Bi-Cayley lift search moved into C, with constructive fallbacks.

Change of approach for weak targets: the whole voltage-lift search runs inside a C engine.
Lifts are over semidirect products Z_m x| Z_k2 with k base vertices per side. Left
multiplication by the group is an automorphism, so distances are checked from only the 2k
block representatives (one BFS each), and each annealing move updates only the changed darts.
Every returned graph is checked with lib.is_valid. Fallbacks: K_{d,d}, C_{2D} for d=2,
projective-plane and quadrangle incidence graphs, and the Araujo-Lopez graph.
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

#define MAXN 12288
#define MAXD 40
#define MAXK 6
#define MAXG 12288
#define MAXE 250000

static int d, D;
static int K, G, N;
static int gm, gk2;
static int gpw[64];
static int perm[MAXD][MAXK + 1];
static int S[MAXD][MAXK + 1];
static int nb[MAXN * MAXD];
static int distv[MAXN], stampv[MAXN], queue_[MAXN];
static int curstamp = 0;
static uint64_t rs = 88172645463325252ULL;
static int bestN = 0, bestM = 0;
static int bu[MAXE], bv[MAXE];
static int rvalid[MAXG];
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static void swap_int(int *a, int *b) { int t = *a; *a = *b; *b = t; }

/* Group Z_m x| Z_k2 with r^k2 = 1 mod m; element (a,b) is coded as a*k2 + b. */
static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    G = m * k2;
    gpw[0] = 1 % m;
    for (int t = 1; t < k2; t++) gpw[t] = (int)((long)gpw[t - 1] * r % m);
}
static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long t = (a + (long)gpw[b] * c) % gm;
    return (int)(t * gk2 + (b + e) % gk2);
}
static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nbk = (gk2 - b) % gk2;
    long t = ((long)((gm - gpw[nbk]) % gm) * a) % gm;
    return (int)(t * gk2 + nbk);
}

static const int K2C[] = {1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 10, 12, 14, 15, 16, 18, 20, 24};
#define NK2 ((int)(sizeof(K2C) / sizeof(K2C[0])))

/* Pick a random semidirect group with order close to targetG. */
static int sample_group(int targetG) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2C[rndint(NK2)];
        int m = (targetG + k2 - 1) / k2 + rndint(3);
        if (m < 2) m = 2;
        if (m * k2 > MAXG) continue;
        int nv = 0;
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            long x = 1;
            for (int t = 0; t < k2; t++) x = x * r % m;
            if (x == 1 % m) rvalid[nv++] = r;
        }
        if (nv == 0) continue;
        set_group(m, k2, rvalid[rndint(nv)]);
        return 1;
    }
    return 0;
}

/* Dart (layer l, base A-block i): A(i,g) ~ B(perm[l][i], g*s), s = S[l][i]. */
static void set_dart(int l, int i) {
    int p = perm[l][i], s = S[l][i];
    int si = ginv(s);
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        nb[(Ab + g) * d + l] = Bb + gmul(g, s);
        nb[(Bb + g) * d + l] = Ab + gmul(g, si);
    }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            swap_int(&perm[l][i], &perm[l][j]);
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Vertices reached within distance D from src. */
static int reach_count(int src) {
    curstamp++;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    stampv[src] = curstamp;
    distv[src] = 0;
    while (head < tail) {
        int v = queue_[head++];
        if (distv[v] >= D) continue;
        const int *row = &nb[v * d];
        for (int l = 0; l < d; l++) {
            int u = row[l];
            if (stampv[u] != curstamp) {
                stampv[u] = curstamp;
                distv[u] = distv[v] + 1;
                queue_[tail++] = u;
            }
        }
    }
    return tail;
}

/* Unreached pairs summed over block representatives. Zero means valid. */
static long eval_cost(void) {
    long c = 0;
    for (int b = 0; b < 2 * K; b++) c += N - reach_count(b * G);
    return c;
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < K * G; u++) {
        for (int l = 0; l < d; l++) {
            int v = nb[u * d + l];
            int dup = 0;
            for (int l2 = 0; l2 < l; l2++)
                if (nb[u * d + l2] == v) { dup = 1; break; }
            if (!dup) {
                if (m < MAXE) { bu[m] = u; bv[m] = v; }
                m++;
            }
        }
    }
    bestM = m;
    bestN = N;
}

/* Simulated annealing over voltages and layer permutations. Returns final cost. */
static long run_sa(double deadline, long patience) {
    random_state();
    long cost = eval_cost();
    long bestc = cost, last = 0;
    for (long t = 0; cost > 0; t++) {
        if ((t & 31) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.3 + 0.08 * (double)cost;
        double x = rnd01();
        if (K >= 2 && x < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_int(&perm[l][i1], &perm[l][i2]);
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                swap_int(&perm[l][i1], &perm[l][i2]);
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i], nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; }
    }
    return cost;
}

static double moore_bound_d(void) {
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    return 2.0 * s;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [init_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int init_n = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.97 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    bestN = init_n;
    bestM = 0;
    if (d < 3 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    double mb = moore_bound_d();
    int trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }

    while (now() < t_end - 0.3) {
        int bk = 1;
        double bs = -1.0;
        for (int k = 1; k <= MAXK; k++) {
            double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.15 * rnd01();
            if (sc > bs) { bs = sc; bk = k; }
        }
        K = bk;
        int target = bestN + 2 + rndint(1 + bestN / 120);
        int targetG = (target + 2 * K - 1) / (2 * K);
        if (!sample_group(targetG)) { trials[K]++; continue; }
        N = 2 * K * G;
        if (N <= bestN || N > MAXN || (double)N > mb) { trials[K]++; continue; }
        trials[K]++;
        double rem = t_end - now();
        double slice = rem / 4.0;
        if (slice < 1.5) slice = 1.5;
        if (slice > 12.0) slice = 12.0;
        double dl = now() + slice;
        if (dl > t_end) dl = t_end;
        if (run_sa(dl, 3000) == 0) {
            wins[K]++;
            save_best();
        }
    }

    if (bestM > 0) {
        printf("%d %d\n", bestN, bestM);
        for (int i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Constructive fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _cycle(D):
    """Cycle C_{2D}: bipartite, 2-regular, diameter D."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best
    if d == 2:
        consider(*_cycle(D))
        return best

    # Exact constructions.
    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    except Exception:
        pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: bi-Cayley lift search inside C.
    total = 0.85 * time_limit - 2.0
    remaining = total - (time.monotonic() - t0)
    if remaining > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             stdin_graph=None, timeout=remaining + 4)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
