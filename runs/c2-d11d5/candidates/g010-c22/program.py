"""Bi-Cayley lift annealer in C over metacyclic groups Z_m x| Z_k2.

Exact constructions (projective planes, Araujo-Pardo-Lopez, W(q), cycles, K_{d,d}) are built in
Python. The main search is a C engine. It samples a group of order about goal/(2k) and k base
vertices per side. It places d permutation layers with group voltages, then anneals the voltages
and permutations. Reachability is tracked with one 64-bit mask per vertex: bit c is set when block
representative c is within distance D. Layers are refreshed incrementally, and groups come from
enumerating the roots r with r^k2 = 1 mod m. Every returned graph is checked with lib.is_valid.
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

#define MAXK 4
#define MAXD 24
#define MAXG 20000
#define MAXV 40000
#define PEN 1000L

static int d, D;
static int K, G, Nv;
static int gm, gk, grp_r;
static int rpow[16];
static int GA[MAXG], GB[MAXG];
static int layerP[MAXD][MAXK], invP[MAXD][MAXK];
static int volt[MAXD][MAXK], invV[MAXD][MAXK];
static int nbr[MAXV * MAXD];
static uint64_t bufX[MAXV], bufY[MAXV], curR[MAXV], outR[MAXV];
static uint64_t rng_state = 88172645463325252ULL;

static int bK, bNv, bGm, bGk, bR;
static int bLayerP[MAXD][MAXK], bVolt[MAXD][MAXK];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int pc(uint64_t x) { return __builtin_popcountll(x); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x| Z_k2 with (a,b)*(c,e) = (a + r^b c, b + e); element (a,b) is coded a*k2+b. */
static void set_group(int m, int k2, int r) {
    gm = m;
    gk = k2;
    G = m * k2;
    grp_r = r;
    rpow[0] = 1 % m;
    for (int t = 1; t < k2; t++) rpow[t] = (int)((long long)rpow[t - 1] * r % m);
    for (int x = 0; x < G; x++) { GA[x] = x / k2; GB[x] = x % k2; }
}

static int gmul(int x, int y) {
    int a = GA[x], b = GB[x], c = GA[y], e = GB[y];
    int t = (int)(((long long)rpow[b] * c) % gm);
    int aa = a + t;
    if (aa >= gm) aa -= gm;
    int bb = b + e;
    if (bb >= gk) bb -= gk;
    return aa * gk + bb;
}

static int ginv(int x) {
    int a = GA[x], b = GB[x];
    int nb = (gk - b) % gk;
    int c = (int)((gm - ((long long)rpow[nb] * a) % gm) % gm);
    return c * gk + nb;
}

/* Vertices: A_{i,g} = i*G+g, B_{p,h} = (K+p)*G+h. Layer l joins A_{i,g} to B_{layerP[l][i], g*volt}. */
static void refresh_layer(int l) {
    for (int i = 0; i < K; i++) {
        int p = layerP[l][i], s = volt[l][i];
        invP[l][p] = i;
        invV[l][i] = ginv(s);
        for (int g = 0; g < G; g++)
            nbr[(i * G + g) * d + l] = (K + p) * G + gmul(g, s);
    }
    for (int p = 0; p < K; p++) {
        int i = invP[l][p], si = invV[l][i];
        for (int h = 0; h < G; h++)
            nbr[((K + p) * G + h) * d + l] = i * G + gmul(h, si);
    }
}

/* Repeated (i, p, s) triples across layers: these would produce multi-edges. */
static int dup_count(void) {
    int dup = 0;
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            for (int i = 0; i < K; i++)
                if (layerP[l1][i] == layerP[l2][i] && volt[l1][i] == volt[l2][i]) dup++;
    return dup;
}

/* Cost = unreached (block representative, vertex) pairs + PEN * duplicates. Writes the reach masks to res. */
static long eval_cost(uint64_t *res) {
    int N = Nv;
    uint64_t *a = bufX, *b = bufY;
    memset(a, 0, sizeof(uint64_t) * (size_t)N);
    for (int c = 0; c < 2 * K; c++) a[(size_t)c * G] = 1ULL << c;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = a[v];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= a[nb[l]];
            b[v] = x;
            changed |= (x != a[v]);
        }
        uint64_t *t = a; a = b; b = t;
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += 2 * K - pc(a[v]);
    memcpy(res, a, sizeof(uint64_t) * (size_t)N);
    return unreached + PEN * (long)dup_count();
}

static int accept(long c2, long c, double temp) {
    if (c2 <= c) return 1;
    return rnd01() < exp(-(double)(c2 - c) / temp);
}

static long anneal(long maxit, long patience, double deadline) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layerP[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), t = layerP[l][i];
            layerP[l][i] = layerP[l][j];
            layerP[l][j] = t;
        }
        for (int i = 0; i < K; i++) volt[l][i] = rndint(G);
        refresh_layer(l);
    }
    long cost = eval_cost(outR);
    memcpy(curR, outR, sizeof(uint64_t) * (size_t)Nv);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < maxit && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)maxit);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layerP[l][i1];
            layerP[l][i1] = layerP[l][i2];
            layerP[l][i2] = tmp;
            refresh_layer(l);
            long c2 = eval_cost(outR);
            if (accept(c2, cost, temp)) {
                cost = c2;
                memcpy(curR, outR, sizeof(uint64_t) * (size_t)Nv);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = layerP[l][i1];
                layerP[l][i1] = layerP[l][i2];
                layerP[l][i2] = tmp;
                refresh_layer(l);
            }
            continue;
        }

        int v = -1;
        if (rnd01() < 0.4) {
            for (int tries = 0; tries < 30; tries++) {
                int x = rndint(Nv);
                if (pc(curR[x]) < 2 * K) { v = x; break; }
            }
        }
        int l, i = -1;
        if (v >= 0) {
            int c = v / G;
            l = rndint(d);
            if (c < K) i = c;
            else {
                for (int ii = 0; ii < K; ii++)
                    if (layerP[l][ii] == c - K) i = ii;
            }
        } else {
            l = rndint(d);
            i = rndint(K);
        }
        if (i < 0) continue;

        int old = volt[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        volt[l][i] = nw;
        refresh_layer(l);
        long c2 = eval_cost(outR);
        if (accept(c2, cost, temp)) {
            cost = c2;
            memcpy(curR, outR, sizeof(uint64_t) * (size_t)Nv);
            if (cost < best) { best = cost; last = t; }
        } else {
            volt[l][i] = old;
            refresh_layer(l);
        }
    }
    return cost;
}

static void save_best(void) {
    bK = K;
    bNv = Nv;
    bGm = gm;
    bGk = gk;
    bR = grp_r;
    memcpy(bLayerP, layerP, sizeof(layerP));
    memcpy(bVolt, volt, sizeof(volt));
}

static void print_best(void) {
    K = bK;
    set_group(bGm, bGk, bR);
    Nv = bNv;
    if (Nv != 2 * K * G) { printf("0 0\n"); return; }
    memcpy(layerP, bLayerP, sizeof(layerP));
    memcpy(volt, bVolt, sizeof(volt));
    for (int l = 0; l < d; l++) refresh_layer(l);
    if (eval_cost(outR) != 0) { printf("0 0\n"); return; }
    printf("%d %ld\n", Nv, (long)Nv * d / 2);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[v * d + l]);
}

static int pick_K(long *trials, long *wins) {
    if (rnd01() < 0.2) return 1 + rndint(4);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= 4; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_goal]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double start_goal = argc > 5 ? atof(argv[5]) : 0.0;
    double t0 = now();
    double t_end = t0 + limit * 0.97 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    static const int K2S[] = {1, 1, 2, 2, 3, 4, 4, 5, 6, 6, 8, 9, 10, 12};
    const int nK2 = (int)(sizeof(K2S) / sizeof(K2S[0]));
    long trials[5] = {0, 0, 0, 0, 0}, wins[5] = {0, 0, 0, 0, 0};
    double goal = start_goal > 0 ? start_goal : 2.0 * d;
    const double cap = MAXV * 0.95;
    long bestN = 0;

    while (now() < t_end) {
        int Kc = pick_K(trials, wins);
        long target = (long)(goal / (2.0 * Kc)) + rndint(3);
        if (target < 2) target = 2;
        int k2 = K2S[rndint(nK2)];
        int m = (int)((target + k2 - 1) / k2);
        if (m < 2) m = 2;

        int ok = 0, rr = 1;
        for (int attempt = 0; attempt < 8 && !ok; attempt++) {
            if (k2 == 1) { rr = 1; ok = 1; break; }
            int cands[512], nc = 0;
            for (int r = 1; r < m && nc < 512; r++)
                if (gcd_i(r, m) == 1 && powmod_l(r, k2, m) == 1 % m) cands[nc++] = r;
            if (nc > 0) { rr = cands[rndint(nc)]; ok = 1; }
            else m++;
        }
        if (!ok) { goal *= 0.99; continue; }
        if ((long)2 * Kc * m * k2 > MAXV) { goal *= 0.97; continue; }
        if ((long)2 * Kc * m * k2 <= bestN) { goal = bestN * 1.02 + 1.0; continue; }

        set_group(m, k2, rr);
        K = Kc;
        Nv = 2 * K * G;
        trials[K]++;
        long c = anneal(6000, 1500, t_end);
        if (c == 0) {
            wins[K]++;
            if (Nv > bestN) {
                save_best();
                bestN = Nv;
            }
            if (goal < Nv * 1.04) goal = Nv * 1.04;
        } else {
            double alt = bestN * 1.02, dec = goal * 0.99;
            goal = alt > dec ? alt : dec;
        }
        if (goal > cap) goal = cap;
    }

    if (bestN == 0) printf("0 0\n");
    else print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # C bi-Cayley lift annealer over metacyclic groups, using the remaining time.
    remaining = final - time.monotonic() - 1.0
    if remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             timeout=remaining + 5)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
