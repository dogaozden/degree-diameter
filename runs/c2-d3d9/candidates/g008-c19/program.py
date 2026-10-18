"""Voltage-lift search over metacyclic groups with simulated annealing on the voltages.

New idea (not in the parent): a bipartite graph of degree d is a lift of a base
multigraph B on P + P vertices (d-regular, built as a union of d random perfect
matchings, so parallel darts are allowed). Each dart (i, j) carries a voltage g in a
group G of order N, and the lift has vertices (A_i, x), (B_j, y) for x, y in G, with
edges (A_i, x) ~ (B_j, x g). The lift has 2 P N vertices and degree d.

Left multiplication by G is an automorphism, so each fibre is one orbit. The diameter
check therefore needs only 2P BFS runs, from A_i,1 and B_j,1. The number of
unreached (vertex, source) pairs is an integer objective, which simulated annealing
drives to zero by changing one voltage at a time. Voltages on darts between the same
pair of base vertices must differ, which keeps the lift simple.

The parent only uses P = 1 with 200 random sets per group. This version also tries
P = 2, 3, ... (orders 2PN, which can land between the parent's values) and anneals
the voltages instead of sampling them. A window of target orders above the current
best is swept, and the effort per attempt doubles each round that finds nothing.
Any success is re-verified by a full BFS from every vertex before it is printed.
If nothing beats the start, the C program prints "0 0" and Python keeps its fallback.
"""
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXV 1024
#define MAXP 8
#define MAXDEG 8
#define MAXDART (MAXP * MAXDEG)
#define MAXGRP 2048

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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp grps[MAXGRP];
static int ngrp;

static void enum_groups(int N) {
    ngrp = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ngrp < MAXGRP) { grps[ngrp].m = 1; grps[ngrp].k = k; grps[ngrp].r = 0; ngrp++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngrp < MAXGRP) { grps[ngrp].m = m; grps[ngrp].k = k; grps[ngrp].r = r; ngrp++; }
        }
    }
}

static int MT[MAXN * MAXN];
static int INV[MAXN];
static int NN;

/* Element (a, b) coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is 0. */
static void build_group(Grp G, int N) {
    NN = N;
    static int rp[MAXN];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < N; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < N; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * N + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- base multigraph and voltages */

static int P;                               /* base vertices per side */
static int da[MAXDART], db[MAXDART], vg[MAXDART];
static int incA[MAXP][MAXDEG], incB[MAXP][MAXDEG];
static int VV;                              /* lift vertex count 2*P*NN */

/* Random d-regular bipartite multigraph on P+P vertices: union of d random permutations. */
static void make_base(int p) {
    P = p;
    int cntB[MAXP];
    for (int j = 0; j < p; j++) cntB[j] = 0;
    int sig[MAXP];
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < p; i++) sig[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sig[i]; sig[i] = sig[j]; sig[j] = tmp;
        }
        for (int i = 0; i < p; i++) {
            int t = k * p + i;
            da[t] = i;
            db[t] = sig[i];
            incA[i][k] = t;
            int j = sig[i];
            incB[j][cntB[j]++] = t;
        }
    }
}

/* Voltage of dart t may not equal that of another dart t2 < upto with the same endpoints. */
static int ok_volt(int t, int g, int upto) {
    for (int s = 0; s < upto; s++)
        if (s != t && da[s] == da[t] && db[s] == db[t] && vg[s] == g) return 0;
    return 1;
}

static int init_volt(void) {
    int nd = P * d;
    for (int t = 0; t < nd; t++) {
        int placed = 0;
        for (int tries = 0; tries < 200 && !placed; tries++) {
            int g = rndint(NN);
            if (ok_volt(t, g, t)) { vg[t] = g; placed = 1; }
        }
        if (!placed) return 0;
    }
    return 1;
}

/* ---------------------------------------------------------- BFS on the lift */

static int stamp_a[MAXV];
static int stampc = 0;
static int dep[MAXV], qb[MAXV];

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    stampc++;
    int head = 0, tail = 0;
    int PN = P * NN;
    stamp_a[src] = stampc;
    dep[src] = 0;
    qb[tail++] = src;
    while (head < tail) {
        int v = qb[head++];
        int dv = dep[v];
        if (dv >= D) continue;
        if (v < PN) {
            int i = v / NN, x = v - i * NN;
            for (int k = 0; k < d; k++) {
                int t = incA[i][k];
                int w = PN + db[t] * NN + MT[x * NN + vg[t]];
                if (stamp_a[w] != stampc) { stamp_a[w] = stampc; dep[w] = dv + 1; qb[tail++] = w; }
            }
        } else {
            int idx = v - PN;
            int j = idx / NN, y = idx - j * NN;
            for (int k = 0; k < d; k++) {
                int t = incB[j][k];
                int w = da[t] * NN + MT[y * NN + INV[vg[t]]];
                if (stamp_a[w] != stampc) { stamp_a[w] = stampc; dep[w] = dv + 1; qb[tail++] = w; }
            }
        }
    }
    return tail;
}

/* Objective: unreached (vertex, source) pairs, sources = one vertex per fibre. 0 means valid. */
static int eval_bad(void) {
    int bad = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = (s < P) ? s * NN : P * NN + (s - P) * NN;
        bad += VV - bfs_reach(src);
    }
    return bad;
}

static int verify_full(void) {
    for (int s = 0; s < VV; s++)
        if (bfs_reach(s) != VV) return 0;
    return 1;
}

/* ---------------------------------------------------------- annealing on voltages */

static int attempt(int E) {
    if (!init_volt()) return 0;
    int nd = P * d;
    int f = eval_bad();
    if (f == 0) return 1;
    double T0 = 3.0, T1 = 0.2;
    for (int it = 0; it < E; it++) {
        if ((it & 63) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)E);
        int t = rndint(nd);
        int old = vg[t];
        int g = rndint(NN);
        if (g == old || !ok_volt(t, g, nd)) continue;
        vg[t] = g;
        int f2 = eval_bad();
        int df = f2 - f;
        if (df <= 0 || rnd01() < exp(-df / T)) {
            f = f2;
            if (f == 0) return 1;
        } else {
            vg[t] = old;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- search state */

static int bestV = 0, bestP = 0, bestN = 0;
static Grp bestG;
static int bestDa[MAXDART], bestDb[MAXDART], bestVg[MAXDART];

/* Try to find a valid lift on exactly V vertices. Returns 1 on success (stored in best*). */
static int try_V(int V, int E) {
    int found = 0;
    for (int p = 1; p <= MAXP && !found; p++) {
        if (V % (2 * p)) continue;
        int N = V / (2 * p);
        if (N < 2 || N > MAXN) continue;
        enum_groups(N);
        int ord[MAXGRP];
        for (int i = 0; i < ngrp; i++) ord[i] = i;
        for (int i = ngrp - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = ord[i]; ord[i] = ord[j]; ord[j] = tmp;
        }
        for (int q = 0; q < ngrp && !found; q++) {
            if (now() > t_end) return 0;
            Grp G = grps[ord[q]];
            build_group(G, N);
            make_base(p);
            VV = 2 * p * N;
            if (attempt(E)) {
                if (verify_full()) {
                    found = 1;
                    bestV = V; bestP = p; bestN = N; bestG = G;
                    memcpy(bestDa, da, sizeof(bestDa));
                    memcpy(bestDb, db, sizeof(bestDb));
                    memcpy(bestVg, vg, sizeof(bestVg));
                }
            }
        }
    }
    return found;
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget lo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int lo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long moore = moore_bound();
    int VMAX = (moore < MAXV) ? (int)moore : MAXV;
    VMAX -= VMAX % 2;
    if (lo < 2) lo = 2;
    lo += lo % 2;
    if (lo > VMAX) { printf("0 0\n"); return 0; }

    int cur_lo = lo;
    int E = 300;
    const int WIN = 6;
    while (now() < t_end && cur_lo <= VMAX) {
        int improved = 0;
        for (int w = 0; w < WIN && now() < t_end; w++) {
            int V = cur_lo + 2 * w;
            if (V > VMAX) break;
            if (try_V(V, E)) {
                improved = 1;
                cur_lo = bestV + 2;
                break;
            }
        }
        if (!improved && E < (1 << 22)) E *= 2;
    }

    if (bestV == 0) { printf("0 0\n"); return 0; }

    P = bestP;
    NN = bestN;
    VV = 2 * P * NN;
    memcpy(da, bestDa, sizeof(da));
    memcpy(db, bestDb, sizeof(db));
    memcpy(vg, bestVg, sizeof(vg));
    build_group(bestG, NN);
    int nd = P * d;
    printf("%d %d\n", VV, nd * NN);
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NN; x++) {
            int u = da[t] * NN + x;
            int w = P * NN + db[t] * NN + MT[x * NN + vg[t]];
            printf("%d %d\n", u, w);
        }
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 8:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    # Start the order window near 0.45 of the Moore bound, and above the current best.
    lo = max(2 * (best[0] // 2) + 2, int(0.45 * moore))
    lo += lo % 2

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
