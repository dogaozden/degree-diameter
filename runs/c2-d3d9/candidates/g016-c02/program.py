"""Multi-orbit voltage lifts over metacyclic groups, optimised by simulated annealing.

New construction (not used by the parent): take a bipartite base multigraph with
K vertices per side that is d-regular, given as d perfect matchings sigma_t between
the two sides. Give each dart (i, t) a voltage v[i][t] in a group G of order N.
The lift has vertices A_{i,x} and B_{j,y} (i, j < K, x, y in G) and edges

    A_{i,x} ~ B_{sigma_t(i), x * v[i][t]}   for t = 0..d-1.

Left multiplication by any h in G is an automorphism, so each fibre is one orbit.
The lift therefore has diameter <= D iff every representative A_{i,1} and B_{j,1}
reaches all vertices within D steps. That is 2K BFS runs, not 2KN.

The cost of a state is the number of (representative, vertex) pairs at distance
greater than D. Simulated annealing moves single voltages and swaps matching
targets until the cost is 0. A valid state is rebuilt explicitly, dedupes parallel
edges (distances are unchanged), is fully re-verified when small, and is printed.

Groups are Z_m x| Z_k, with nonabelian ones preferred. The target order rises after
each success, starting from about 0.45 of the Moore bound. Python keeps the best of
the known start and the C result, and checks everything with lib.is_valid.
"""
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

#define MAXN 512
#define MAXK 16
#define MAXD 16
#define MAXV (2 * MAXK * MAXN)
#define MAXGRP 4096

typedef struct { int m, k, r; } Grp;

static int dd, DIAM, K, GN;
static double t_end;

static int MT[MAXN * MAXN];
static int INV[MAXN];
static int perm[MAXD][MAXK], pinv[MAXD][MAXK], volt[MAXK][MAXD];

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
    if (DIAM <= 0 || dd <= 0) return 1;
    if (dd == 1) return 2;
    if (dd == 2) return 2L * DIAM;
    long s = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        s += p;
        p *= (dd - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------------------------------------------------------- groups Z_m x| Z_k */

static Grp groups[MAXGRP];
static int ngroups;

static void addg(int m, int k, int r) {
    if (ngroups < MAXGRP) {
        groups[ngroups].m = m;
        groups[ngroups].k = k;
        groups[ngroups].r = r;
        ngroups++;
    }
}

/* Nonabelian groups (r > 1) come first, then abelian ones. Element (a,b) = a*k+b. */
static void enum_groups(int n) {
    ngroups = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1) addg(1, k, 0);
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                addg(m, k, r);
            }
        }
    }
}

static void build_group(Grp G) {
    int n = G.m * G.k;
    GN = n;
    static int rp[MAXN];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++) {
        INV[x] = -1;
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
    }
}

/* ---------------------------------------------------------- lift state */

static void set_pinv(void) {
    for (int t = 0; t < dd; t++)
        for (int i = 0; i < K; i++)
            pinv[t][perm[t][i]] = i;
}

/* Random d matchings between the two K-sets, and random voltages. */
static void init_state(void) {
    for (int t = 0; t < dd; t++) {
        for (int i = 0; i < K; i++) perm[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[t][i];
            perm[t][i] = perm[t][j];
            perm[t][j] = tmp;
        }
    }
    set_pinv();
    for (int i = 0; i < K; i++)
        for (int t = 0; t < dd; t++)
            volt[i][t] = rndint(GN);
}

/* ---------------------------------------------------------- representative BFS */

static unsigned vis[MAXV];
static unsigned gen = 0;
static int dep[MAXV], qb[MAXV];

/* Number of vertices within DIAM of src. Vertex A_{i,x} = i*GN+x, B_{j,y} = K*GN + j*GN + y. */
static int bfs_reach(int src) {
    int nS = K * GN;
    if (++gen == 0) { memset(vis, 0, sizeof vis); gen = 1; }
    int head = 0, tail = 0;
    vis[src] = gen;
    dep[src] = 0;
    qb[tail++] = src;
    while (head < tail) {
        int v = qb[head++];
        int dv = dep[v];
        if (dv >= DIAM) continue;
        if (v < nS) {
            int i = v / GN, x = v % GN;
            for (int t = 0; t < dd; t++) {
                int j = perm[t][i];
                int y = MT[x * GN + volt[i][t]];
                int u = nS + j * GN + y;
                if (vis[u] != gen) { vis[u] = gen; dep[u] = dv + 1; qb[tail++] = u; }
            }
        } else {
            int w = v - nS;
            int j = w / GN, y = w % GN;
            for (int t = 0; t < dd; t++) {
                int i = pinv[t][j];
                int x = MT[y * GN + INV[volt[i][t]]];
                int u = i * GN + x;
                if (vis[u] != gen) { vis[u] = gen; dep[u] = dv + 1; qb[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Number of (representative, vertex) pairs at distance > DIAM. Zero iff the lift is valid. */
static long cost_of(void) {
    int V = 2 * K * GN;
    long c = 0;
    for (int i = 0; i < K; i++) {
        c += V - bfs_reach(i * GN);
        c += V - bfs_reach(K * GN + i * GN);
    }
    return c;
}

/* ---------------------------------------------------------- annealing */

static int sa_attempt(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0) return 0;
    long c = cost_of();
    double T = 1.5;
    long it = 0;
    while (c > 0) {
        if ((it & 127) == 0) {
            double tn = now();
            if (tn >= until) break;
            double f = (tn - start) / span;
            T = 1.5 * pow(0.08 / 1.5, f);
        }
        it++;
        if (rndint(100) < 85) {
            int i = rndint(K), t = rndint(dd);
            int old = volt[i][t];
            int nv = rndint(GN);
            if (nv == old) continue;
            volt[i][t] = nv;
            long nc = cost_of();
            long dl = nc - c;
            if (dl <= 0 || rnd01() < exp(-(double)dl / T)) c = nc;
            else volt[i][t] = old;
        } else {
            if (K < 2) continue;
            int t = rndint(dd);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int j1 = perm[t][i1], j2 = perm[t][i2];
            perm[t][i1] = j2;
            perm[t][i2] = j1;
            pinv[t][j2] = i1;
            pinv[t][j1] = i2;
            long nc = cost_of();
            long dl = nc - c;
            if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
                c = nc;
            } else {
                perm[t][i1] = j1;
                perm[t][i2] = j2;
                pinv[t][j1] = i1;
                pinv[t][j2] = i2;
            }
        }
    }
    return c == 0;
}

/* ---------------------------------------------------------- explicit graph */

static int adjl[MAXV][MAXD], degl[MAXV];
static int EU[MAXV * MAXD], EV[MAXV * MAXD];

/* Build the simple graph (duplicates removed) and verify it when small. Returns 1 on success. */
static int build_explicit(int *outm) {
    int nS = K * GN, V = 2 * nS;
    for (int v = 0; v < V; v++) degl[v] = 0;
    int m = 0;
    for (int i = 0; i < K; i++)
        for (int x = 0; x < GN; x++) {
            int u = i * GN + x;
            for (int t = 0; t < dd; t++) {
                int j = perm[t][i];
                int y = MT[x * GN + volt[i][t]];
                int v = nS + j * GN + y;
                int dup = 0;
                for (int q = 0; q < degl[u]; q++)
                    if (adjl[u][q] == v) { dup = 1; break; }
                if (dup) continue;
                if (degl[u] >= dd || degl[v] >= dd) return 0;
                adjl[u][degl[u]++] = v;
                adjl[v][degl[v]++] = u;
                EU[m] = u;
                EV[m] = v;
                m++;
            }
        }
    for (int v = 0; v < V; v++)
        if (degl[v] < 1 || degl[v] > dd) return 0;

    if (V <= 2500) {
        static int dist[MAXV], qq[MAXV];
        for (int s = 0; s < V; s++) {
            for (int i = 0; i < V; i++) dist[i] = -1;
            int head = 0, tail = 0;
            dist[s] = 0;
            qq[tail++] = s;
            while (head < tail) {
                int v = qq[head++];
                if (dist[v] >= DIAM) continue;
                for (int q = 0; q < degl[v]; q++) {
                    int u = adjl[v][q];
                    if (dist[u] < 0) { dist[u] = dist[v] + 1; qq[tail++] = u; }
                }
            }
            if (tail != V) return 0;
        }
    }
    *outm = m;
    return 1;
}

/* ---------------------------------------------------------- main */

static Grp bestGrp;
static int bestV = 0, bestK = 0;
static int bestPerm[MAXD][MAXK], bestVolt[MAXK][MAXD];

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget target\n", argv[0]);
        return 2;
    }
    dd = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int target = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (dd < 2 || dd > MAXD || DIAM < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long moore = moore_bound();
    if (moore > MAXV) moore = MAXV;
    if (target < 2) target = 2;

    double slice = budget / 8.0;
    if (slice < 1.0) slice = 1.0;
    if (slice > 8.0) slice = 8.0;

    static const int kl[] = {2, 3, 1, 4, 2, 6, 3, 5, 8, 2, 4, 3};
    const int nk = 12;
    int attempt = 0, skips = 0;

    while (now() < t_end) {
        if (target > moore) break;
        int k = kl[attempt % nk];
        attempt++;
        int N = (target + 2 * k - 1) / (2 * k);
        if (N < 1) N = 1;
        long V = 2L * k * N;
        if (N > MAXN || k > MAXK || V > moore || V > MAXV) {
            if (++skips >= nk) break;
            continue;
        }
        skips = 0;
        K = k;
        enum_groups(N);
        if (ngroups == 0) continue;
        int nn = 0;
        while (nn < ngroups && groups[nn].r > 1) nn++;
        int gi;
        if (nn > 0 && rndint(10) < 8) gi = rndint(nn);
        else gi = rndint(ngroups);
        build_group(groups[gi]);
        init_state();

        double until = now() + slice;
        if (until > t_end) until = t_end;
        if (sa_attempt(until)) {
            int VV = 2 * K * GN;
            if (VV > bestV) {
                bestV = VV;
                bestK = K;
                bestGrp = groups[gi];
                memcpy(bestPerm, perm, sizeof perm);
                memcpy(bestVolt, volt, sizeof volt);
            }
            target = VV + 1;
        }
    }

    if (bestV == 0) { printf("0 0\n"); return 0; }

    K = bestK;
    build_group(bestGrp);
    memcpy(perm, bestPerm, sizeof perm);
    memcpy(volt, bestVolt, sizeof volt);
    set_pinv();
    int m = 0;
    if (!build_explicit(&m)) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * K * GN, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", EU[e], EV[e]);
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
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    # Start the climb at about 0.45 of the Moore bound; the C side raises the target after each success.
    target = max(best[0] + 1, int(0.45 * moore))
    if target > moore:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), target],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
