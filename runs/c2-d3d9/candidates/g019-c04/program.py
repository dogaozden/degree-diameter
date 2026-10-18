"""Multi-orbit random voltage lifts over metacyclic groups (new in this version).

Parent idea: bi-Cayley graphs with one orbit per side, i.e. base = 2 vertices with d parallel
darts, voltages in a group of order n, total order 2n.

New idea: a base multigraph with b vertices per side (b = 1..4) and d darts out of each A-vertex.
Dart t out of A_i goes to B_{sigma_t(i)}, where sigma_1..sigma_d are random permutations of [b].
This gives a d-regular bipartite multigraph on b + b vertices, for any b. Each dart carries a
voltage in a metacyclic group G = Z_m x| Z_k of order n. The lift has total order 2*b*n, so
targets like 508 = 2*2*127 or 510 = 2*3*85 can be reached with groups of smaller order than the
b = 1 case needs (for b = 2, n = 127 gives 508 vertices, where b = 1 needs n = 254).

Each lift is simple (parallel darts get different voltages) and bipartite. Left multiplication by G
acts on every orbit, so the diameter check needs only b + b BFS runs, one from the identity of each
orbit. Voltages are normalised so the first dart out of each A_i is the identity. The C engine scans
total order T upward from a lower bound, spends a time slice on each T, and keeps the largest T that
succeeds. The final graph is re-verified with a BFS from every vertex before it is printed. If
nothing is found, the C program prints K_{d,d}. Python keeps the best of the known start and the C
result, and checks everything with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXT 1024
#define MAXN 512
#define MAXB 4
#define MAXDEG 16
#define MAXGRP 8192

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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
static Grp lists[MAXB + 1][MAXGRP];
static int cnts[MAXB + 1];

/* All metacyclic groups of order n (abelian ones have r = 1). Returns how many were written. */
static int enum_groups(int n, Grp *out, int cap) {
    int c = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (c < cap) { out[c].m = 1; out[c].k = k; out[c].r = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (c < cap) { out[c].m = m; out[c].k = k; out[c].r = r; c++; }
        }
    }
    return c;
}

static int MT[MAXN * MAXN];  /* multiplication table, element (a,b) coded a*k+b */
static int INV[MAXN];
static int NG;

static void build_group(Grp G) {
    int m = G.m, k = G.k, n = m * k;
    NG = n;
    int rp[MAXN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- lift configuration */

static int nb, nn;              /* base size per side, group order */
static int dj[MAXB][MAXDEG];    /* dart t out of A_i lands in B_{dj[i][t]} */
static int vg[MAXB][MAXDEG];    /* its voltage */

/* Random d-regular base multigraph (union of d permutations) plus random voltages.
 * Returns 0 if two parallel darts got the same voltage (the lift would not be simple). */
static int random_config(void) {
    int b = nb, n = nn;
    for (int t = 0; t < d; t++) {
        int p[MAXB];
        for (int i = 0; i < b; i++) p[i] = i;
        for (int i = b - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < b; i++) dj[i][t] = p[i];
    }
    for (int i = 0; i < b; i++)
        for (int t = 0; t < d; t++) vg[i][t] = rndint(n);
    /* Right-relabel each A_i so its first dart has voltage identity. */
    for (int i = 0; i < b; i++) {
        int ci = INV[vg[i][0]];
        for (int t = 0; t < d; t++) vg[i][t] = MT[ci * n + vg[i][t]];
    }
    for (int i = 0; i < b; i++)
        for (int t = 0; t < d; t++)
            for (int u = t + 1; u < d; u++)
                if (dj[i][t] == dj[i][u] && vg[i][t] == vg[i][u]) return 0;
    return 1;
}

static int adj[MAXT][MAXDEG];
static int deg[MAXT];
static int V_;

/* Explicit adjacency of the lift. A_{i,x} = i*n + x, B_{j,y} = b*n + j*n + y.
 * Edge A_{i,x} ~ B_{j, x*g} for each dart (i, t) with j = dj[i][t], g = vg[i][t]. */
static int build_adj(void) {
    int b = nb, n = nn;
    V_ = 2 * b * n;
    for (int v = 0; v < V_; v++) deg[v] = 0;
    for (int i = 0; i < b; i++)
        for (int x = 0; x < n; x++) {
            int A = i * n + x;
            for (int t = 0; t < d; t++) {
                int B = b * n + dj[i][t] * n + MT[x * n + vg[i][t]];
                if (deg[A] >= d || deg[B] >= d) return 0;
                adj[A][deg[A]++] = B;
                adj[B][deg[B]++] = A;
            }
        }
    return 1;
}

static int dist_[MAXT], q_[MAXT];

/* 1 iff every vertex is within D of src. */
static int bfs_full(int src) {
    int V = V_;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    q_[t++] = src;
    while (h < t) {
        int v = q_[h++];
        if (dist_[v] >= D) continue;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; q_[t++] = u; }
        }
    }
    return t == V;
}

/* Left multiplication is an automorphism transitive on each orbit, so checking the
 * identity of every orbit suffices. */
static int check_lift(void) {
    int b = nb, n = nn;
    for (int i = 0; i < b; i++)
        if (!bfs_full(i * n)) return 0;
    for (int j = 0; j < b; j++)
        if (!bfs_full(b * n + j * n)) return 0;
    return 1;
}

static int verify_full(void) {
    for (int v = 0; v < V_; v++) {
        if (deg[v] != d) return 0;
        for (int i = 0; i < d; i++)
            for (int j = i + 1; j < d; j++)
                if (adj[v][i] == adj[v][j]) return 0;
    }
    for (int s = 0; s < V_; s++)
        if (!bfs_full(s)) return 0;
    return 1;
}

/* ---------------------------------------------------------- search state */

static int best_T = 0, best_b, best_n;
static Grp best_G;
static int bdj[MAXB][MAXDEG], bvg[MAXB][MAXDEG];

static int try_group(Grp G, int b, int n, int attempts) {
    build_group(G);
    nb = b;
    nn = n;
    for (int a = 0; a < attempts; a++) {
        if (!random_config()) continue;
        if (!build_adj()) continue;
        if (check_lift()) {
            best_T = 2 * b * n;
            best_b = b;
            best_n = n;
            best_G = G;
            memcpy(bdj, dj, sizeof dj);
            memcpy(bvg, vg, sizeof vg);
            return 1;
        }
    }
    return 0;
}

static void set_complete(void) {
    int V = 2 * d;
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget tlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int tlo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    long tmax = moore_bound();
    if (tmax > MAXT) tmax = MAXT;
    int T0 = tlo;
    if (T0 < 2 * (d + 1)) T0 = 2 * (d + 1);
    if (T0 & 1) T0++;

    double slice = budget / 25.0;
    if (slice < 0.4) slice = 0.4;
    if (slice > 3.0) slice = 3.0;

    for (int T = T0; T <= tmax && now() < t_end; T += 2) {
        int cand[MAXB], nc = 0;
        for (int b = 1; b <= MAXB; b++) {
            if (T % (2 * b)) continue;
            int n = T / (2 * b);
            if (n < d || n > MAXN) continue;
            cnts[b] = enum_groups(n, lists[b], MAXGRP);
            if (cnts[b] > 0) cand[nc++] = b;
        }
        if (!nc) continue;
        double until = now() + slice;
        if (until > t_end) until = t_end;
        int found = 0;
        while (!found && now() < until) {
            int b = cand[rndint(nc)];
            int n = T / (2 * b);
            int gi = rndint(cnts[b]);
            found = try_group(lists[b][gi], b, n, 300);
        }
    }

    int ok = 0;
    if (best_T > 0) {
        nb = best_b;
        nn = best_n;
        build_group(best_G);
        memcpy(dj, bdj, sizeof dj);
        memcpy(vg, bvg, sizeof vg);
        if (build_adj() && verify_full()) {
            ok = 1;
            int b = nb, n = nn;
            long m = (long)b * n * d;
            printf("%d %ld\n", V_, m);
            for (int i = 0; i < b; i++)
                for (int x = 0; x < n; x++) {
                    int A = i * n + x;
                    for (int t = 0; t < d; t++) {
                        int B = b * n + dj[i][t] * n + MT[x * n + vg[i][t]];
                        printf("%d %d\n", A, B);
                    }
                }
        }
    }
    if (!ok) set_complete();
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    tmax = min(moore, 1024)
    # Lower bound for the scan on total order T = 2*b*n. The C side starts a little
    # below the record so that it re-finds known orders quickly before pushing upward.
    tlo = max(best[0] + 2, int(0.45 * moore))
    if tlo % 2:
        tlo += 1
    if tlo > tmax:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), tlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
