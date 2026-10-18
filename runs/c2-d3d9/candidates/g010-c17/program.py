"""Bold variant: simulated annealing over voltage lifts of small bipartite base graphs.

Construction: pick a group G of order n (metacyclic Z_m x| Z_k) and a base
d-regular bipartite multigraph on K + K vertices, with K in {1,2,3,4}. Each base
dart (a_i, b_j, v) lifts to the edges (a_i, g) ~ (b_j, g v) for all g in G, giving a
d-regular bipartite graph on 2*K*n vertices. Left multiplication by G is an
automorphism, so the diameter check needs only BFS from the 2K identity
vertices. The cost is the number of vertices not within distance D of those
sources. Simulated annealing moves change one voltage or swap the B-endpoints of
two darts, and it stops when the cost reaches 0.

The vertex count V is scanned upward from a lower bound. Each V gets a time slice
with fresh random (K, group, base) restarts. The best valid lift is re-verified by
a full BFS from every vertex before it is printed. Python keeps the best of the
known start and the C result, and checks everything with lib.is_valid.
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

#define MAXG 1024
#define MAXV 2048
#define MAXDEG 16
#define MAXK 4
#define MAXDARTS (MAXK * MAXDEG)
#define MAXGRP 8192
#define ITERS 6000

static int d, D;

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
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* Largest possible number of vertices of a bipartite graph with max degree d, diameter D. */
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
static Grp groups[MAXGRP];
static int ngroups;

static void enum_groups(int n) {
    ngroups = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ngroups < MAXGRP) {
                groups[ngroups].m = 1;
                groups[ngroups].k = k;
                groups[ngroups].r = 0;
                ngroups++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXGRP) {
                groups[ngroups].m = m;
                groups[ngroups].k = k;
                groups[ngroups].r = r;
                ngroups++;
            }
        }
    }
}

static int MT[MAXG * MAXG]; /* multiplication table, current group */
static int INV[MAXG];
static int GN;              /* current group order; identity is element 0 */

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_group(Grp G) {
    int n = G.m * G.k;
    GN = n;
    static int rp[MAXG];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- lift state */

static int K;        /* base vertices per side */
static int NDART;    /* K * d darts */
static int da[MAXDARTS], db[MAXDARTS], dv[MAXDARTS];
static int bak_da[MAXDARTS], bak_db[MAXDARTS], bak_dv[MAXDARTS];
static int outl[MAXK][MAXDEG], outc[MAXK];
static int inl[MAXK][MAXDEG], inc[MAXK];

static void rebuild_lists(void) {
    for (int i = 0; i < K; i++) { outc[i] = 0; inc[i] = 0; }
    for (int t = 0; t < NDART; t++) {
        outl[da[t]][outc[da[t]]++] = t;
        inl[db[t]][inc[db[t]]++] = t;
    }
}

static void save_state(void) {
    memcpy(bak_da, da, sizeof(int) * (size_t)NDART);
    memcpy(bak_db, db, sizeof(int) * (size_t)NDART);
    memcpy(bak_dv, dv, sizeof(int) * (size_t)NDART);
}

static void restore_state(void) {
    memcpy(da, bak_da, sizeof(int) * (size_t)NDART);
    memcpy(db, bak_db, sizeof(int) * (size_t)NDART);
    memcpy(dv, bak_dv, sizeof(int) * (size_t)NDART);
}

static int dup_exists(void) {
    for (int t = 0; t < NDART; t++)
        for (int u = 0; u < t; u++)
            if (da[t] == da[u] && db[t] == db[u] && dv[t] == dv[u]) return 1;
    return 0;
}

/* Random d-regular bipartite base on K+K vertices; parallel darts get distinct voltages. */
static int random_base(void) {
    int A[MAXDARTS], B[MAXDARTS];
    for (int t = 0; t < NDART; t++) { A[t] = t / d; B[t] = t / d; }
    for (int t = NDART - 1; t > 0; t--) {
        int r = rndint(t + 1);
        int tmp = B[t]; B[t] = B[r]; B[r] = tmp;
    }
    for (int t = 0; t < NDART; t++) { da[t] = A[t]; db[t] = B[t]; dv[t] = rndint(GN); }
    for (int pass = 0; pass < 200; pass++) {
        int bad = 0;
        for (int t = 0; t < NDART; t++)
            for (int u = 0; u < t; u++)
                if (da[t] == da[u] && db[t] == db[u] && dv[t] == dv[u]) {
                    dv[t] = rndint(GN);
                    bad = 1;
                    break;
                }
        if (!bad) return 1;
    }
    return 0;
}

/* One random move. Returns 0 if nothing changed or the result was invalid (state restored). */
static int mutate(void) {
    int t1 = rndint(NDART), t2 = rndint(NDART);
    if (K >= 2 && rndu() < 0.5) {
        if (t1 == t2 || db[t1] == db[t2]) return 0;
        int tmp = db[t1]; db[t1] = db[t2]; db[t2] = tmp;
    } else {
        dv[t1] = rndint(GN);
    }
    if (dup_exists()) {
        restore_state();
        return 0;
    }
    return 1;
}

/* ---------------------------------------------------------- cost via BFS */

static int stamp_[MAXV], stampc = 0;
static int dist_[MAXV], queue_[MAXV];

/* Number of vertices within distance D of source src in the implicit lift. */
static int bfs_reach(int src) {
    int KN = K * GN;
    stampc++;
    int head = 0, tail = 0;
    stamp_[src] = stampc;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dz = dist_[v];
        if (dz >= D) continue;
        if (v < KN) {
            int i = v / GN, g = v - i * GN;
            for (int c = 0; c < outc[i]; c++) {
                int t = outl[i][c];
                int u = KN + db[t] * GN + MT[g * GN + dv[t]];
                if (stamp_[u] != stampc) {
                    stamp_[u] = stampc;
                    dist_[u] = dz + 1;
                    queue_[tail++] = u;
                }
            }
        } else {
            int off = v - KN;
            int j = off / GN, h = off - j * GN;
            for (int c = 0; c < inc[j]; c++) {
                int t = inl[j][c];
                int u = da[t] * GN + MT[h * GN + INV[dv[t]]];
                if (stamp_[u] != stampc) {
                    stamp_[u] = stampc;
                    dist_[u] = dz + 1;
                    queue_[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Sum over the 2K orbit representatives of the number of unreached vertices. */
static int eval_cost(void) {
    int V = 2 * K * GN, cost = 0;
    for (int i = 0; i < K; i++) {
        cost += V - bfs_reach(i * GN);
        cost += V - bfs_reach(K * GN + i * GN);
    }
    return cost;
}

/* ---------------------------------------------------------- annealing */

static int run_sa(int iters, double until) {
    const double T0 = 2.0, T1 = 0.15;
    rebuild_lists();
    int cur = eval_cost();
    if (cur == 0) return 1;
    for (int it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now() > until) break;
        double frac = (double)it / (double)iters;
        double T = T0 * pow(T1 / T0, frac);
        save_state();
        if (!mutate()) continue;
        rebuild_lists();
        int c = eval_cost();
        if (c <= cur || rndu() < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (cur == 0) return 1;
        } else {
            restore_state();
            rebuild_lists();
        }
    }
    return 0;
}

/* ---------------------------------------------------------- explicit graph */

static int adjl[MAXV][MAXDEG], degl[MAXV];
static int best_V = 0, best_E = 0;
static int best_eu[MAXV * MAXDEG / 2], best_ev[MAXV * MAXDEG / 2];

/* Build the explicit lift, check it fully, and store it if valid. */
static int store_if_valid(void) {
    int KN = K * GN;
    int V = 2 * KN;
    if (V > MAXV) return 0;
    for (int v = 0; v < V; v++) degl[v] = 0;
    for (int t = 0; t < NDART; t++)
        for (int g = 0; g < GN; g++) {
            int a = da[t] * GN + g;
            int b = KN + db[t] * GN + MT[g * GN + dv[t]];
            if (degl[a] >= MAXDEG || degl[b] >= MAXDEG) return 0;
            adjl[a][degl[a]++] = b;
            adjl[b][degl[b]++] = a;
        }
    for (int v = 0; v < V; v++) {
        if (degl[v] != d) return 0;
        for (int c1 = 0; c1 < degl[v]; c1++)
            for (int c2 = 0; c2 < c1; c2++)
                if (adjl[v][c1] == adjl[v][c2]) return 0;
    }
    for (int s = 0; s < V; s++) {
        stampc++;
        int head = 0, tail = 0;
        stamp_[s] = stampc;
        dist_[s] = 0;
        queue_[tail++] = s;
        while (head < tail) {
            int v = queue_[head++];
            if (dist_[v] >= D) continue;
            for (int c = 0; c < degl[v]; c++) {
                int u = adjl[v][c];
                if (stamp_[u] != stampc) {
                    stamp_[u] = stampc;
                    dist_[u] = dist_[v] + 1;
                    queue_[tail++] = u;
                }
            }
        }
        if (tail != V) return 0;
    }
    int m = 0;
    for (int v = 0; v < V; v++)
        for (int c = 0; c < degl[v]; c++) {
            int u = adjl[v][c];
            if (v < u) {
                if (m >= MAXV * MAXDEG / 2) return 0;
                best_eu[m] = v;
                best_ev[m] = u;
                m++;
            }
        }
    best_V = V;
    best_E = m;
    return 1;
}

/* ---------------------------------------------------------- search driver */

static int attempt(int V, double until) {
    int cand[MAXK], nc = 0;
    for (int k = 1; k <= MAXK; k++) {
        if (V % (2 * k)) continue;
        int n = V / (2 * k);
        if (n >= 2 && n < MAXG) cand[nc++] = k;
    }
    if (nc == 0) return 0;
    while (now() < until) {
        int k = cand[rndint(nc)];
        int n = V / (2 * k);
        enum_groups(n);
        if (ngroups == 0) continue;
        Grp G = groups[rndint(ngroups)];
        build_group(G);
        K = k;
        NDART = K * d;
        if (!random_base()) continue;
        rebuild_lists();
        if (run_sa(ITERS, until)) {
            if (store_if_valid()) return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget minV\n", argv[0]);
        printf("0 0\n");
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int minV = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    double t_end = t0 + budget * 0.9;

    long cap = moore_bound();
    if (cap > MAXV) cap = MAXV;

    int V = minV;
    if (V < 2 * (d + 1)) V = 2 * (d + 1);
    if (V % 2) V++;

    double slice = budget / 120.0;
    if (slice < 0.2) slice = 0.2;
    if (slice > 1.5) slice = 1.5;

    while (now() < t_end && V <= cap) {
        double until = now() + slice;
        if (until > t_end) until = t_end;
        attempt(V, until);
        V += 2;
    }

    if (best_V > 0) {
        printf("%d %d\n", best_V, best_E);
        for (int e = 0; e < best_E; e++) printf("%d %d\n", best_eu[e], best_ev[e]);
    } else {
        printf("0 0\n");
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
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    # Lower bound on the vertex count to scan from: about 0.45 of the Moore bound, even.
    minV = max(2 * (d + 1), 2 * (int(0.45 * moore) // 2))
    if minV > moore:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), minV],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
