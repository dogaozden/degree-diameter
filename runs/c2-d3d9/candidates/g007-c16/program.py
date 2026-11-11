"""Bold variant: hill-climbed voltage lifts of small bipartite base graphs over metacyclic groups.

Construction: a d-regular bipartite base multigraph on K + K vertices is given by d permutations
sigma_t of {0..K-1}, so dart (t, i) joins A_i to B_{sigma_t(i)}. Each dart carries a voltage
g in a group G of order N. The lift has vertices A_{i,x}, B_{j,y} (x, y in G) and edges
A_{i,x} ~ B_{sigma_t(i), x*g_{t,i}}. Left multiplication by G is an automorphism, so the
diameter check needs only BFS from the 2K base representatives (A_i,e) and (B_j,e).

For each total order T = 2KN (scanned upward from a lower bound), the C engine tries
K = 1..8 and N = T/(2K) over metacyclic groups Z_m x| Z_k. For each (K, N), it runs a
hill climb over permutations and voltages, minimizing the number of pairs at distance
greater than D. A zero-cost state is re-verified by BFS from every vertex and printed.
If nothing beats the fallback, the C program prints K_{d,d}. Python checks everything
with lib.is_valid and keeps the best valid graph.
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

#define MAXN 2048
#define MAXV 4096
#define MAXDEG 16
#define MAXK 8
#define MAXGRP 4096
#define STALL 4000

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
static Grp groups[MAXGRP];
static int ngroups;

/* All metacyclic groups of order N: element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void enum_groups(int N) {
    ngroups = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
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

static int MT[MAXN * MAXN];  /* multiplication table of the current group */
static int NN;

static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
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
}

/* ---------------------------------------------------------- lift state */

static int K_, N_;
static int SIG[MAXDEG][MAXK];   /* SIG[t] is a permutation of 0..K-1 */
static int VOL[MAXDEG][MAXK];   /* voltages in 0..N-1 */
static int adj[MAXV][MAXDEG];
static int deg[MAXV];

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

/* A_i = i*N + x ; B_j = (K + j)*N + y. Dart (t,i): A_{i,x} ~ B_{SIG[t][i], x*VOL[t][i]}. */
static void build_adj(void) {
    int K = K_, N = N_;
    int V = 2 * K * N;
    for (int v = 0; v < V; v++) deg[v] = 0;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) {
            int j = SIG[t][i], g = VOL[t][i];
            for (int x = 0; x < N; x++) {
                int a = i * N + x;
                int b = (K + j) * N + MT[x * N + g];
                if (has_edge(a, b)) continue;
                adj[a][deg[a]++] = b;
                adj[b][deg[b]++] = a;
            }
        }
    }
}

static int stamp_v[MAXV], stampc = 0;
static int dist_[MAXV], q_[MAXV];

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    stampc++;
    int head = 0, tail = 0;
    stamp_v[src] = stampc;
    dist_[src] = 0;
    q_[tail++] = src;
    while (head < tail) {
        int v = q_[head++];
        if (dist_[v] >= D) continue;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (stamp_v[u] != stampc) {
                stamp_v[u] = stampc;
                dist_[u] = dist_[v] + 1;
                q_[tail++] = u;
            }
        }
    }
    return tail;
}

/* Cost = total unreached pairs from the 2K base representatives (identity of each side). */
static long evaluate(void) {
    build_adj();
    int V = 2 * K_ * N_;
    long bad = 0;
    for (int s = 0; s < 2 * K_; s++) {
        int r = bfs_reach(s * N_);
        bad += V - r;
    }
    return bad;
}

static void init_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K_; i++) SIG[t][i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = SIG[t][i]; SIG[t][i] = SIG[t][j]; SIG[t][j] = tmp;
        }
        for (int i = 0; i < K_; i++) VOL[t][i] = rndint(N_);
    }
}

static void mutate(void) {
    int t = rndint(d), i = rndint(K_);
    if (K_ >= 2 && rndint(4) == 0) {
        int i2 = rndint(K_);
        int tmp = SIG[t][i]; SIG[t][i] = SIG[t][i2]; SIG[t][i2] = tmp;
    } else {
        VOL[t][i] = rndint(N_);
    }
}

/* ---------------------------------------------------------- search */

static int bestT = 0;
static int bestK, bestN;
static Grp bestG;
static int bestSIG[MAXDEG][MAXK];
static int bestVOL[MAXDEG][MAXK];

/* Hill climb for base size K and group order N. Returns 1 on success (stored in best*). */
static int try_order(int K, int N, double until) {
    K_ = K;
    N_ = N;
    enum_groups(N);
    if (ngroups == 0) return 0;
    static int sS[MAXDEG][MAXK], sV[MAXDEG][MAXK];
    while (now() < until) {
        Grp G = groups[rndint(ngroups)];
        build_group(G);
        init_state();
        long cur = evaluate();
        int stall = 0;
        unsigned long it = 0;
        while (cur > 0 && stall < STALL) {
            if ((++it & 127) == 0 && now() >= until) break;
            memcpy(sS, SIG, sizeof SIG);
            memcpy(sV, VOL, sizeof VOL);
            mutate();
            long nv = evaluate();
            if (nv <= cur) {
                if (nv < cur) stall = 0; else stall++;
                cur = nv;
            } else {
                memcpy(SIG, sS, sizeof SIG);
                memcpy(VOL, sV, sizeof VOL);
                stall++;
            }
        }
        if (cur == 0) {
            bestT = 2 * K * N;
            bestK = K;
            bestN = N;
            bestG = G;
            memcpy(bestSIG, SIG, sizeof SIG);
            memcpy(bestVOL, VOL, sizeof VOL);
            return 1;
        }
    }
    return 0;
}

/* Full verification (BFS from every vertex), then print. Returns 1 if printed. */
static int print_verified(void) {
    int V = 2 * K_ * N_;
    build_adj();
    for (int v = 0; v < V; v++)
        if (deg[v] < 1 || deg[v] > d) return 0;
    for (int s = 0; s < V; s++)
        if (bfs_reach(s) != V) return 0;
    long m = 0;
    for (int a = 0; a < V; a++)
        for (int i = 0; i < deg[a]; i++)
            if (adj[a][i] > a) m++;
    printf("%d %ld\n", V, m);
    for (int a = 0; a < V; a++)
        for (int i = 0; i < deg[a]; i++)
            if (adj[a][i] > a) printf("%d %d\n", a, adj[a][i]);
    return 1;
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

    if (d < 2 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    long moore = moore_bound();
    long tmax = moore;
    if (tmax > MAXV) tmax = MAXV;

    double slice = budget / 100.0;
    if (slice < 0.1) slice = 0.1;
    if (slice > 1.0) slice = 1.0;

    int T = tlo;
    if (T < 2 * (d + 1)) T = 2 * (d + 1);
    if (T % 2) T++;

    for (; T <= tmax && now() < t_end; T += 2) {
        for (int K = 1; K <= MAXK && now() < t_end; K++) {
            if (T % (2 * K)) continue;
            int N = T / (2 * K);
            if (N < 2 || N > MAXN) continue;
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (try_order(K, N, until)) break;
        }
    }

    if (bestT > 0) {
        K_ = bestK;
        N_ = bestN;
        build_group(bestG);
        memcpy(SIG, bestSIG, sizeof SIG);
        memcpy(VOL, bestVOL, sizeof VOL);
        if (print_verified()) return 0;
    }
    set_complete();
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
    if start is None:
        start = lib.haar_graph(d, range(d))           # K_{d,d}
        if not lib.is_valid(start[0], start[1], d, D):
            start = (2, [(0, 1)])
    best = start
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    # Lower bound for the total order scan (always even, since T = 2KN).
    tstart = max(2 * (d + 1), best[0] + 2, 2 * (int(0.45 * moore) // 2))
    if tstart % 2:
        tstart += 1

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), tstart],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
