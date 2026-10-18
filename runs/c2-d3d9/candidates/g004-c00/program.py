"""Multi-orbit voltage lifts over metacyclic groups, searched by annealing.

New construction: a K-orbit lift of a d-regular bipartite base. Each side has K
orbits of a group G of order N, giving 2KN vertices. Vertex A_{i,x} is joined to
B_{j,x*g} for every dart (t, i) with target j = perm_t(i) and voltage g = gel[t][i].
Each layer t is a permutation of the K orbits, so every vertex has degree d and
the lift is automatically bipartite. Left multiplication by G is an automorphism,
so it suffices to check BFS from the K A-representatives and the K B-representatives.

Search:
  Phase A (d = 3): exhaustive bi-Cayley scan (K = 1, S = {0, s, t}) over all
    metacyclic groups of order n, upward from nlo, stopping at the first order that
    fails completely or runs out of its time share.
  Phase B: simulated annealing on the lift state (permutations and voltages), with
    K in {2,3,4} and N chosen so the lift order exceeds the best found so far.
    Cost = total unreached (source, vertex) pairs plus a large penalty per
    duplicate dart. Cost 0 means valid.

The C program re-verifies its output before printing. Python checks everything
with lib.is_valid and keeps the valid fallback.
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
#define MAXK 4
#define MAXD 16
#define MAXV (2 * MAXK * MAXN)
#define MAXGRP 4096

static int d, D;
static long moore;
static double t_end;
static long vfloor;

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
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1 && ngroups < MAXGRP) {
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
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (ngroups < MAXGRP) {
                    groups[ngroups].m = m;
                    groups[ngroups].k = k;
                    groups[ngroups].r = r;
                    ngroups++;
                }
            }
        }
    }
}

static int MT[MAXN * MAXN];
static int INV[MAXN];
static int NN;

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
    int rp[MAXN];
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

static int K;
static int perm[MAXD][MAXK];   /* perm[t][i] = target orbit j of dart (t, i) */
static int gel[MAXD][MAXK];    /* voltage of dart (t, i) */
static int inI[MAXK][MAXD], inT[MAXK][MAXD];

typedef struct { int perm[MAXD][MAXK]; int gel[MAXD][MAXK]; } State;

/* Vertices: A_{i,x} = i*NN + x, B_{j,h} = (K + j)*NN + h. */

static void index_darts(void) {
    int cnt[MAXK] = {0, 0, 0, 0};
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) {
            int j = perm[t][i];
            inI[j][cnt[j]] = i;
            inT[j][cnt[j]] = t;
            cnt[j]++;
        }
}

static int dup_count(void) {
    int bad = 0;
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = t + 1; t2 < d; t2++)
                if (perm[t][i] == perm[t2][i] && gel[t][i] == gel[t2][i]) bad++;
    return bad;
}

static int vis[MAXV], dst_[MAXV], que_[MAXV];
static int stamp = 0;

/* Number of vertices within distance D of src. */
static int bfs_visited(int src) {
    int half = K * NN;
    if (++stamp == 0x7fffff00) { memset(vis, 0, sizeof vis); stamp = 1; }
    int head = 0, tail = 0;
    vis[src] = stamp;
    dst_[src] = 0;
    que_[tail++] = src;
    while (head < tail) {
        int v = que_[head++];
        int dv = dst_[v];
        if (dv >= D) continue;
        if (v < half) {
            int i = v / NN, x = v % NN;
            for (int t = 0; t < d; t++) {
                int j = perm[t][i];
                int u = half + j * NN + MT[x * NN + gel[t][i]];
                if (vis[u] != stamp) {
                    vis[u] = stamp;
                    dst_[u] = dv + 1;
                    que_[tail++] = u;
                }
            }
        } else {
            int w = v - half, j = w / NN, h = w % NN;
            for (int q = 0; q < d; q++) {
                int i = inI[j][q], t = inT[j][q];
                int u = i * NN + MT[h * NN + INV[gel[t][i]]];
                if (vis[u] != stamp) {
                    vis[u] = stamp;
                    dst_[u] = dv + 1;
                    que_[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* 0 iff the current state is a valid lift; otherwise a positive penalty. */
static long cost_state(void) {
    index_darts();
    int dup = dup_count();
    if (dup) return 1000L * dup;
    long V = 2L * K * NN;
    long c = 0;
    for (int s = 0; s < 2 * K; s++)   /* representatives: s*NN for all 2K orbits */
        c += V - bfs_visited(s * NN);
    return c;
}

/* ---------------------------------------------------------- best store */

static int bestK = 0;
static long bestV = 0;
static Grp bestG;
static State bestSt;

static void save_best(int Kv, Grp G) {
    bestK = Kv;
    bestG = G;
    bestV = 2L * Kv * (G.m * G.k);
    memcpy(bestSt.perm, perm, sizeof perm);
    memcpy(bestSt.gel, gel, sizeof gel);
}

/* ---------------------------------------------------------- phase A: exhaustive bi-Cayley (d = 3) */

static int exhaustive_n(int n, double until, int *complete) {
    *complete = 1;
    enum_groups(n);
    K = 1;
    for (int t = 0; t < d; t++) perm[t][0] = 0;
    for (int gi = 0; gi < ngroups; gi++) {
        build_group(groups[gi]);
        gel[0][0] = 0;
        for (int s = 1; s < n; s++)
            for (int u = s + 1; u < n; u++) {
                if (now() >= until) { *complete = 0; return 0; }
                gel[1][0] = s;
                gel[2][0] = u;
                if (cost_state() == 0) {
                    save_best(1, groups[gi]);
                    return 1;
                }
            }
    }
    return 0;
}

static void phase_a(int nlo, double until) {
    long half = moore / 2;
    for (int n = nlo; n <= half && n < MAXN; n++) {
        int complete = 0;
        if (!exhaustive_n(n, until, &complete)) break;
    }
}

/* ---------------------------------------------------------- phase B: annealing over multi-orbit lifts */

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) perm[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[t][i];
            perm[t][i] = perm[t][j];
            perm[t][j] = tmp;
        }
        for (int i = 0; i < K; i++) gel[t][i] = rndint(NN);
    }
}

static void mutate(void) {
    if (K >= 2 && rndint(3) == 0) {
        int t = rndint(d), a = rndint(K), b = rndint(K);
        int tmp = perm[t][a];
        perm[t][a] = perm[t][b];
        perm[t][b] = tmp;
    } else {
        int t = rndint(d), i = rndint(K);
        gel[t][i] = rndint(NN);
    }
}

static int sa_run(int Kv, Grp G, double until) {
    K = Kv;
    build_group(G);
    random_state();
    long cur = cost_state();
    const long L = 20000;
    long it = 0;
    for (;;) {
        if (cur == 0) { save_best(Kv, G); return 1; }
        if ((it & 127) == 0 && now() >= until) return 0;
        double frac = (double)(it % L) / (double)L;
        double T = 3.0 * (1.0 - frac) + 0.2;
        State sv;
        memcpy(sv.perm, perm, sizeof perm);
        memcpy(sv.gel, gel, sizeof gel);
        mutate();
        long c = cost_state();
        if (c <= cur || rndu() < exp(-(double)(c - cur) / T)) {
            cur = c;
        } else {
            memcpy(perm, sv.perm, sizeof perm);
            memcpy(gel, sv.gel, sizeof gel);
        }
        it++;
    }
}

static void phase_b(double until) {
    while (now() < until) {
        long floor_v = bestV > vfloor ? bestV : vfloor;
        long target = floor_v + 1;
        if (target > moore) break;
        int Kv = 2 + rndint(3);                      /* 2..4 orbits per side */
        long N = (target + 2L * Kv - 1) / (2L * Kv); /* smallest N with 2KN >= target */
        if (N < 2 || 2L * Kv * N > moore || N >= MAXN) continue;
        enum_groups((int)N);
        if (ngroups == 0) continue;
        Grp G = groups[rndint(ngroups)];
        double rem = until - now();
        double slice = 1.5 < rem ? 1.5 : rem;
        if (slice <= 0) break;
        sa_run(Kv, G, now() + slice);
    }
}

/* ---------------------------------------------------------- output */

static void print_best(void) {
    if (bestK == 0) { printf("0 0\n"); return; }
    K = bestK;
    build_group(bestG);
    memcpy(perm, bestSt.perm, sizeof perm);
    memcpy(gel, bestSt.gel, sizeof gel);
    if (cost_state() != 0) { printf("0 0\n"); return; }
    int n = NN;
    int V = 2 * K * n;
    long m = (long)K * n * d;
    printf("%d %ld\n", V, m);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < n; x++)
            for (int t = 0; t < d; t++) {
                int j = perm[t][i];
                int a = i * n + x;
                int b = (K + j) * n + MT[x * n + gel[t][i]];
                printf("%d %d\n", a, b);
            }
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget nlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    moore = moore_bound();
    double t0 = now();
    t_end = t0 + budget * 0.92;
    vfloor = 2L * (nlo > 1 ? nlo : 2);

    if (d == 3) {
        double ua = t0 + 0.35 * (t_end - t0);
        phase_a(nlo > 2 ? nlo : 2, ua);
    }
    phase_b(t_end);
    print_best();
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

    # Start the lift search near 47% of the Moore bound (in half-order units).
    nlo = max(d + 1, best[0] // 2 + 1, int(0.47 * moore) // 2)
    if nlo > moore // 2:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
