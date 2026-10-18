"""Bold variant: two engines, keep the best valid graph.

Phase 1 is the parent's bi-Cayley search over metacyclic groups (about half the
time). It gives a floor, usually the 506-vertex record for d=3, D=9.

Phase 2 is new. It searches voltage lifts of small cubic-type bipartite base
multigraphs. The base has K vertices per side, and d perfect matchings
(permutations) between them. Voltages live in Z_N, so the lift has 2KN vertices.
Each step of simulated annealing changes one voltage or swaps two entries of a
permutation. The cost is the number of (representative, vertex) pairs at distance
greater than D, summed over the 2K representatives. Fiber translations are
automorphisms, so representatives suffice. Phase 2 only accepts orders above the
current best.

Every returned graph is checked with lib.is_valid. If a phase fails, the best
valid graph so far is returned.
"""
import time

import lib

C_BICAYLEY = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXV (2 * MAXG)
#define MAXDEG 16
#define MAXGRP 4096

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

static int MT[MAXG * MAXG];
static int INV[MAXG];
static int NN;

static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
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

static int dist_[MAXV], queue_[MAXV];

static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

static int bestN = 0;
static Grp bestG;
static int bestS[MAXDEG];

static int search_n(int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return 0;
    int S[MAXDEG];
    while (now() < until) {
        for (int gi = 0; gi < ngroups; gi++) {
            if (now() >= until) break;
            build_group(groups[gi]);
            for (int t = 0; t < 200; t++) {
                pick_set(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) {
                    bestN = n;
                    bestG = groups[gi];
                    memcpy(bestS, S, sizeof(int) * (size_t)d);
                    return 1;
                }
            }
        }
    }
    return 0;
}

static int adjl[MAXV][MAXDEG], degl[MAXV];

static void add_e(int u, int v) {
    adjl[u][degl[u]++] = v;
    adjl[v][degl[v]++] = u;
}

static int verify_explicit(int V) {
    static int dd[MAXV], qq[MAXV];
    for (int v = 0; v < V; v++) if (degl[v] > d || degl[v] < 1) return 0;
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int i = 0; i < degl[v]; i++) {
                int u = adjl[v][i];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void set_complete(void) {
    int V = 2 * d;
    for (int v = 0; v < V; v++) degl[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_e(a, d + b);
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_explicit(int V) {
    long m = 0;
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) m++;
    printf("%d %ld\n", V, m);
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) printf("%d %d\n", u, adjl[u][i]);
}

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

    if (d < 1 || d > MAXDEG) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    int nstart = nlo;
    if (nstart < d + 1) nstart = d + 1;
    double slice = budget / 40.0;
    if (slice < 0.5) slice = 0.5;
    if (slice > 3.0) slice = 3.0;

    if (d >= 2 && D >= 2) {
        for (int n = nstart; n <= nmax && now() < t_end; n++) {
            double until = now() + slice;
            if (until > t_end) until = t_end;
            search_n(n, until);
        }
    }

    int ok = 0;
    if (bestN > 0) {
        int n = bestN, V = 2 * n;
        build_group(bestG);
        for (int v = 0; v < V; v++) degl[v] = 0;
        for (int x = 0; x < n; x++)
            for (int i = 0; i < d; i++) {
                int y = MT[x * n + bestS[i]];
                add_e(x, n + y);
            }
        ok = verify_explicit(V);
        if (ok) print_explicit(V);
    }
    if (!ok) set_complete();
    return 0;
}
'''

C_VOLT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 8
#define MAXK 16
#define MAXV 4096

static int d, D;
static double tend;

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

/* Base: K A-vertices and K B-vertices; dart s joins A_i to B_{sig[s][i]} with voltage volt[s][i].
 * Lift: A_{i,x} = i*N + x, B_{j,y} = K*N + j*N + y; A_{i,x} ~ B_{sig[s][i], x+volt[s][i]}. */
static int K, N, V;
static int sig[MAXD][MAXK], volt[MAXD][MAXK], sinv[MAXD][MAXK];

static void make_inv(void) {
    for (int s = 0; s < d; s++)
        for (int i = 0; i < K; i++) sinv[s][sig[s][i]] = i;
}

static int dist_[MAXV], queue_[MAXV];

/* Number of lifted vertices NOT within distance D of src. */
static int bad_from(int src) {
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    int A = K * N;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < A) {
            int i = v / N, x = v % N;
            for (int s = 0; s < d; s++) {
                int j = sig[s][i];
                int y = x + volt[s][i];
                if (y >= N) y -= N;
                int u = A + j * N + y;
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int w = v - A, j = w / N, y = w % N;
            for (int s = 0; s < d; s++) {
                int i = sinv[s][j];
                int x = y - volt[s][i];
                if (x < 0) x += N;
                int u = i * N + x;
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return V - tail;
}

/* Fibers are Z_N-orbits (translations are automorphisms), so one source per fiber suffices. */
static int total_cost(void) {
    int c = 0;
    for (int i = 0; i < K; i++) c += bad_from(i * N);
    for (int j = 0; j < K; j++) c += bad_from(K * N + j * N);
    return c;
}

static void random_state(void) {
    for (int s = 0; s < d; s++) {
        for (int i = 0; i < K; i++) sig[s][i] = i;
        if (s > 0)
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = sig[s][i];
                sig[s][i] = sig[s][j];
                sig[s][j] = t;
            }
        for (int i = 0; i < K; i++) volt[s][i] = rndint(N);
    }
    make_inv();
}

static int mk, ms, mi, mj, mold_v;

static void do_move(void) {
    if (K < 2 || rnd01() < 0.8) {
        ms = rndint(d);
        mi = rndint(K);
        mk = 0;
        mold_v = volt[ms][mi];
        int nv = rndint(N);
        if (N > 1) while (nv == mold_v) nv = rndint(N);
        volt[ms][mi] = nv;
    } else {
        ms = 1 + rndint(d - 1);
        mi = rndint(K);
        mj = rndint(K);
        if (mj == mi) mj = (mi + 1) % K;
        mk = 1;
        int t = sig[ms][mi];
        sig[ms][mi] = sig[ms][mj];
        sig[ms][mj] = t;
    }
    make_inv();
}

static void undo_move(void) {
    if (mk == 0) {
        volt[ms][mi] = mold_v;
    } else {
        int t = sig[ms][mi];
        sig[ms][mi] = sig[ms][mj];
        sig[ms][mj] = t;
    }
    make_inv();
}

/* Simulated annealing on the current (K, N). Returns 1 with cost 0 (state left in globals). */
static int attempt(double until) {
    random_state();
    int c = total_cost();
    double ta = now();
    double span = until - ta;
    if (span <= 0) return 0;
    double T = 1.0;
    const double T0 = 2.5, T1 = 0.05;
    long it = 0;
    while (c > 0) {
        if ((it & 31) == 0) {
            double tn = now();
            if (tn >= until) break;
            T = T0 * pow(T1 / T0, (tn - ta) / span);
        }
        it++;
        do_move();
        int nc = total_cost();
        if (nc <= c || rnd01() < exp(-(double)(nc - c) / T)) c = nc;
        else undo_move();
    }
    return c == 0;
}

static int ex_adj[MAXV][MAXD], ex_deg[MAXV];

static void build_explicit(void) {
    V = 2 * K * N;
    for (int v = 0; v < V; v++) ex_deg[v] = 0;
    int A = K * N;
    for (int i = 0; i < K; i++)
        for (int x = 0; x < N; x++) {
            int u = i * N + x;
            for (int s = 0; s < d; s++) {
                int j = sig[s][i];
                int y = (x + volt[s][i]) % N;
                int w = A + j * N + y;
                int dup = 0;
                for (int t = 0; t < ex_deg[u]; t++)
                    if (ex_adj[u][t] == w) { dup = 1; break; }
                if (dup) continue;
                if (ex_deg[u] >= d || ex_deg[w] >= d) continue;
                ex_adj[u][ex_deg[u]++] = w;
                ex_adj[w][ex_deg[w]++] = u;
            }
        }
}

static int verify_explicit(void) {
    static int dd[MAXV], qq[MAXV];
    for (int v = 0; v < V; v++) if (ex_deg[v] < 1) return 0;
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int t = 0; t < ex_deg[v]; t++) {
                int u = ex_adj[v][t];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void print_explicit(void) {
    long m = 0;
    for (int u = 0; u < V; u++)
        for (int t = 0; t < ex_deg[u]; t++)
            if (u < ex_adj[u][t]) m++;
    printf("%d %ld\n", V, m);
    for (int u = 0; u < V; u++)
        for (int t = 0; t < ex_deg[u]; t++)
            if (u < ex_adj[u][t]) printf("%d %d\n", u, ex_adj[u][t]);
}

static int bK = 0, bN = 0;
static int bS[MAXD][MAXK], bVt[MAXD][MAXK];

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget minv\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int minv = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 7) * 0xD1B54A32D192ED03ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    tend = t0 + budget * 0.92;

    int bestV = minv;
    int have = 0;
    static const int Ks[] = {4, 3, 6, 2, 8, 5, 12, 16};
    const int nKs = 8;
    double slice = budget / 6.0;
    if (slice < 2.0) slice = 2.0;
    int rr = 0;

    while (now() < tend - 0.3) {
        int Kc = Ks[rr % nKs];
        rr++;
        int Nc = bestV / (2 * Kc) + 1;
        if (Nc < 2) Nc = 2;
        if (2 * Kc * Nc > MAXV) continue;
        K = Kc;
        N = Nc;
        V = 2 * K * N;
        double until = now() + slice;
        if (until > tend) until = tend;
        if (attempt(until) && V > bestV) {
            bestV = V;
            bK = K;
            bN = N;
            memcpy(bS, sig, sizeof sig);
            memcpy(bVt, volt, sizeof volt);
            have = 1;
        }
    }

    if (!have) { printf("0 0\n"); return 0; }
    K = bK;
    N = bN;
    V = 2 * K * N;
    memcpy(sig, bS, sizeof sig);
    memcpy(volt, bVt, sizeof volt);
    make_inv();
    build_explicit();
    if (!verify_explicit()) { printf("0 0\n"); return 0; }
    print_explicit();
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

    def accept(out):
        nonlocal best
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out

    # Phase 1: bi-Cayley over metacyclic groups (the parent engine), about half the time.
    budget1 = 0.5 * (0.82 * time_limit - 1.0)
    if budget1 >= 1.0:
        nlo = max(d + 1, best[0] // 2 + 1, int(0.45 * moore) // 2)
        if nlo <= moore // 2:
            try:
                text = lib.run_c(C_BICAYLEY, [d, D, seed, round(budget1, 2), nlo],
                                 stdin_graph=None, timeout=budget1 + 8)
                accept(lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                pass

    # Phase 2: voltage lifts of small bipartite base graphs, searching above the current best.
    if d <= 8:
        budget2 = 0.82 * time_limit - (time.monotonic() - t0) - 1.5
        if budget2 >= 2.0:
            try:
                text = lib.run_c(C_VOLT, [d, D, seed, round(budget2, 2), best[0]],
                                 stdin_graph=None, timeout=budget2 + 8)
                accept(lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                pass

    return best
