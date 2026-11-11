"""Bold variant: voltage lifts of small bipartite base graphs over metacyclic groups.

For a base d-regular bipartite multigraph on P+P vertices (P in 1..4), the lift over a
group G of order N has 2PN vertices. Base vertex A_i with fiber element g is joined to
B_j with fiber element g*s for each dart (i -> j, voltage s). Left multiplication is an
automorphism, so eccentricities are constant on fibers and a BFS from one vertex of each
base vertex suffices during search. The output is re-verified by a full BFS from every
vertex. P = 1 is the bi-Cayley (generalized Haar) construction of the parent. Larger P
gives a different family of lifts.

Configurations (P, N) are visited in ascending order of order T = 2PN, starting above
0.3 * Moore bound. Each success raises the bar. Failed configurations get time slices
that double each round. If nothing beats the start, the result is K_{d,d} or the known start.
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

#define MAXDEG 16
#define MAXP 4
#define MAXN 512
#define MAXGRP 4096
#define MAXV 4096
#define MAXCFG 2048

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
static int ngroups, nnonab;

/* All groups of order n, nonabelian ones first (nnonab of them). */
static void enum_groups(int n) {
    ngroups = 0;
    nnonab = 0;
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
        if (pass == 0) nnonab = ngroups;
    }
}

static int MT[MAXN * MAXN]; /* multiplication table of the current group */
static int INV[MAXN];
static int NN;
static int rp[MAXN];

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is 0. */
static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
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
        INV[x] = 0;
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
    }
}

/* ---------------------------------------------------------- voltage lift state */

/* Dart t from A_i goes to B_{sig[t][i]} with voltage vol[t][i].
 * Lifted vertices: A_i,g = i*N + g; B_j,h = P*N + j*N + h.
 * Edges: A_i,g ~ B_j,g*s for each dart (i, j, s). */
static int sig[MAXDEG][MAXP];
static int sinv[MAXDEG][MAXP];
static int vol[MAXDEG][MAXP];
static int dist_[MAXV], queue_[MAXV];

/* 1 iff every vertex of the lift is within D of src. */
static int reach_from(int src, int P, int N) {
    int half = P * N, V = 2 * half;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < half) {
            int i = v / N, g = v % N;
            for (int t = 0; t < d; t++) {
                int j = sig[t][i];
                int u = half + j * N + MT[g * N + vol[t][i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int w = v - half;
            int j = w / N, h = w % N;
            for (int t = 0; t < d; t++) {
                int i = sinv[t][j];
                int u = i * N + MT[h * N + INV[vol[t][i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

/* One random lift over the current group (already built, order N). */
static int try_once(int P, int N) {
    for (int t = 0; t < d; t++) {
        int p[MAXP];
        for (int i = 0; i < P; i++) p[i] = i;
        if (t > 0)
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
            }
        for (int i = 0; i < P; i++) {
            sig[t][i] = p[i];
            sinv[t][p[i]] = i;
        }
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++)
            vol[t][i] = rndint(N);
    /* Parallel darts from A_i to the same B_j need distinct voltages (simple graph). */
    for (int i = 0; i < P; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = t + 1; t2 < d; t2++)
                if (sig[t][i] == sig[t2][i] && vol[t][i] == vol[t2][i]) return 0;
    /* Fiber transitivity: one source per base vertex suffices. */
    for (int r = 0; r < 2 * P; r++) {
        int src = (r < P) ? r * N : P * N + (r - P) * N;
        if (!reach_from(src, P, N)) return 0;
    }
    return 1;
}

/* ---------------------------------------------------------- search state */

static int bP = 0, bN = 0;
static Grp bG;
static int bsig[MAXDEG][MAXP], bvol[MAXDEG][MAXP];

static void save_best(int P, int N, Grp G) {
    bP = P;
    bN = N;
    bG = G;
    memcpy(bsig, sig, sizeof sig);
    memcpy(bvol, vol, sizeof vol);
}

/* Random search over groups of order N and lifts with P base parts per side.
 * Returns 1 on success (stored in best*). */
static int search_config(int P, int N, double until) {
    enum_groups(N);
    if (ngroups == 0) return 0;
    while (now() < until) {
        int gi;
        if (nnonab > 0 && rndint(10) < 8) gi = rndint(nnonab);
        else gi = rndint(ngroups);
        build_group(groups[gi]);
        for (int t = 0; t < 64; t++) {
            if ((t & 15) == 0 && now() >= until) break;
            if (try_once(P, N)) {
                save_best(P, N, groups[gi]);
                return 1;
            }
        }
    }
    return 0;
}

/* ---------------------------------------------------------- output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static int adj[MAXV][MAXDEG], deg[MAXV];
static int dd[MAXV], qq[MAXV];

static int add_e(int u, int v) {
    if (deg[u] >= d || deg[v] >= d) return 0;
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    return 1;
}

static void output_best(void) {
    int P = bP, N = bN;
    int half = P * N, V = 2 * half;
    build_group(bG);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++) {
            sig[t][i] = bsig[t][i];
            vol[t][i] = bvol[t][i];
            sinv[t][bsig[t][i]] = i;
        }
    for (int v = 0; v < V; v++) deg[v] = 0;
    int ok = 1;
    for (int i = 0; i < P && ok; i++)
        for (int g = 0; g < N && ok; g++) {
            int v = i * N + g;
            for (int t = 0; t < d && ok; t++) {
                int u = half + sig[t][i] * N + MT[g * N + vol[t][i]];
                if (!add_e(v, u)) ok = 0;
            }
        }
    for (int v = 0; v < V && ok; v++) {
        if (deg[v] != d) { ok = 0; break; }
        for (int a = 0; a < deg[v] && ok; a++)
            for (int b = a + 1; b < deg[v]; b++)
                if (adj[v][a] == adj[v][b]) { ok = 0; break; }
    }
    for (int s = 0; s < V && ok; s++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int a = 0; a < deg[v]; a++) {
                int u = adj[v][a];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) ok = 0;
    }
    if (!ok) { print_complete(); return; }
    printf("%d %d\n", V, half * d);
    for (int v = 0; v < half; v++)
        for (int a = 0; a < deg[v]; a++)
            printf("%d %d\n", v, adj[v][a]);
}

/* ---------------------------------------------------------- main */

typedef struct { int P, N, T; } Cfg;
static Cfg cfgs[MAXCFG];
static int ncfg;

static int cmp_cfg(const void *a, const void *b) {
    const Cfg *x = a, *y = b;
    if (x->T != y->T) return x->T - y->T;
    return x->P - y->P;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.93;

    long tmax = moore_bound();
    if (tmax > 4000) tmax = 4000;
    long tlo = tmax * 3 / 10;

    ncfg = 0;
    for (int P = 1; P <= MAXP; P++)
        for (int N = 2; N < MAXN; N++) {
            long T = 2L * P * N;
            if (T < tlo || T > tmax) continue;
            if (ncfg < MAXCFG) {
                cfgs[ncfg].P = P;
                cfgs[ncfg].N = N;
                cfgs[ncfg].T = (int)T;
                ncfg++;
            }
        }
    qsort(cfgs, (size_t)ncfg, sizeof(Cfg), cmp_cfg);

    int bestT = 0;
    double slice = 0.01;
    while (now() < t_end) {
        int active = 0;
        for (int c = 0; c < ncfg && now() < t_end; c++) {
            if (cfgs[c].T <= bestT) continue;
            active++;
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (search_config(cfgs[c].P, cfgs[c].N, until))
                bestT = cfgs[c].T;
        }
        if (active == 0) break;
        slice *= 2;
        if (slice > 5.0) slice = 5.0;
    }

    if (bestT > 0) output_best();
    else print_complete();
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


def _default_graph(d, D):
    """K_{d,d} when valid, otherwise a single vertex (always valid)."""
    if d >= 1:
        g = lib.haar_graph(d, range(d))
        if lib.is_valid(g[0], g[1], d, D):
            return g
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else _default_graph(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.78 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 2.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 8.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass   # keep the valid fallback
    return best
