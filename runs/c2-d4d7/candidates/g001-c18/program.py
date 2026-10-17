"""Bi-Cayley / voltage-lift search with BFS-only evaluation.

Strategy (new in this version): a lift of a d-regular bipartite base multigraph with p vertices
per side over a semidirect group Z_m x| Z_k of order N. Left multiplication acts transitively on
each fibre, so validity only needs BFS from one representative per fibre (2p BFS runs). The C
engine hill-climbs on the voltages over many random groups and base shapes, growing the target
order one step at a time from scratch or from the start graph. Python keeps the best valid graph
and falls back to K_{d,d} (or the known construction) if anything fails.
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

#define MAXV 4096
#define MAXD 16
#define MAXP 3
#define MAXN 2048
#define MAXE (MAXV * MAXD / 2)
#define STALL 4000

typedef struct { int i, j, g; } Dart;

static int d, D;
static uint64_t rs = 88172645463325252ULL;

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

/* ---------------------------------------------------------------- group Z_m x|_r Z_k */

static int GM, GK, GN;
static int rp[MAXN];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int s = (a + (int)((long)rp[b] * c % GM)) % GM;
    return s * GK + (b + e) % GK;
}

static int random_group(int N) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    GM = bm; GK = bk; GN = N;
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * br % GM);
    return 1;
}

/* ---------------------------------------------------------------- base and darts */

static int P;
static int Mb[MAXP][MAXP];
static Dart DT[MAXP * MAXD];
static int ND;

/* Random base: sum of d random permutation matrices on p+p vertices, retried until connected. */
static int make_base(int p) {
    P = p;
    for (int tries = 0; tries < 1000; tries++) {
        memset(Mb, 0, sizeof Mb);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) Mb[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, cnt = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && Mb[v][u - p] > 0)
                                   : (u < p && Mb[u][v - p] > 0);
                if (linked) { seen[u] = 1; cnt++; st[top++] = u; }
            }
        }
        if (cnt == 2 * p) return 1;
    }
    return 0;
}

/* A voltage not used by any other dart (except skip) between the same base pair. */
static int fresh_g(int skip, int i, int j) {
    for (;;) {
        int g = rndint(GN), ok = 1;
        for (int t = 0; t < ND; t++)
            if (t != skip && DT[t].i == i && DT[t].j == j && DT[t].g == g) { ok = 0; break; }
        if (ok) return g;
    }
}

static void init_darts(void) {
    ND = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int c = 0; c < Mb[i][j]; c++) {
                DT[ND].i = i;
                DT[ND].j = j;
                DT[ND].g = 0;
                ND++;
            }
    for (int t = 0; t < ND; t++) DT[t].g = fresh_g(t, DT[t].i, DT[t].j);
}

/* ---------------------------------------------------------------- lift evaluation */

/* Vertex ids: A(i,x) = i*GN + x, B(j,y) = P*GN + j*GN + y. Edge A(i,x)-B(j,x*g) per dart. */
static int V;
static int adjv[MAXV][MAXD];
static int degv[MAXV];
static int bq[MAXV], dist_[MAXV];
static int TE[MAXE][2];
static int BE[MAXE][2];
static int nBE = 0;
static int bestN = 0;

static void build_adj(void) {
    V = 2 * P * GN;
    for (int v = 0; v < V; v++) degv[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GN; x++) {
            int a = DT[t].i * GN + x;
            int b = P * GN + DT[t].j * GN + gmul(x, DT[t].g);
            if (degv[a] < MAXD && degv[b] < MAXD) {
                adjv[a][degv[a]++] = b;
                adjv[b][degv[b]++] = a;
            }
        }
}

/* Number of vertices farther than D from src. */
static long cost_from(int src) {
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, t = 0, vis = 1;
    bq[t++] = src;
    dist_[src] = 0;
    while (h < t) {
        int v = bq[h++];
        if (dist_[v] >= D) continue;
        for (int k = 0; k < degv[v]; k++) {
            int u = adjv[v][k];
            if (dist_[u] < 0) {
                dist_[u] = dist_[v] + 1;
                bq[t++] = u;
                vis++;
            }
        }
    }
    return V - vis;
}

static long eval_state(void) {
    build_adj();
    long c = 0;
    for (int i = 0; i < P; i++) c += cost_from(i * GN);
    for (int j = 0; j < P; j++) c += cost_from(P * GN + j * GN);
    return c;
}

static int extract(int E[][2]) {
    int m = 0;
    for (int a = 0; a < V; a++)
        for (int k = 0; k < degv[a]; k++) {
            int b = adjv[a][k];
            if (a < b) { E[m][0] = a; E[m][1] = b; m++; }
        }
    return m;
}

/* Full independent validity check: simple, bipartite, degree <= dd, diameter <= DD. */
static int check_graph(int n, int m, int E[][2], int dd, int DD) {
    static int adj[MAXV][MAXD], deg[MAXV], col[MAXV], q[MAXV], dist[MAXV];
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return 0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = E[e][0], v = E[e][1];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= MAXD || deg[v] >= MAXD) return 0;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    for (int v = 0; v < n; v++) {
        if (deg[v] > dd) return 0;
        for (int i = 0; i < deg[v]; i++)
            for (int j = 0; j < i; j++)
                if (adj[v][i] == adj[v][j]) return 0;
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int h = 0, t = 0;
        col[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (col[u] < 0) { col[u] = 1 - col[v]; q[t++] = u; }
                else if (col[u] == col[v]) return 0;
            }
        }
    }
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0, vis = 1;
        dist[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            if (dist[v] >= DD) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; q[t++] = u; vis++; }
            }
        }
        if (vis != n) return 0;
    }
    return 1;
}

static void try_store(void) {
    build_adj();
    int m = extract(TE);
    if (V > bestN && check_graph(V, m, TE, d, D)) {
        bestN = V;
        nBE = m;
        memcpy(BE, TE, sizeof(int) * 2 * (size_t)m);
    }
}

static void read_start(void) {
    static int E[MAXE][2];
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return;
    for (int e = 0; e < m; e++)
        if (scanf("%d %d", &E[e][0], &E[e][1]) != 2) return;
    if (check_graph(n, m, E, d, D)) {
        bestN = n;
        nBE = m;
        memcpy(BE, E, sizeof(int) * 2 * (size_t)m);
    }
}

/* ---------------------------------------------------------------- search */

static void search(double until, long moore) {
    while (now() < until) {
        long target = bestN + 2;
        if (target > moore) return;
        int p = 1 + rndint(MAXP);
        if (p > d) p = d;
        long N = (target + 2L * p - 1) / (2L * p) + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore) N = moore / (2L * p);
        if (2L * p * N > MAXV) N = MAXV / (2L * p);
        if (N > MAXN) N = MAXN;
        if (N < d || 2L * p * N < target) continue;
        if (!random_group((int)N)) continue;
        if (!make_base(p)) continue;
        init_darts();
        long cur = eval_state();
        int stall = 0;
        for (long s = 0; cur > 0 && stall < STALL; s++) {
            if ((s & 127) == 0 && now() > until) break;
            int t = rndint(ND);
            int old = DT[t].g;
            DT[t].g = fresh_g(t, DT[t].i, DT[t].j);
            long nc = eval_state();
            if (nc <= cur || rnd01() < 0.0005) {
                stall = nc < cur ? 0 : stall + 1;
                cur = nc;
            } else {
                DT[t].g = old;
                stall++;
            }
        }
        if (cur == 0) try_store();
    }
}

static void print_best(void) {
    printf("%d %d\n", bestN, nBE);
    for (int e = 0; e < nBE; e++) printf("%d %d\n", BE[e][0], BE[e][1]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 1) { printf("1 0\n"); return 0; }
    double t0 = now();
    double t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start();
    long moore = moore_bound();
    if (D >= 2 && d >= 2 && bestN < moore) search(t_end, moore);

    if (bestN == 0) {
        nBE = 0;
        if (D >= 2) {
            for (int a = 0; a < d; a++)
                for (int b = 0; b < d; b++) {
                    BE[nBE][0] = a;
                    BE[nBE][1] = d + b;
                    nBE++;
                }
            bestN = 2 * d;
        } else {
            BE[0][0] = 0;
            BE[0][1] = 1;
            nBE = 1;
            bestN = 2;
        }
    }
    if (!check_graph(bestN, nBE, BE, d, D)) { bestN = 1; nBE = 0; }
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


def _valid(g, d, D):
    try:
        return lib.is_valid(g[0], g[1], d, D)
    except Exception:
        return False


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = (1, [])
    cands = [start] if start is not None else []
    cands.append(lib.haar_graph(d, range(d)))   # K_{d,d}, valid for D >= 2
    for c in cands:
        if c[0] > best[0] and _valid(c, d, D):
            best = c

    if d < 2 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best if best[1] else None,
                         timeout=budget + 5.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and _valid(out, d, D):
            best = out
    except Exception:
        pass
    return best
