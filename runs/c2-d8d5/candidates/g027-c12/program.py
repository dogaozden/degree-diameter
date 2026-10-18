"""Bi-Cayley lift search in C: exact representative-BFS cost, simulated annealing over
layer permutations and voltages on random semidirect groups, with full validation on every improvement.
Python only supplies a projective-plane fallback and validates the output."""
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


C_SOURCE = r'''
/* Bipartite bi-Cayley lift search.
 * Vertices: A_{i,x} = i*G + x (i < K), B_{j,y} = (K+j)*G + y, G = group order.
 * Layer l sends A_{i,x} to B_{lay[l][i], x*volt[l][i]} (left multiplication is an automorphism,
 * so only BFS from the 2K block identities is needed to test diameter).
 * Usage: prog d D seed time_limit   (stdin ignored). stdout: "n m" + edges.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 6000
#define MAXD 16
#define MAXK 8
#define MAXE 60000
#define PEN 40

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

/* Z_m x|_r Z_k with element x = a*k + b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
    int ga[MAXN], gb[MAXN];
} Grp;

static Grp grp;

static inline int gmul(const Grp *g, int x, int y) {
    int b = g->gb[x], e = g->gb[y];
    long a = g->ga[x], c = g->ga[y];
    long aa = (a + (long)g->rp[b] * c) % g->m;
    return (int)(aa * g->k + (b + e) % g->k);
}

static int random_group(int N, Grp *g) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != (1 % m)) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    g->m = bm; g->k = bk; g->r = br;
    g->rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) g->rp[b] = (int)((long)g->rp[b - 1] * br % bm);
    for (int x = 0; x < N; x++) { g->ga[x] = x / bk; g->gb[x] = x % bk; }
    return 1;
}

static int K, GS;
static int lay[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int nb[MAXN][MAXD];
static int vis[MAXN], vst = 0, que[MAXN];

static int best_n = 0, best_m = 0;
static int best_e[MAXE][2];

static void write_entry(int l, int i) {
    int j = lay[l][i], s = volt[l][i];
    for (int x = 0; x < GS; x++) {
        int A = i * GS + x;
        int B = (K + j) * GS + gmul(&grp, x, s);
        nb[A][l] = B;
        nb[B][l] = A;
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l][i] == lay[l2][i] && volt[l][i] == volt[l2][i]) c++;
    return c;
}

/* Unreached (vertex, block-identity) pairs summed over the 2K block identities. */
static long cost_reps(int N) {
    long total = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * GS;
        vst++;
        int head = 0, tail = 0;
        que[tail++] = src;
        vis[src] = vst;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int v = que[head++];
                for (int l = 0; l < d; l++) {
                    int u = nb[v][l];
                    if (vis[u] != vst) { vis[u] = vst; que[tail++] = u; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static int full_check(int N) {
    int half = K * GS;
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++) {
            int u = nb[v][l];
            if (u < 0 || u >= N) return 0;
            if ((v < half) == (u < half)) return 0;
            int found = 0;
            for (int l2 = 0; l2 < d; l2++) {
                if (nb[u][l2] == v) found = 1;
                if (l2 < l && nb[v][l2] == u) return 0;
            }
            if (!found) return 0;
        }
    for (int s = 0; s < N; s++) {
        vst++;
        int head = 0, tail = 0;
        que[tail++] = s;
        vis[s] = vst;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int v = que[head++];
                for (int l = 0; l < d; l++) {
                    int u = nb[v][l];
                    if (vis[u] != vst) { vis[u] = vst; que[tail++] = u; }
                }
            }
        }
        if (tail != N) return 0;
    }
    return 1;
}

static void save_best(int N) {
    int m = 0;
    int half = K * GS;
    for (int v = 0; v < half; v++)
        for (int l = 0; l < d; l++) {
            best_e[m][0] = v;
            best_e[m][1] = nb[v][l];
            m++;
        }
    best_n = N;
    best_m = m;
}

static int anneal(double until, long iters, long patience) {
    int N = 2 * K * GS;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) volt[l][i] = rndint(GS);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) write_entry(l, i);

    long cost = cost_reps(N) + (long)PEN * dupcount();
    double T0 = 1.0 + 0.02 * (double)(cost > 0 ? cost : 1);
    long best_c = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > until) break;
        if (t - last > patience) break;
        double T = T0 * pow(0.02, (double)t / (double)iters) + 0.2;

        int l = rndint(d), i = rndint(K), i2 = -1;
        int oj = lay[l][i], os = volt[l][i];
        int oj2 = 0;
        if (K > 1 && rnd01() < 0.3) {
            i2 = rndint(K);
            if (i2 == i) continue;
            oj2 = lay[l][i2];
            int tmp = lay[l][i]; lay[l][i] = lay[l][i2]; lay[l][i2] = tmp;
            write_entry(l, i);
            write_entry(l, i2);
        } else {
            int ns = rndint(GS);
            if (ns == os) continue;
            volt[l][i] = ns;
            write_entry(l, i);
        }

        long nc = cost_reps(N) + (long)PEN * dupcount();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            if (cost < best_c) { best_c = cost; last = t; }
        } else {
            if (i2 >= 0) {
                lay[l][i] = oj;
                lay[l][i2] = oj2;
                write_entry(l, i);
                write_entry(l, i2);
            } else {
                volt[l][i] = os;
                write_entry(l, i);
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    double slice = limit * 0.06;
    if (slice < 1.0) slice = 1.0;
    int fails = 0;

    while (now() < t_end) {
        if (best_n >= moore) break;
        int k = 1 + rndint(MAXK);
        long need = best_n + 2;
        long gmin = (need + 2L * k - 1) / (2L * k);
        long Gt = gmin + rndint((int)(1 + gmin / 12));
        if (2L * k * Gt > moore || 2L * k * Gt > MAXN) {
            if (++fails > 200) break;
            continue;
        }
        if (!random_group((int)Gt, &grp)) continue;
        K = k;
        GS = (int)Gt;
        int N = 2 * K * GS;
        if (N <= best_n) continue;
        double until = now() + slice;
        if (until > t_end) until = t_end;
        if (anneal(until, 20000, 4000) && full_check(N)) save_best(N);
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", best_e[e][0], best_e[e][1]);
    return 0;
}
'''


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.85 * time_limit - 2.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2).
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
        if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
            return best

    if 2 <= d <= 16 and D >= 2:
        c_budget = end - time.monotonic() - 3.0
        if c_budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 timeout=c_budget + 8.0)
                n, e = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
