"""Bi-Cayley / voltage-lift search over semidirect groups, with a safe fallback.

Bold change: instead of random base graphs with bitset diameter checks on the full graph,
the C engine builds lifts of p-orbit base graphs over Z_m x|_r Z_k and checks them with
only 2p BFS runs. Left multiplication by the group is an automorphism that is transitive on
each side of the bipartition, so the diameter is at most D exactly when every vertex is
within D of the 2p orbit representatives. The search raises the vertex target adaptively.
The engine prints K_{d,d} if it finds nothing, and Python keeps the better of that and the start graph.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define MAXG 20000
#define MAXP 4
#define MAXD 32
#define MAXDART (MAXP * MAXD)
#define MAXV (2 * MAXP * MAXG)
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

static int Gm, Gk, Gr, GN;
static int rp[MAXG];      /* rp[b] = r^b mod m */
static int ginv_t[MAXG];  /* inverse table */

/* (a,b)(c,e) = (a + r^b c mod m, b + e mod k), element code a*k + b. */
static int gmul(int x, int y) {
    int a = x / Gk, b = x % Gk, c = y / Gk, e = y % Gk;
    return (int)(((long)a + (long)rp[b] * c) % Gm) * Gk + (b + e) % Gk;
}

static int random_group(int N) {
    long count = 0;
    int bm_ = 0, bk_ = 0, br_ = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm_ = m; bk_ = k; br_ = r; }
        }
    }
    if (!count) return 0;
    Gm = bm_; Gk = bk_; Gr = br_; GN = bm_ * bk_;
    rp[0] = 1 % Gm;
    for (int b = 1; b < Gk; b++) rp[b] = (int)((long)rp[b - 1] * Gr % Gm);
    for (int x = 0; x < GN; x++) {
        int a = x / Gk, b = x % Gk, nb = (Gk - b) % Gk;
        long t = (long)rp[nb] * a % Gm;
        ginv_t[x] = (int)((Gm - t) % Gm) * Gk + nb;
    }
    return 1;
}

/* ---------------------------------------------------------------- lift structure */

/* P A-orbits and P B-orbits, each of size GN. Dart idx = t*P + i joins A(i,x) to
 * B(dJ[idx], x*volt[idx]). Layer t is a permutation pjT[t], so every orbit has
 * exactly d darts out and d darts in, which makes the lift d-regular and bipartite. */
static int P, nd;
static int dI[MAXDART], dJ[MAXDART], volt[MAXDART];
static int baseA[MAXDART], baseB[MAXDART];
static int tabA[MAXDART][MAXG], tabB[MAXDART][MAXG];
static int pjT[MAXD][MAXP], pinvT[MAXD][MAXP];
static int pidx[MAXP][MAXD];

static void set_volt(int idx, int g) {
    volt[idx] = g;
    int gi = ginv_t[g];
    for (int x = 0; x < GN; x++) {
        tabA[idx][x] = gmul(x, g);
        tabB[idx][x] = gmul(x, gi);
    }
}

static void init_base(void) {
    int sig[MAXP];
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < P; i++) sig[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1), s = sig[i];
            sig[i] = sig[j];
            sig[j] = s;
        }
        for (int i = 0; i < P; i++) {
            pjT[t][i] = sig[i];
            pinvT[t][sig[i]] = i;
        }
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++) {
            int idx = t * P + i;
            dI[idx] = i;
            dJ[idx] = pjT[t][i];
            baseA[idx] = P * GN + dJ[idx] * GN;
            baseB[idx] = dI[idx] * GN;
            volt[idx] = -1;
        }
    for (int j = 0; j < P; j++)
        for (int t = 0; t < d; t++) pidx[j][t] = t * P + pinvT[t][j];
}

/* A voltage that does not repeat an existing dart between the same pair of orbits. */
static int fresh(int idx) {
    for (int tries = 0; tries < 300; tries++) {
        int g = rndint(GN), ok = 1;
        for (int o = 0; o < nd && ok; o++)
            if (o != idx && dI[o] == dI[idx] && dJ[o] == dJ[idx] && volt[o] == g) ok = 0;
        if (ok) return g;
    }
    return -1;
}

static int init_volt(void) {
    for (int idx = 0; idx < nd; idx++) {
        int g = fresh(idx);
        if (g < 0) return 0;
        set_volt(idx, g);
    }
    return 1;
}

/* ---------------------------------------------------------------- cost via BFS */

static int vis[MAXV];
static int qu[MAXV];
static int stamp = 0;

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    stamp++;
    int head = 0, tail = 0;
    int PN = P * GN;
    qu[tail++] = src;
    vis[src] = stamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            if (v < PN) {
                int i = v / GN, x = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int idx = t * P + i;
                    int u = baseA[idx] + tabA[idx][x];
                    if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
                }
            } else {
                int w = v - PN;
                int j = w / GN, y = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int idx = pidx[j][t];
                    int u = baseB[idx] + tabB[idx][y];
                    if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertices missed by the BFS from each orbit representative. Zero iff the lift has diameter <= D. */
static long cost(void) {
    long c = 0;
    long NV = 2L * P * GN;
    for (int i = 0; i < P; i++) c += NV - bfs_count(i * GN);
    for (int j = 0; j < P; j++) c += NV - bfs_count(P * GN + j * GN);
    return c;
}

/* ---------------------------------------------------------------- output storage */

static int *bu = NULL, *bv = NULL;
static int bn = 0;
static long bm = 0;

static void save_solution(void) {
    int n = 2 * P * GN;
    long m = (long)nd * GN;
    free(bu);
    free(bv);
    bu = malloc(sizeof(int) * (size_t)m);
    bv = malloc(sizeof(int) * (size_t)m);
    long e = 0;
    for (int idx = 0; idx < nd; idx++)
        for (int x = 0; x < GN; x++) {
            bu[e] = dI[idx] * GN + x;
            bv[e] = baseA[idx] + tabA[idx][x];
            e++;
        }
    bn = n;
    bm = m;
}

static void print_best(void) {
    if (bn > 0) {
        printf("%d %ld\n", bn, bm);
        for (long e = 0; e < bm; e++) printf("%d %d\n", bu[e], bv[e]);
    } else {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
    }
}

/* ---------------------------------------------------------------- search */

/* Try to find a lift with P orbits over a group of order N. Returns 1 and saves on success. */
static int trial(int Pp, int N, double until) {
    P = Pp;
    GN = N;
    nd = d * P;
    if (!random_group(N)) return 0;
    GN = N;
    init_base();
    if (!init_volt()) return 0;
    long c = cost();
    long bestc = c;
    int stall = 0;
    while (c > 0) {
        if (now() > until) return 0;
        if (stall > STALL) {
            init_base();
            if (!init_volt()) return 0;
            c = cost();
            bestc = c;
            stall = 0;
            continue;
        }
        int idx = rndint(nd);
        int old = volt[idx];
        int g = fresh(idx);
        if (g < 0 || g == old) { stall++; continue; }
        set_volt(idx, g);
        long nc = cost();
        if (nc <= c || rnd01() < 0.01) c = nc;
        else set_volt(idx, old);
        if (c < bestc) { bestc = c; stall = 0; }
        else stall++;
    }
    save_solution();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        print_best();
        return 0;
    }
    long M = moore_bound();
    long lo = start_n;
    long step = lo / 64 > 2 ? lo / 64 : 2;
    while (now() < t_end && lo < M) {
        long T = lo + step;
        if (T > M) T = M;
        int found = 0;
        double rem = t_end - now();
        double slice = rem / 16;
        if (slice < 0.2) slice = 0.2;
        if (slice > 4.0) slice = 4.0;
        for (int at = 0; at < 4 && now() < t_end && !found; at++) {
            int Pp = 1 + rndint(MAXP);
            long N = (T + 2L * Pp - 1) / (2L * Pp);
            if (N < d) N = d;
            if (2L * Pp * N > M || N > MAXG) continue;
            double dl = now() + slice;
            if (dl > t_end) dl = t_end;
            if (trial(Pp, (int)N, dl)) found = 1;
        }
        if (found) {
            lo = bn;
            long cap = lo / 32 > 2 ? lo / 32 : 2;
            step *= 2;
            if (step > cap) step = cap;
        } else {
            step /= 2;
            if (step < 1) step = 1;
        }
    }
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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    if best[0] >= lib.moore_bound(d, D):
        return best
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
