"""Bold variant: bi-Cayley / voltage-lift search over groups, with an O(2p) BFS check.

Construction: a d-regular base multigraph with p vertices per side, lifted over a
group G = Z_m x| Z_k (order N). Vertex (side, fibre i, g) joins (B, j, g*h) for each dart
(i, j, h). Left multiplication by G is an automorphism, so the diameter check needs
only one BFS per base fibre instead of one per vertex. Voltages are hill-climbed to
minimise the number of pairs farther than D apart. Python keeps a valid fallback.
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

#define MAXV 2048
#define MAXG 1024
#define MAXD 8
#define MAXP 4
#define MAXQ (MAXD * MAXP)
#define MAXE 8192

static int d, D, p, N, nq;
static long goal;
static double t_end;
static int gm, gk, gr;
static int rp[MAXG + 4];
static int permt[MAXD][MAXP], pinv[MAXD][MAXP];
static int bi[MAXQ], bj[MAXQ], gv[MAXQ], gvi[MAXQ];
static long moore;

static int best_n = 0;
static int best_m = 0;
static int best_u[MAXE], best_v[MAXE];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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
    long s = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        s += pw;
        pw *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Group Z_gm x| Z_gk, element (a,b) = a*gk + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    long t = (a + (long)rp[b] * c) % gm;
    return (int)t * gk + (b + e) % gk;
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    long na = ((long)gm - (long)rp[nb] * a % gm) % gm;
    return (int)na * gk + nb;
}

/* Uniform random group of order NN among the semidirect products Z_m x| Z_k. */
static int pick_group(int NN) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= NN; m++) {
        if (NN % m) continue;
        int k = NN / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (cnt == 0) return 0;
    gm = bm; gk = bk; gr = br;
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
    return 1;
}

/* Base: d random permutation layers on p + p vertices (d-regular bipartite multigraph). */
static void random_base(void) {
    nq = d * p;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < p; i++) {
            permt[s][i] = perm[i];
            pinv[s][perm[i]] = i;
            bi[s * p + i] = i;
            bj[s * p + i] = perm[i];
        }
    }
}

/* Random voltage for dart q, distinct from voltages of darts with the same endpoints. */
static int fresh(int q) {
    for (;;) {
        int g = rndint(N), ok = 1;
        for (int t = 0; t < nq; t++)
            if (t != q && bi[t] == bi[q] && bj[t] == bj[q] && gv[t] == g) { ok = 0; break; }
        if (ok) return g;
    }
}

/* s-th neighbour of vertex v. A(i,x) = i*N + x, B(j,y) = p*N + j*N + y. */
static int nbr(int v, int s) {
    int PN = p * N;
    if (v < PN) {
        int i = v / N, x = v % N;
        int q = s * p + i;
        return PN + bj[q] * N + gmul(x, gv[q]);
    } else {
        int w = v - PN;
        int j = w / N, y = w % N;
        int i = pinv[s][j];
        int q = s * p + i;
        return i * N + gmul(y, gvi[q]);
    }
}

static int dist[MAXV];
static int qbuf[MAXV];

/* Number of (source, vertex) pairs at distance > D, over one source per fibre.
 * Zero means the lift is connected with diameter <= D (fibre transitivity). */
static long far_count(void) {
    int n = 2 * p * N, PN = p * N;
    long bad = 0;
    for (int si = 0; si < 2 * p; si++) {
        int src = si < p ? si * N : PN + (si - p) * N;
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[src] = 0;
        qbuf[t++] = src;
        while (h < t) {
            int v = qbuf[h++];
            if (dist[v] >= D) continue;
            for (int s = 0; s < d; s++) {
                int u = nbr(v, s);
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    qbuf[t++] = u;
                }
            }
        }
        bad += n - t;
    }
    return bad;
}

/* Hill-climb the voltages. Returns the number of bad pairs left (0 = success). */
static long try_lift(int steps) {
    for (int q = 0; q < nq; q++) gv[q] = -1;
    for (int q = 0; q < nq; q++) gv[q] = fresh(q);
    for (int q = 0; q < nq; q++) gvi[q] = ginv(gv[q]);
    long bad = far_count();
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) break;
        int q = rndint(nq);
        int old = gv[q];
        gv[q] = fresh(q);
        gvi[q] = ginv(gv[q]);
        long nb = far_count();
        if (nb <= bad || rnd01() < 0.02) {
            bad = nb;
        } else {
            gv[q] = old;
            gvi[q] = ginv(old);
        }
    }
    return bad;
}

static void save_best(void) {
    int PN = p * N;
    int m = 0;
    for (int q = 0; q < nq; q++)
        for (int x = 0; x < N; x++) {
            if (m >= MAXE) return;
            best_u[m] = bi[q] * N + x;
            best_v[m] = PN + bj[q] * N + gmul(x, gv[q]);
            m++;
        }
    best_m = m;
    best_n = 2 * PN;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    goal = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = moore_bound();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    while (now() < t_end) {
        int r = rndint(10);
        p = r < 5 ? 1 : r < 8 ? 2 : r < 9 ? 3 : 4;
        long target = best_n + 2;
        if (goal > 0 && goal + 2 > target && rndint(2) == 0) target = goal + 2;
        long Nlo = (target + 2L * p - 1) / (2L * p);
        long Ntry = Nlo + rndint((int)(1 + Nlo / 8));
        if (Ntry < d + 1) Ntry = d + 1;
        if (Ntry > MAXG) continue;
        N = (int)Ntry;
        if (2L * p * N > moore || 2 * p * N > MAXV) continue;
        if (2L * p * N <= best_n) continue;
        random_base();
        if (!pick_group(N)) continue;
        if (try_lift(3000) == 0) save_best();
    }
    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_u[i], best_v[i]);
    return 0;
}
'''

# Known record orders, passed to the C engine as a search goal.
RECORD_GOAL = {(3, 9): 506}


def known_start(d, D):
    """Best simple construction for (d, D), or None."""
    if D >= 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # diameter 3, valid for any D >= 3
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = known_start(d, D)
    if best is None or not lib.is_valid(*best, d, D):
        best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    if best[0] >= lib.moore_bound(d, D):
        return best
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best
    goal = RECORD_GOAL.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", goal], timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(*out, d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
