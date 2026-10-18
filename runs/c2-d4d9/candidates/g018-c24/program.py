"""Program: voltage lifts over metacyclic groups with a multi-vertex base graph.

Construction:
  * A base bipartite multigraph with K vertices per side, d-regular, with dK darts.
    Each dart e carries a voltage g_e in a metacyclic group G = Z_m x|_r Z_kk of order N.
  * Lift: fibre A_i and fibre B_j each have N vertices. Dart e from i to j joins
    (A,i,x) to (B,j,x*g_e) for all x in G. The lift is d-regular, bipartite, with 2KN vertices.
  * Left multiplication by h in G is an automorphism of the lift, so the diameter bound
    holds iff BFS from one representative per fibre reaches all 2KN vertices within D steps.
  * K = 1 is the bi-Cayley construction. K = 2, 3, 4 is the new, substantially different
    family: a larger, less symmetric base gives many more free voltages.
  * Search: simulated-annealing-style hill climbing on the voltages, with random base
    restarts. Cost = number of (representative, vertex) pairs left beyond distance D.
  * Candidates are ordered by total vertex count, starting at the record, and are scheduled
    by iterative deepening so that the record-level K = 1 candidates are tried first.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
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

#define MAXK 4
#define MAXDEG 8
#define MAXDART (MAXK * MAXDEG)
#define MAXN 6400
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 256
#define STALL_LIMIT 3000
#define ACCEPT_WORSE 0.01
#define BIG 1000000000L

static int d, D;
static long lo_total;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
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

/* ------------------------------------------------------------ group Z_m x| Z_kk */

static int GM = 1, GK = 1, GR = 1, GN = 1;
static int pw[MAXN];

static void set_group(int m, int kk, int r) {
    GM = m;
    GK = kk;
    GR = r;
    GN = m * kk;
    pw[0] = 1 % m;
    for (int b = 1; b < kk; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
}

/* (a,b)(c,e) = (a + r^b c, b + e), element coded a*GK + b */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, e = y % GK;
    int aa = (int)(((long)a + (long)pw[b] * c) % GM);
    int bb = (b + e) % GK;
    return aa * GK + bb;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int t = (int)((long)pw[nb] * a % GM);
    int na = (GM - t) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------ base graph and voltages */

static int K = 1, NDART = 1;
static int dto[MAXDART];           /* dart e: A-fibre e/d -> B-fibre dto[e] */
static int dvol[MAXDART];          /* voltage of dart e */
static int Rf[MAXDART][MAXN];      /* Rf[e][x] = x * g_e */
static int Rb[MAXDART][MAXN];      /* Rb[e][y] = y * g_e^{-1} */
static int ind[MAXK][MAXDEG];      /* darts entering B-fibre j */

static void build_ind(void) {
    int cnt[MAXK];
    for (int j = 0; j < K; j++) cnt[j] = 0;
    for (int e = 0; e < NDART; e++) {
        int j = dto[e];
        ind[j][cnt[j]++] = e;
    }
}

static void random_base(void) {
    int slots[MAXDART];
    int c = 0;
    for (int j = 0; j < K; j++)
        for (int t = 0; t < d; t++) slots[c++] = j;
    for (int i = c - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = slots[i];
        slots[i] = slots[j];
        slots[j] = tmp;
    }
    for (int e = 0; e < NDART; e++) dto[e] = slots[e];
    build_ind();
}

/* True if giving dart e voltage g would duplicate an existing lifted edge set. */
static int conflicts(int e, int g) {
    int fe = e / d;
    for (int f = 0; f < NDART; f++) {
        if (f == e) continue;
        if (f / d == fe && dto[f] == dto[e] && dvol[f] == g) return 1;
    }
    return 0;
}

static void set_dart(int e, int g) {
    dvol[e] = g;
    int gi = ginv(g);
    for (int x = 0; x < GN; x++) {
        Rf[e][x] = gmul(x, g);
        Rb[e][x] = gmul(x, gi);
    }
}

static void random_volts(void) {
    for (int e = 0; e < NDART; e++) dvol[e] = -1;
    for (int e = 0; e < NDART; e++) {
        int g = -1;
        for (int tries = 0; tries < 10000; tries++) {
            int c = rndint(GN);
            if (!conflicts(e, c)) { g = c; break; }
        }
        if (g < 0) g = rndint(GN);
        set_dart(e, g);
    }
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qbuf[MAXV];

static int ball_count(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int half = K * GN;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qbuf[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qbuf[head];
            if (v < half) {
                int i = v / GN, x = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int e = i * d + t;
                    int u = half + dto[e] * GN + Rf[e][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qbuf[tail++] = u; }
                }
            } else {
                int idx = v - half;
                int j = idx / GN, y = idx - j * GN;
                for (int t = 0; t < d; t++) {
                    int e = ind[j][t];
                    int u = (e / d) * GN + Rb[e][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qbuf[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long total_cost(void) {
    for (int e = 0; e < NDART; e++)
        for (int f = e + 1; f < NDART; f++)
            if (e / d == f / d && dto[e] == dto[f] && dvol[e] == dvol[f]) return BIG;
    long NV = 2L * K * GN;
    long c = 0;
    for (int i = 0; i < K; i++) c += NV - ball_count(i * GN);
    for (int j = 0; j < K; j++) c += NV - ball_count((K + j) * GN);
    return c;
}

/* ------------------------------------------------------------ search */

static int climb(double until) {
    random_base();
    random_volts();
    long cur = total_cost();
    long best_local = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL_LIMIT) {
            random_base();
            random_volts();
            cur = total_cost();
            best_local = cur;
            stall = 0;
            continue;
        }
        int e = rndint(NDART);
        int g = rndint(GN);
        if (g == dvol[e] || conflicts(e, g)) { stall++; continue; }
        int old = dvol[e];
        set_dart(e, g);
        long nc = total_cost();
        if (nc <= cur || rnd01() < ACCEPT_WORSE) {
            cur = nc;
        } else {
            set_dart(e, old);
        }
        if (cur < best_local) { best_local = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

static long bestTotal = 0;
static int bK, bM, bKK, bR;
static int bTo[MAXDART], bVol[MAXDART];

static void record_best(void) {
    bestTotal = 2L * K * GN;
    bK = K;
    bM = GM;
    bKK = GK;
    bR = GR;
    memcpy(bTo, dto, sizeof(int) * (size_t)NDART);
    memcpy(bVol, dvol, sizeof(int) * (size_t)NDART);
}

/* ------------------------------------------------------------ candidates */

typedef struct { int k, N, m, kk, r; } Cand;
static Cand cands[MAXCAND];
static int ncand = 0;

static long cand_total(const Cand *c) { return 2L * c->k * c->N; }

static void add_cand(int k, int N, int m, int kk, int r) {
    if (ncand < MAXCAND) {
        cands[ncand].k = k;
        cands[ncand].N = N;
        cands[ncand].m = m;
        cands[ncand].kk = kk;
        cands[ncand].r = r;
        ncand++;
    }
}

static void gen_cands(long moore) {
    ncand = 0;
    for (int k = 1; k <= MAXK; k++) {
        long Nmin = (lo_total + 2L * k - 1) / (2L * k);
        if (Nmin < 3) Nmin = 3;
        for (long N = Nmin; N <= Nmin + 3 && N <= MAXN; N++) {
            if (2L * k * N > moore) break;
            int got = 0;
            for (int kk = 1; kk <= N / 3 && got < 6 && ncand < MAXCAND; kk++) {
                if (N % kk) continue;
                long m = N / kk;
                if (m < 2) continue;
                int rc = 0;
                for (long r = 1; r < m && rc < 2 && got < 6; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, kk, m) != 1 % m) continue;
                    add_cand(k, (int)N, (int)m, kk, (int)r);
                    rc++;
                    got++;
                }
            }
        }
    }
    for (int i = 1; i < ncand; i++) {
        Cand c = cands[i];
        int j = i - 1;
        while (j >= 0 && cand_total(&cands[j]) > cand_total(&c)) {
            cands[j + 1] = cands[j];
            j--;
        }
        cands[j + 1] = c;
    }
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lo_total]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    lo_total = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 0.8;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    if (lo_total < 2L * d + 1) lo_total = 2L * d + 1;
    if (lo_total > moore) { print_complete(); return 0; }

    gen_cands(moore);

    double budget = t_end - now();
    double base_slice = budget * 0.02;
    if (base_slice < 0.25) base_slice = 0.25;

    for (int round = 0; round < 10; round++) {
        int attempted = 0;
        for (int c = 0; c < ncand; c++) {
            double rem = t_end - now();
            if (rem < 0.1) break;
            Cand *cd = &cands[c];
            long T = cand_total(cd);
            if (T <= bestTotal || T < lo_total) continue;
            set_group(cd->m, cd->kk, cd->r);
            K = cd->k;
            NDART = K * d;
            double slice = base_slice * (double)(1 << round);
            if (slice > rem) slice = rem;
            attempted = 1;
            if (climb(now() + slice)) record_best();
        }
        if (!attempted || t_end - now() < 0.1) break;
    }

    if (bestTotal == 0) { print_complete(); return 0; }

    set_group(bM, bKK, bR);
    K = bK;
    NDART = K * d;
    memcpy(dto, bTo, sizeof(int) * (size_t)NDART);
    build_ind();
    for (int e = 0; e < NDART; e++) set_dart(e, bVol[e]);
    if (total_cost() != 0) { print_complete(); return 0; }

    int n = 2 * K * GN;
    printf("%d %d\n", n, NDART * GN);
    for (int e = 0; e < NDART; e++) {
        int i = e / d;
        for (int x = 0; x < GN; x++)
            printf("%d %d\n", i * GN + x, K * GN + dto[e] * GN + Rf[e][x]);
    }
    return 0;
}
'''

REF_TOTAL = {(4, 9): 4970}


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
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best
    lo = REF_TOTAL.get((d, D), max(best[0] + 1, 2 * d + 1))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo], timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
