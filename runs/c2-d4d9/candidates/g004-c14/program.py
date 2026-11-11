"""Program: bi-Cayley search over many small metacyclic groups (Z_m semidirect Z_K), for d=4 D=9.

Changed construction (replacing the PSL/SL(2,q) search):
  * Groups are semidirect products G = Z_m x| Z_K with multiplication
    (a,b)(c,e) = (a + r^b c mod m, b + e mod K), requiring r^K = 1 mod m.
    This covers cyclic groups (K=1), abelian groups (r=1) and nonabelian metacyclic groups.
    Orders are restricted to a window (about 1500..2700) around the record scale.
  * Bi-Cayley graph: A_x -- B_{x s_k} for k < d. Left translation is an automorphism, so
    diameter <= D is checked by two BFS runs (from A_e and from B_e).
  * C engine: simulated annealing over the connection set for each sampled group. Groups are
    scheduled round-robin with geometrically growing time slices. Once a group succeeds, only
    strictly larger groups are searched further.
  * Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
    lib.is_valid and keeps the best valid graph (known start or K_{d,d}).
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

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 60
#define POOLMAX 20000
#define BIG (1L << 60)

static int d, D;
static double t_deadline;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ------------------------------------------------------------ group Z_m x| Z_K */

static int gm, gK, N;
static int pw[MAXN];   /* pw[b] = r^b mod m */

static void set_group(int m, int K, int r) {
    gm = m;
    gK = K;
    N = m * K;
    long p = 1 % m;
    for (int b = 0; b < K; b++) {
        pw[b] = (int)p;
        p = p * r % m;
    }
}

/* element (a,b) coded as a*K + b; (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a = x / gK, b = x % gK, c = y / gK, e = y % gK;
    int aa = (int)((a + (long)pw[b] * c) % gm);
    int bb = (b + e) % gK;
    return aa * gK + bb;
}

static int ginv(int x) {
    int a = x / gK, b = x % gK;
    int nb = (gK - b) % gK;
    int na = (int)((gm - ((long)pw[nb] * a) % gm) % gm);
    return na * gK + nb;
}

/* ------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k      (A_x -> B) */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^-1   (B_y -> A) */

static void set_col(int k) {
    int s = S[k], si = ginv(s);
    for (int x = 0; x < N; x++) {
        Rr[k][x] = gmul(x, s);
        Ri[k][x] = gmul(x, si);
    }
}

static int in_S_upto(int x, int cnt) {
    for (int k = 0; k < cnt; k++)
        if (S[k] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + Rr[k][v];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < d; k++) {
                    int u = Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Pairs at distance > D from A_e or B_e; 0 means the graph has diameter <= D. */
static long cost_now(void) {
    return (long)(2 * N - ball(0, D)) + (long)(2 * N - ball(N, D));
}

/* ------------------------------------------------------------ candidates */

typedef struct { int m, K, r; } Triple;
typedef struct {
    int m, K, r;
    int S[MAXDEG];
    int has_S;
    long best_cost;
} Cand;

static Triple pool[POOLMAX];
static int npool = 0;
static Cand cand[MAXCAND];
static int ncand = 0;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void build_pool(int lo, int hi) {
    npool = 0;
    for (int n = hi; n >= lo; n--) {
        for (int m = 2; m <= n; m++) {
            if (n % m) continue;
            int K = n / m;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_l(r, K, m) != 1 % m) continue;
                if (npool >= POOLMAX) return;
                pool[npool].m = m;
                pool[npool].K = K;
                pool[npool].r = r;
                npool++;
            }
        }
    }
}

static void pick_cands(void) {
    ncand = 0;
    for (int i = 0; i < npool && ncand < MAXCAND; i++) {
        int j = i + rndint(npool - i);
        Triple t = pool[j];
        pool[j] = pool[i];
        pool[i] = t;
        int n = t.m * t.K;
        if (n <= d) continue;
        cand[ncand].m = t.m;
        cand[ncand].K = t.K;
        cand[ncand].r = t.r;
        cand[ncand].has_S = 0;
        cand[ncand].best_cost = BIG;
        ncand++;
    }
}

/* Simulated annealing over the connection set of one group, until cost 0 or time limit.
 * Returns 1 if a valid connection set was found (saved in c->S). */
static int anneal(Cand *c, double tlim) {
    set_group(c->m, c->K, c->r);
    if (c->has_S) {
        memcpy(S, c->S, sizeof(int) * (size_t)d);
    } else {
        for (int k = 0; k < d; k++) {
            int x;
            do x = rndint(N); while (in_S_upto(x, k));
            S[k] = x;
        }
    }
    for (int k = 0; k < d; k++) set_col(k);
    long cur = cost_now();
    if (cur < c->best_cost) c->best_cost = cur;
    const double T = 1.5;
    long it = 0;
    while (cur > 0) {
        if ((++it & 63) == 0 && now() > tlim) break;
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S_upto(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            S[k] = old;
            set_col(k);
        }
        if (cur < c->best_cost) c->best_cost = cur;
    }
    memcpy(c->S, S, sizeof(int) * (size_t)d);
    c->has_S = 1;
    return cur == 0;
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lo hi]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = argc > 5 ? atoi(argv[5]) : 2;
    int hi = argc > 6 ? atoi(argv[6]) : MAXN - 1;

    double t0 = now();
    t_deadline = t0 + limit * 0.92 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) {
        print_complete();
        return 0;
    }

    long moore = moore_bound();
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (hi > moore / 2) hi = (int)(moore / 2);
    if (lo < d + 1) lo = d + 1;
    if (lo < 2) lo = 2;

    int best_idx = -1, best_N = 0;
    if (lo <= hi) {
        build_pool(lo, hi);
        pick_cands();
        for (int round = 0;; round++) {
            double slice = 0.08 * pow(1.8, (double)round);
            int progressed = 0;
            int stop = 0;
            for (int c = 0; c < ncand && !stop; c++) {
                int n = cand[c].m * cand[c].K;
                if (n <= best_N) continue;
                double rem = t_deadline - now();
                if (rem < 0.05) { stop = 1; break; }
                double tl = now() + (slice < rem ? slice : rem);
                progressed = 1;
                if (anneal(&cand[c], tl)) {
                    if (n > best_N) {
                        best_N = n;
                        best_idx = c;
                    }
                }
            }
            if (stop || !progressed) break;
        }
    }

    if (best_idx < 0) {
        print_complete();
        return 0;
    }
    set_group(cand[best_idx].m, cand[best_idx].K, cand[best_idx].r);
    memcpy(S, cand[best_idx].S, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + Rr[k][x]);
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


def search_window(d, D):
    """Range of group orders the C engine samples from."""
    if (d, D) == (4, 9):
        return 1500, 2700
    return 2, 3000


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.3:
        lo, hi = search_window(d, D)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
