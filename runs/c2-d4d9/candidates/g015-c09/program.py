"""Program: bi-Cayley (Haar-type) lifts over metacyclic groups with generator annealing.

Substantially different construction from the parent's voltage lifts:
  * One vertex per side. Vertices are A(x) and B(y) for x, y in a finite group G of
    order N. Each generator s_1..s_d (distinct, non-identity) gives edges
    A(x)-B(x s_t). The graph is simple, bipartite and d-regular on 2N vertices.
  * Left multiplication by G is an automorphism, so diameter <= D iff BFS from A(e)
    and from B(e) reaches all 2N vertices within D steps. One evaluation costs about
    4*N*d operations, so annealing runs hundreds of thousands of evaluations.
  * Groups are metacyclic Z_m x| Z_k (element (a,b), (a,b)(c,e) = (a + r^b c, b + e),
    r^k = 1 mod m, gcd(r,m) = 1). Multiplication and inverse are computed by formula,
    so no multiplication table is stored.
  * Schedule: a fallback pass (descending orders, first success kept) guarantees a
    valid graph. The main pass then climbs upward from the target order 2N > ref,
    keeping the largest valid graph found.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks every output
with lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
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

#define MAXN 4096
#define MAXD 8
#define GMAX 6
#define CYC 3.0
#define T_HI 2.5
#define T_LO 0.15
#define PER_N 2.5

static int d, D;
static long moore_v;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
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

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int gm, gk, gr, N;
static int pw[MAXN];

static void set_group(int m, int k, int r) {
    gm = m;
    gk = k;
    gr = r;
    N = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    int aa = (a + pw[b] * c) % gm;
    int bb = (b + e) % gk;
    return aa * gk + bb;
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    int c = (gm - (int)((long)pw[nb] * a % gm)) % gm;
    return c * gk + nb;
}

/* ------------------------------------------------------------ bi-Cayley state */

static int S[MAXD], Si[MAXD];
static int FW[MAXD][MAXN];   /* FW[t][x] = x * s_t        : A(x) -> B */
static int BW[MAXD][MAXN];   /* BW[t][y] = y * s_t^{-1}   : B(y) -> A */

static void set_gen(int t) {
    for (int x = 0; x < N; x++) {
        FW[t][x] = gmul(x, S[t]);
        BW[t][x] = gmul(x, Si[t]);
    }
}

/* ------------------------------------------------------------ cost */

static int stamp[2 * MAXN];
static int tick = 0;
static int qb[2 * MAXN];

/* Unreached vertices from A(e) and from B(e) within D steps; 0 means valid. */
static long cost_eval(void) {
    long total = 0;
    for (int src = 0; src < 2; src++) {
        if (++tick == 0x7ffffff0) {
            memset(stamp, 0, sizeof stamp);
            tick = 1;
        }
        int head = 0, tail = 0;
        int s0 = src ? N : 0;
        stamp[s0] = tick;
        qb[tail++] = s0;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            for (; head < end; head++) {
                int v = qb[head];
                if (v < N) {
                    for (int t = 0; t < d; t++) {
                        int u = N + FW[t][v];
                        if (stamp[u] != tick) { stamp[u] = tick; qb[tail++] = u; }
                    }
                } else {
                    int y = v - N;
                    for (int t = 0; t < d; t++) {
                        int u = BW[t][y];
                        if (stamp[u] != tick) { stamp[u] = tick; qb[tail++] = u; }
                    }
                }
            }
        }
        total += 2L * N - tail;
    }
    return total;
}

/* ------------------------------------------------------------ annealing over S */

/* Returns 1 with a valid S left in place, 0 if the time slice ends first. */
static int anneal(double until) {
    if (N - 1 < d) return 0;
    for (int t = 0; t < d; t++) {
        int g;
        int ok;
        do {
            g = 1 + rndint(N - 1);
            ok = 1;
            for (int s = 0; s < t; s++) if (S[s] == g) { ok = 0; break; }
        } while (!ok);
        S[t] = g;
    }
    for (int t = 0; t < d; t++) {
        Si[t] = ginv(S[t]);
        set_gen(t);
    }
    long cur = cost_eval();
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    double temp = T_HI;
    long it = 0;
    for (;;) {
        if (cur == 0) return 1;
        if ((++it & 31) == 0) {
            double tm = now();
            if (tm >= until) return 0;
            double ph = (tm - start) / span * CYC;
            double fr = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, fr);
        }
        int t = rndint(d);
        int g = 1 + rndint(N - 1);
        int dup = 0;
        for (int s = 0; s < d; s++) if (S[s] == g) { dup = 1; break; }
        if (dup) continue;
        int old = S[t], oldi = Si[t];
        S[t] = g;
        Si[t] = ginv(g);
        set_gen(t);
        long c2 = cost_eval();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = c2;
        } else {
            S[t] = old;
            Si[t] = oldi;
            set_gen(t);
        }
    }
}

/* ------------------------------------------------------------ group enumeration */

static int collect_groups(int Nv, int *M, int *K, int *R, int cap) {
    int cnt = 0;
    for (int k = 2; k <= Nv / 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        for (int r = 1; r < m && cnt < cap; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            M[cnt] = m;
            K[cnt] = k;
            R[cnt] = r;
            cnt++;
        }
    }
    return cnt;
}

/* Up to GMAX groups of order Nv, shuffled, non-abelian (r != 1) first. */
static int groups_for(int Nv, int *M, int *K, int *R) {
    static int tm[1024], tk[1024], tr[1024];
    int n = collect_groups(Nv, tm, tk, tr, 1024);
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int x;
        x = tm[i]; tm[i] = tm[j]; tm[j] = x;
        x = tk[i]; tk[i] = tk[j]; tk[j] = x;
        x = tr[i]; tr[i] = tr[j]; tr[j] = x;
    }
    int out = 0;
    for (int pass = 0; pass < 2; pass++) {
        int want_nonab = (pass == 0);
        for (int i = 0; i < n && out < GMAX; i++) {
            if ((tr[i] != 1) == want_nonab) {
                M[out] = tm[i];
                K[out] = tk[i];
                R[out] = tr[i];
                out++;
            }
        }
    }
    return out;
}

/* ------------------------------------------------------------ best so far */

static int have = 0;
static int bestN = 0, bgm = 0, bgk = 0, bgr = 0;
static int bS[MAXD];

static void save_best(void) {
    have = 1;
    bestN = N;
    bgm = gm;
    bgk = gk;
    bgr = gr;
    memcpy(bS, S, sizeof(int) * (size_t)d);
}

/* Try every group of order Nv until time `until`; returns 1 on success. */
static int try_N(int Nv, double until) {
    int M[GMAX], K[GMAX], R[GMAX];
    int G = groups_for(Nv, M, K, R);
    for (int i = 0; i < G; i++) {
        double tn = now();
        if (tn >= until) return 0;
        double slice = (until - tn) / (double)(G - i);
        set_group(M[i], K[i], R[i]);
        if (anneal(tn + slice)) {
            save_best();
            return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_best(void) {
    set_group(bgm, bgk, bgr);
    for (int t = 0; t < d; t++) {
        S[t] = bS[t];
        Si[t] = ginv(S[t]);
        set_gen(t);
    }
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++) printf("%d %d\n", x, N + FW[t][x]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    moore_v = moore_bound();
    if (ref <= 0) ref = moore_v / 4;
    if (ref < 2L * d + 4) ref = 2L * d + 4;

    long nstart = ref / 2 + 1;           /* group order giving 2N > ref */
    if (nstart <= d + 1) nstart = d + 2;
    long nhi = nstart * 13 / 10;
    if (nhi > MAXN - 1) nhi = MAXN - 1;
    if (2 * nhi > moore_v) nhi = moore_v / 2;

    /* Phase A: fallback. Descending candidates, stop at the first success. */
    double endA = t0 + 0.25 * usable;
    long cand[6] = {nstart - 1, nstart * 9 / 10, nstart * 7 / 10, nstart / 2, nstart / 4, 100};
    for (int i = 0; i < 6 && !have; i++) {
        long Nv = cand[i];
        if (Nv <= d + 1 || Nv > MAXN - 1 || 2 * Nv > moore_v) continue;
        double tn = now();
        if (tn >= endA) break;
        double share = (endA - tn) / (double)(6 - i);
        if (try_N((int)Nv, tn + share)) break;
    }

    /* Phase B: ascending from the target order; keep the largest success. */
    if (nstart <= nhi) {
        long nxt = nstart;
        while (nxt <= nhi && now() < t_end - 0.3) {
            double until = now() + PER_N;
            if (until > t_end) until = t_end;
            try_N((int)nxt, until);
            nxt++;
        }
    }

    if (!have) { print_complete(); return 0; }
    print_best();
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


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
        start = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best   # a Moore graph cannot be beaten
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 0.2:
        ref = REF_VERTICES.get((d, D), 0)
        if ref == 0 and best[0] > 2 * d:
            ref = best[0]
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
