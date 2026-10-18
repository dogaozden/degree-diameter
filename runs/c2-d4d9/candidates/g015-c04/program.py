"""Program: bi-Cayley lifts over metacyclic groups, greedy-coverage start plus annealing.

Construction (new in this version):
  * One base vertex per side (P = 1), so the lift is a bi-Cayley graph over a
    non-abelian metacyclic group G = Z_m x|_r Z_k of order N. Vertices are A(x) and
    B(y), x, y in G, and A(x) ~ B(x*g_t) for d distinct voltages g_t. Left
    multiplication is an automorphism, so diameter <= D iff BFS from A(e) and from B(e)
    reaches all 2N vertices within D steps.
  * Abelian groups (r = 1) are skipped, since abelian bi-Cayley graphs have tiny balls.
  * Candidate orders N run upward from ref/2 + 1, so each accepted lift has 2N > ref.
    Each candidate gets a time slice. A greedy pass picks voltages one by one to maximise
    the ball coverage, and simulated annealing with cyclic reheating then repairs the
    remaining unreached pairs. The search only accepts cost 0, and the lift is re-verified
    before output.

Safety: if nothing is found, the C engine prints K_{d,d}. Python checks every output
with lib.is_valid and keeps the best valid graph, falling back to the known start.
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
#define MAXD 8
#define MAXCAND 40000
#define T_HI 6.0
#define T_LO 0.3
#define CYCLES 4.0

static int d, D;
static long MOORE, REFV;
static double usable;

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

/* ------------------------------------------------------------ group Z_M x|_R Z_K */

static int M = 1, K = 1, R = 1, NG = 1;
static int PW[MAXN];

static void set_group(int m, int k, int r) {
    M = m;
    K = k;
    R = r;
    NG = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
}

/* (a,b)(c,e) = (a + r^b c, b + e), element (a,b) coded as a*K+b. */
static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    int aa = (int)(((long)a + (long)PW[b] * c) % M);
    int bb = (b + e) % K;
    return aa * K + bb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    int aa = (int)((M - ((long)PW[nb] * a) % M) % M);
    return aa * K + nb;
}

/* ------------------------------------------------------------ voltage state */

static int vol[MAXD];
static int FW[MAXD][MAXN];   /* FW[t][x] = x * g_t : A side -> B side index */
static int BW[MAXD][MAXN];   /* BW[t][y] = y * g_t^{-1} : B side -> A side index */
static int nact = 0;
static int usedv[MAXN];

static void set_dart(int t, int g) {
    vol[t] = g;
    int gi = ginv(g);
    for (int x = 0; x < NG; x++) {
        FW[t][x] = gmul(x, g);
        BW[t][x] = gmul(x, gi);
    }
}

static int clashes(int t, int g) {
    for (int s = 0; s < d; s++)
        if (s != t && vol[s] == g) return 1;
    return 0;
}

/* ------------------------------------------------------------ BFS cost */

static int stampv[2 * MAXN];
static int tick = 0;
static int qv[2 * MAXN];

static int ball(int src) {
    if (++tick > 1000000000) {
        memset(stampv, 0, sizeof stampv);
        tick = 1;
    }
    int head = 0, tail = 0;
    stampv[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < NG) {
                for (int t = 0; t < nact; t++) {
                    int u = NG + FW[t][v];
                    if (stampv[u] != tick) { stampv[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - NG;
                for (int t = 0; t < nact; t++) {
                    int u = BW[t][y];
                    if (stampv[u] != tick) { stampv[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices from A(e) and B(e); 0 means valid. */
static long cost_now(void) {
    long c = 0;
    c += 2L * NG - ball(0);
    c += 2L * NG - ball(NG);
    return c;
}

/* ------------------------------------------------------------ construction */

static void greedy_init(void) {
    memset(usedv, 0, sizeof(int) * (size_t)NG);
    for (int t = 0; t < d; t++) {
        nact = t + 1;
        long bestc = 0;
        int bestg = -1, cnt = 0;
        int off = rndint(NG);
        for (int s = 0; s < NG; s++) {
            int g = (s + off) % NG;
            if (usedv[g]) continue;
            set_dart(t, g);
            long c = cost_now();
            if (bestg < 0 || c < bestc) {
                bestc = c;
                bestg = g;
                cnt = 1;
            } else if (c == bestc && rndint(++cnt) == 0) {
                bestg = g;
            }
        }
        set_dart(t, bestg);
        usedv[bestg] = 1;
    }
    nact = d;
}

/* Greedy start, then annealing on voltages. Returns 1 with a valid lift in vol. */
static int anneal(double until) {
    nact = d;
    greedy_init();
    if (now() >= until) return 0;
    long cur = cost_now();
    if (cur == 0) return 1;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    double temp = T_HI;
    long it = 0;
    for (;;) {
        if ((++it & 63) == 0) {
            double tm = now();
            if (tm >= until) return 0;
            double ph = (tm - start) / span * CYCLES;
            double fr = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, fr);
        }
        int t = rndint(d);
        int g = rndint(NG);
        if (g == vol[t] || clashes(t, g)) continue;
        int old = vol[t];
        set_dart(t, g);
        long c2 = cost_now();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            set_dart(t, old);
        }
    }
}

/* ------------------------------------------------------------ candidates */

typedef struct {
    int m, k, r, N;
} Cand;

static Cand CAND[MAXCAND];
static int nc = 0;

/* Metacyclic groups with K >= 2 and R >= 2 (non-abelian), ascending in N. */
static void gen_candidates(long Nlo, long Nhi) {
    nc = 0;
    for (long N = Nlo; N <= Nhi; N++) {
        for (long k = 2; k <= N / 3; k++) {
            if (N % k) continue;
            long m = N / k;
            if (m < 3) continue;
            int got = 0;
            for (long r = 2; r < m && got < 2; r++) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1 % m) continue;
                if (nc < MAXCAND) {
                    CAND[nc].m = (int)m;
                    CAND[nc].k = (int)k;
                    CAND[nc].r = (int)r;
                    CAND[nc].N = (int)N;
                    nc++;
                }
                got++;
            }
        }
    }
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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
    usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    double t_end = t0 + usable;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    MOORE = moore_bound();
    if (ref <= 0) ref = 2L * d;
    REFV = ref;

    long Nlo = ref / 2 + 1;           /* 2N > ref */
    long Nhi = MOORE / 2;
    if (Nhi > MAXN) Nhi = MAXN;
    if (Nlo < 3) Nlo = 3;
    if (Nlo > Nhi) { print_complete(); return 0; }

    gen_candidates(Nlo, Nhi);

    long bestV = REFV;
    int found = 0;
    int bm = 0, bk = 0, br = 0;
    int bvol[MAXD];

    for (int i = 0; i < nc; i++) {
        double rem = t_end - now();
        if (rem < 0.5) break;
        Cand *c = &CAND[i];
        if (2L * c->N <= bestV) continue;
        if (2L * c->N > MOORE) continue;
        set_group(c->m, c->k, c->r);
        double slice = usable * 0.06;
        if (slice > rem) slice = rem;
        if (anneal(now() + slice)) {
            found = 1;
            bestV = 2L * NG;
            bm = c->m;
            bk = c->k;
            br = c->r;
            memcpy(bvol, vol, sizeof(int) * (size_t)d);
        }
    }

    if (!found) { print_complete(); return 0; }

    set_group(bm, bk, br);
    nact = d;
    for (int t = 0; t < d; t++) set_dart(t, bvol[t]);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %d\n", 2 * NG, d * NG);
    for (int x = 0; x < NG; x++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", x, NG + gmul(x, bvol[t]));
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
        start = lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(start[0], start[1], d, D):
        start = (2, [(0, 1)])
    best = start
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
