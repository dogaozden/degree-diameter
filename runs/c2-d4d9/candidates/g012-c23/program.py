"""Program: Haar-type Cayley bipartite graphs over finite groups, found by annealing connection sets.

Different construction from the parent's voltage lifts:
  * A Haar graph over a group G of order N has parts A = G and B = G, with a_x ~ b_{x s} for s in S,
    where |S| = d. It is bipartite and d-regular on 2N vertices.
  * Left translation by g maps a_x -> a_{gx}, b_y -> b_{gy}, so it is an automorphism. Hence every
    A vertex is equivalent to a_e, and every B vertex to b_e. Diameter <= D holds iff a_e and b_e
    both reach all 2N vertices within D steps. Each check is one BFS, so the cost is cheap.
  * C searches over the connection set S (d group elements) by simulated annealing, minimising the
    number of unreached vertices from a_e and b_e. Orders N from ceil((ref+1)/2) upward are tried in
    turn, so the largest valid order found wins. Several groups per order are tried: metacyclic
    Z_m x| Z_k (including dihedral-type r = -1) and non-cyclic abelian Z_m x Z_k.

Safety: the C engine prints "0 0" when nothing is found. Python validates every output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
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

#define MAXG 2800
#define MAXD 8
#define MAXC 64
#define T_HI 3.0
#define T_LO 0.2
#define CYCLES 5.0

static int d, D;
static double usable, t_end;

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

/* ------------------------------------------------------------------ groups */

static int N = 1;                 /* current group order; identity is element 0 */
static uint16_t T[MAXG * MAXG];   /* T[x*N+y] = x*y */
static int INV[MAXG];

static void finish_group(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (T[(size_t)x * N + y] == 0) { INV[x] = y; break; }
    }
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static void build_meta(int m, int k, int r) {
    static int pw[MAXG];
    N = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = pw[b - 1] * r % m;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    finish_group();
}

/* Z_m x Z_k (direct product), element (a,b) coded as a*k+b. */
static void build_abel(int m, int k) {
    N = m * k;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    finish_group();
}

typedef struct { int type; long m, k, r; } Grp;   /* type 0 metacyclic, 1 abelian */

static int build_group(const Grp *g) {
    long n = g->m * g->k;
    if (n < 2 || n > MAXG) return 0;
    if (g->type == 0) build_meta((int)g->m, (int)g->k, (int)g->r);
    else build_abel((int)g->m, (int)g->k);
    return 1;
}

static int gen_groups(long ord, Grp *out) {
    int cnt = 0;
    for (long k = 2; k <= ord / 3 && cnt < MAXC - 2; k++) {
        if (ord % k) continue;
        long m = ord / k;
        if (m < 3) continue;
        if (powmod_l(m - 1, k, m) == 1) {
            out[cnt].type = 0; out[cnt].m = m; out[cnt].k = k; out[cnt].r = m - 1; cnt++;
        }
        for (int t = 0; t < 300; t++) {
            long r = 2 + rndint((int)(m - 2));
            if (gcd_l(r, m) != 1 || powmod_l(r, k, m) != 1) continue;
            out[cnt].type = 0; out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++;
            break;
        }
    }
    for (long k = 2; k * k <= ord && cnt < MAXC; k++) {
        if (ord % k) continue;
        long m = ord / k;
        if (gcd_l(m, k) == 1) continue;
        out[cnt].type = 1; out[cnt].m = m; out[cnt].k = k; out[cnt].r = 0; cnt++;
    }
    return cnt;
}

/* ------------------------------------------------------------------ Haar graph cost */

static int S[MAXD], SI[MAXD];     /* connection set and its inverses */
static int elite[MAXD];
static int stampv[2 * MAXG];
static int qv[2 * MAXG];
static int tick = 0;

static int in_set(int g, int cnt) {
    for (int i = 0; i < cnt; i++) if (S[i] == g) return 1;
    return 0;
}

/* Vertices reached within D of source (A vertices 0..N-1, B vertices N..2N-1). */
static int reach(int src) {
    if (++tick == 0x7fffffff) { memset(stampv, 0, sizeof stampv); tick = 1; }
    int head = 0, tail = 0;
    stampv[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < N) {
                const uint16_t *row = &T[(size_t)v * N];
                for (int k = 0; k < d; k++) {
                    int u = N + row[S[k]];
                    if (stampv[u] != tick) { stampv[u] = tick; qv[tail++] = u; }
                }
            } else {
                const uint16_t *row = &T[(size_t)(v - N) * N];
                for (int k = 0; k < d; k++) {
                    int u = row[SI[k]];
                    if (stampv[u] != tick) { stampv[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices from a_e and b_e; 0 means the Haar graph of S has diameter <= D. */
static long eval_cost(void) {
    for (int k = 0; k < d; k++) SI[k] = INV[S[k]];
    long c = (long)(2 * N - reach(0));
    c += (long)(2 * N - reach(N));
    return c;
}

/* Annealing over the connection set; returns 1 with a valid S left in place. */
static int anneal(double until) {
    for (int k = 0; k < d; k++) {
        int g;
        do g = rndint(N); while (in_set(g, k));
        S[k] = g;
    }
    long cur = eval_cost();
    if (cur == 0) return 1;
    long bestc = cur;
    memcpy(elite, S, sizeof(int) * (size_t)d);
    double start = now(), span = until - start;
    if (span <= 0.0) return 0;
    double temp = T_HI;
    int cyc_prev = -1;
    unsigned long it = 0;
    for (;;) {
        if ((++it & 31) == 0) {
            double tm = now();
            if (tm >= until) return 0;
            double ph = (tm - start) / span * CYCLES;
            int cyc = (int)floor(ph);
            double fr = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, fr);
            if (cyc != cyc_prev) {
                cyc_prev = cyc;
                memcpy(S, elite, sizeof(int) * (size_t)d);
                cur = bestc;
            }
        }
        int i = rndint(d);
        int g = rndint(N);
        if (in_set(g, d)) continue;
        int old = S[i];
        S[i] = g;
        long c2 = eval_cost();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = c2;
            if (cur == 0) return 1;
            if (cur < bestc) {
                bestc = cur;
                memcpy(elite, S, sizeof(int) * (size_t)d);
            }
        } else {
            S[i] = old;
        }
    }
}

/* ------------------------------------------------------------------ output */

static void print_graph(void) {
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + T[(size_t)x * N + S[k]]);
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit lo_half hi_half\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]), hi = atol(argv[6]);

    double t0 = now();
    usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { puts("0 0"); return 0; }

    long moore = moore_bound();
    if (hi > MAXG - 1) hi = MAXG - 1;
    if (hi > moore / 2) hi = moore / 2;
    if (lo < 2) lo = 2;

    int found = 0;
    Grp bestG;
    int bestS[MAXD];
    double slice_n = usable * 0.02;
    if (slice_n < 0.3) slice_n = 0.3;

    for (long ord = lo; ord <= hi; ord++) {
        if (now() >= t_end) break;
        Grp G[MAXC];
        int cnt = gen_groups(ord, G);
        if (cnt == 0) continue;
        for (int i = cnt - 1; i > 0; i--) {
            int j = rndint(i + 1);
            Grp tmp = G[i]; G[i] = G[j]; G[j] = tmp;
        }
        if (cnt > 6) cnt = 6;
        double per = slice_n / cnt;
        for (int i = 0; i < cnt; i++) {
            double rem = t_end - now();
            if (rem <= 0.0) break;
            double sl = per < rem ? per : rem;
            if (!build_group(&G[i])) continue;
            if (anneal(now() + sl)) {
                found = 1;
                bestG = G[i];
                memcpy(bestS, S, sizeof(int) * (size_t)d);
                break;
            }
        }
    }

    if (!found) { puts("0 0"); return 0; }
    if (!build_group(&bestG)) { puts("0 0"); return 0; }
    memcpy(S, bestS, sizeof(int) * (size_t)d);
    if (eval_cost() != 0) { puts("0 0"); return 0; }
    print_graph();
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}
MAX_HALF_ORDER = 2799


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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 0.2 and d >= 2 and D >= 2:
        ref = REF_VERTICES.get((d, D), best[0])
        moore = lib.moore_bound(d, D)
        lo = ref // 2 + 1                       # Haar graph of order 2N beats ref iff N > ref/2
        hi = min(lo + 250, moore // 2, MAX_HALF_ORDER)
        if lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), lo, hi],
                                 timeout=budget + 5)
                n, edges = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
            except Exception:
                pass   # keep the valid fallback
    return best
