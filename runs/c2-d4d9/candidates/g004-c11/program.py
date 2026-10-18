"""Program: bi-Cayley graphs over PSL(2,q), SL(2,q) and metacyclic groups Z_m x| Z_k.

New in this version:
  * Metacyclic family: groups Z_m x|_r Z_k (r^k = 1 mod m, r != 1) with per-side order in
    [2480, 3600]. These fill the gap between PSL(2,17) (2448) and PSL(2,19) (3420) that
    the matrix groups miss. The C engine builds them directly.
  * Annealing search: Metropolis moves on one connection element at a time, with a cost
    that breaks ties by the number of pairs still unreached at radius D-1. Restarts run in
    time-based epochs.
  * Two-pass schedule: a quick pass over small groups secures a fallback, then the larger
    targets (closest to per-side order 3420) get most of the remaining time.

Symmetry: for vertices A_x = x and B_y = N + y, left multiplication is an automorphism,
so diameter <= D iff BFS from A_e and from B_e reaches all 2N vertices within D steps.

Safety: the C engine always prints a valid graph (K_{d,d} if nothing is found). Python
checks it with lib.is_valid and keeps the best valid graph, falling back to the known
start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over PSL(2,q), SL(2,q) and metacyclic groups, with annealing.
 * Usage:  prog d D seed time_limit        (stdin is ignored)
 * Output: "n m" then m lines "u v": a bipartite graph, every degree d, diameter <= D
 *         (K_{d,d} if nothing better was found).
 *
 * Vertices: A_x = x, B_y = N + y, for group elements x, y in 0..N-1.
 * Edges: A_x -- B_{x*s_k} for k < d.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 12200
#define MAXV (2 * MAXG)
#define MAXDEG 8
#define MAXK 512
#define MAXRAW 20000
#define NMETA 8
#define MAXCAND 40
#define META_LO 2480
#define META_HI 3600
#define T_HI 1.5
#define T_LO 0.05

static int d, D;
static double deadline;

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

/* ------------------------------------------------------------------ groups */

static int gtype = 0;     /* 0: PSL/SL(2,q) matrices; 1: metacyclic Z_MM x| Z_KK */
static int q, isPSL;
static int N, e_id;
static int gm[MAXG][4];   /* matrix entries a,b,c,e of element x = [[a,b],[c,e]] */
static int *idx = NULL;   /* key -> element index */
static int idx_cap = 0;
static int MM, KK, RR;    /* metacyclic parameters: element (a,b) coded as a*KK+b */
static int pw[MAXK];      /* pw[b] = RR^b mod MM */

static int canon_key(int a, int b, int c, int e) {
    int k = ((a * q + b) * q + c) * q + e;
    if (!isPSL) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int lookup(int a, int b, int c, int e) { return idx[canon_key(a, b, c, e)]; }

static int build_matrix(int qq, int psl) {
    gtype = 0;
    q = qq;
    isPSL = psl;
    int ks = q * q * q * q;
    if (ks > idx_cap) {
        free(idx);
        idx = malloc(sizeof(int) * (size_t)ks);
        if (!idx) exit(1);
        idx_cap = ks;
    }
    for (int i = 0; i < ks; i++) idx[i] = -1;
    N = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (N >= MAXG) return 0;
                    gm[N][0] = a; gm[N][1] = b; gm[N][2] = c; gm[N][3] = e;
                    idx[own] = N;
                    N++;
                }
    e_id = lookup(1, 0, 0, 1);
    return N;
}

/* Z_m x|_r Z_k: (a,b)(c,d) = (a + r^b c, b + d). Needs r^k = 1 mod m. */
static int build_meta(int m, int k, int r) {
    if (m < 2 || k < 1 || k > MAXK || (long)m * k > MAXG) return 0;
    gtype = 1;
    MM = m; KK = k; RR = r;
    N = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    if ((long)pw[k - 1] * r % m != 1 % m) return 0;
    e_id = 0;
    return N;
}

static int gmul(int x, int y) {
    if (gtype == 0) {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        int sa = gm[y][0], sb = gm[y][1], sc = gm[y][2], se = gm[y][3];
        return lookup((a * sa + b * sc) % q, (a * sb + b * se) % q,
                      (c * sa + e * sc) % q, (c * sb + e * se) % q);
    }
    int a = x / KK, b = x % KK, c = y / KK, dd = y % KK;
    int na = (a + pw[b] * c) % MM;
    int nb = (b + dd) % KK;
    return na * KK + nb;
}

static int ginv(int x) {
    if (gtype == 0)
        return lookup(gm[x][3], (q - gm[x][1]) % q, (q - gm[x][2]) % q, gm[x][0]);
    int a = x / KK, b = x % KK;
    int nb = (KK - b) % KK;
    int na = (MM - (pw[nb] * a) % MM) % MM;
    return na * KK + nb;
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXG];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXG];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = ginv(s);
    for (int x = 0; x < N; x++) {
        Rr[k][x] = gmul(x, s);
        Ri[k][x] = gmul(x, si);
    }
}

static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
}

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* BFS from src to depth dmax. Returns the number reached within dmax steps,
 * and in *prevc the number reached within dmax-1 steps. */
static int ball2(int src, int dmax, int *prevc) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0, pc = -1;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax; lvl++) {
        if (lvl == dmax - 1) pc = tail;
        if (head >= tail) break;
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
    if (pc < 0) pc = tail;
    *prevc = pc;
    return tail;
}

/* uD: pairs unreached within D (0 means valid). cost adds a tie-breaker below 1. */
static void eval_cost(int *uD, double *cost) {
    int pA = 0, pB = 0;
    int rA = ball2(e_id, D, &pA);
    int rB = ball2(N + e_id, D, &pB);
    int full = 2 * N;
    int ud = (full - rA) + (full - rB);
    int up = (full - pA) + (full - pB);
    *uD = ud;
    *cost = (double)ud + (double)up / (4.0 * N + 1.0);
}

/* Simulated annealing over the connection set of the current group, with random
 * restarts in time-based epochs. Returns 1 with S valid (uD == 0), else 0. */
static int anneal(double until) {
    double span = until - now();
    if (span <= 0) return 0;
    double epoch = span / 3.0;
    if (epoch < 1.0) epoch = span;
    while (now() < until) {
        randomize_S();
        int ud;
        double cur;
        eval_cost(&ud, &cur);
        if (ud == 0) return 1;
        double ep0 = now();
        double ep1 = ep0 + epoch;
        if (ep1 > until) ep1 = until;
        double len = ep1 - ep0;
        if (len <= 0) break;
        for (;;) {
            double tn = now();
            if (tn >= ep1) break;
            double frac = (tn - ep0) / len;
            double T = T_HI * pow(T_LO / T_HI, frac);
            int k = rndint(d);
            int old = S[k];
            int x;
            do x = rndint(N); while (in_S(x, d));
            S[k] = x;
            set_col(k);
            int nu;
            double nc;
            eval_cost(&nu, &nc);
            if (nu == 0) return 1;
            double dl = nc - cur;
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                cur = nc;
            } else {
                S[k] = old;
                set_col(k);
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int kind, q, psl, m, k, r; long bi; double key; } Cand;

static Cand raw[MAXRAW];
static int nraw = 0;
static Cand cand[MAXCAND];
static int ncand = 0;

static int cmp_bi(const void *a, const void *b) {
    long x = ((const Cand *)a)->bi, y = ((const Cand *)b)->bi;
    return (x > y) - (x < y);
}
static int cmp_key(const void *a, const void *b) {
    double x = ((const Cand *)a)->key, y = ((const Cand *)b)->key;
    return (x > y) - (x < y);
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int build_cand(const Cand *c) {
    return c->kind == 0 ? build_matrix(c->q, c->psl) : build_meta(c->m, c->k, c->r);
}

static int have_best = 0;
static int best_n = 0;          /* per-side order of best valid graph */
static Cand bestc;
static int bestS[MAXDEG];

static int try_cand(const Cand *c, double until) {
    if (build_cand(c) <= 0) return 0;
    if (!anneal(until)) return 0;
    if (!have_best || N > best_n) {
        have_best = 1;
        best_n = N;
        bestc = *c;
        memcpy(bestS, S, sizeof(int) * (size_t)d);
    }
    return 1;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    deadline = t0 + limit - 1.0;
    if (limit < 1.0) deadline = t0 + limit * 0.5;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();

    /* Matrix-group candidates: PSL(2,q) and SL(2,q). */
    static const int primes[] = {5, 7, 11, 13, 17, 19, 23};
    ncand = 0;
    for (unsigned pi = 0; pi < sizeof primes / sizeof primes[0]; pi++) {
        for (int psl = 0; psl < 2; psl++) {
            long qq = primes[pi];
            long ord = qq * (qq * qq - 1);
            if (psl) ord /= 2;
            long bi = 2 * ord;
            if (bi > moore || ord > MAXG || ncand >= MAXCAND) continue;
            Cand *c = &cand[ncand++];
            c->kind = 0; c->q = (int)qq; c->psl = psl; c->m = 0; c->k = 0; c->r = 0;
            c->bi = bi;
            c->key = fabs(log((double)bi) - log(6840.0));
        }
    }

    /* Metacyclic candidates Z_m x|_r Z_k with per-side order in [META_LO, META_HI]. */
    if (moore >= 2L * META_LO) {
        for (int k = 4; k <= 60 && nraw < MAXRAW; k++) {
            int mlo = (META_LO + k - 1) / k;
            if (mlo < 3) mlo = 3;
            int mhi = META_HI / k;
            for (int m = mlo; m <= mhi && nraw < MAXRAW; m++) {
                if (2L * m * k > moore) break;
                for (int r = 2; r < m; r++) {
                    if (gcd_int(r, m) != 1) continue;
                    long p = 1 % m;
                    for (int i = 0; i < k; i++) p = p * r % m;
                    if (p != 1 % m) continue;
                    Cand *c = &raw[nraw++];
                    c->kind = 1; c->q = 0; c->psl = 0; c->m = m; c->k = k; c->r = r;
                    c->bi = 2L * m * k;
                    c->key = fabs(log((double)c->bi) - log(6840.0));
                    break;
                }
            }
        }
        qsort(raw, (size_t)nraw, sizeof(Cand), cmp_key);
        for (int i = 0; i < nraw && i < NMETA && ncand < MAXCAND; i++) cand[ncand++] = raw[i];
    }

    /* Pass A: quick pass over small matrix groups, ascending order, to secure a fallback. */
    qsort(cand, (size_t)ncand, sizeof(Cand), cmp_bi);
    for (int i = 0; i < ncand; i++) {
        Cand *c = &cand[i];
        if (c->bi > 4400) break;
        if (c->bi <= 2L * best_n) continue;
        double rem = deadline - now();
        if (rem < 0.5) break;
        double bud = rem * 0.25;
        if (bud > 3.0) bud = 3.0;
        try_cand(c, now() + bud);
    }

    /* Pass B: larger targets, closest to per-side order 3420 first, most of the time. */
    qsort(cand, (size_t)ncand, sizeof(Cand), cmp_key);
    for (int i = 0; i < ncand; i++) {
        Cand *c = &cand[i];
        if (c->bi <= 2L * best_n) continue;
        double rem = deadline - now();
        if (rem < 1.0) break;
        double bud = 0.45 * rem;
        try_cand(c, now() + bud);
    }

    if (!have_best) {
        print_complete();
        return 0;
    }
    build_cand(&bestc);
    memcpy(S, bestS, sizeof(int) * (size_t)d);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 6.0)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
