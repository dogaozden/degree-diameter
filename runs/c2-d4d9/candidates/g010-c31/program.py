"""Program: two-orbit voltage lifts over groups (bold change), with the parent engine as a safe fallback.

Construction (new):
  * Group G of order N. Four orbits of vertices: A_0, A_1, B_0, B_1, each a copy of G, so 4N vertices.
    Base graph: 2x2 block matrix M = [[a, d-a], [d-a, a]] with row and column sums d.
    Each block (i, j) carries M[i][j] distinct voltages s, joining A_i,x to B_j,x*s.
  * Left multiplication is an automorphism, so the diameter condition reduces to four BFS runs,
    one from each orbit representative (A_0,e), (A_1,e), (B_0,e), (B_1,e).
  * Target: order 4N > record, so beat 2N = 4970 vertices with N >= 1243.
  * Search: simulated annealing over the voltages inside iterative-deepening rounds, over
    cyclic, metacyclic and SL/PSL(2,q) groups in ascending order of N.

Safety: the parent bi-Cayley engine runs first with about 40% of the budget. The two-orbit
engine then gets the rest. Each result is checked with lib.is_valid and kept only if it has
more vertices than the current best. The fallback is the known start or K_{d,d}.
"""
import time

import lib

C_PARENT = r'''
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
#define MAXCAND 48

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D;
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

/* ------------------------------------------------------------------ group */

static int N = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return N;
}

/* SL(2,q) or PSL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > idxm_cap) {
        free(idxm);
        idxm = malloc(sizeof(int) * (size_t)ks);
        idxm_cap = ks;
    }
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return N;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
    double frac;
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void add_meta(int Nval, Cand *arr, int *cnt) {
    for (int k = 2; k <= Nval / 3 && *cnt < MAXCAND; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && *cnt < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            c.frac = 0.06;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)T[(size_t)x * N + s];
        Ri[k][x] = (int)T[(size_t)x * N + si];
    }
}

static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------------ BFS cost */

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

/* Number of vertices not reached within D from A_e and from B_e (0 = valid). */
static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

/* Simulated annealing with sawtooth reheating. Returns 1 and leaves the best valid S in place. */
static int climb(double until) {
    if (N <= d + 1) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_S();
    long cur = cost_now();
    long bestc = cur;
    static int bestS[MAXDEG];
    memcpy(bestS, S, sizeof(int) * (size_t)d);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double tn = now();
            if (tn >= until) break;
            double f = (tn - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        } else {
            S[k] = old;
            set_col(k);
        }
    }
    if (bestc != 0) return 0;
    memcpy(S, bestS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
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
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 4970;
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long bestN = d;

    int recHalf = (int)(ref / 2);
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;
    int recN = recHalf + 1;

    static Cand all[3 * MAXCAND + 32];
    static Cand hi[MAXCAND], lo[MAXCAND];
    int na = 0, nh = 0, nl = 0;

    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            if (na >= 16) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            c.frac = 0.25;
            all[na++] = c;
        }
    }

    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_meta(Nv, lo, &nl);
    for (int Nv = recN; Nv <= hiN; Nv++) add_meta(Nv, hi, &nh);

    for (int i = 0; i < nl; i++) all[na++] = lo[i];
    for (int i = 0; i < nh; i++) all[na++] = hi[i];

    double budget0 = t_end - now();
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    double base_slice = budget0 * 0.03;
    if (base_slice < 0.3) base_slice = 0.3;
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < na; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &all[i];
            if ((long)c->N <= bestN) continue;
            if (2L * c->N > moore) continue;
            if (!apply_cand(c)) continue;
            double slice = base_slice * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestN = N;
                best = *c;
                memcpy(bS, S, sizeof(int) * (size_t)d);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(S, bS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + Rr[k][x]);
    return 0;
}
'''

C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXDEG 8
#define MAXG 80
#define MAXCAND 160
#define MAXVT (4 * MAXN)

#define T_HI 6.0
#define T_LO 0.15
#define CYCLES 3.0

static int d, D;
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

/* ------------------------------------------------------------------ group */

static int N = 0, e_id = 0;
static uint16_t *T = NULL;
static int *INV = NULL;

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
}

static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return N;
}

static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > idxm_cap) {
        free(idxm);
        idxm = malloc(sizeof(int) * (size_t)ks);
        idxm_cap = ks;
    }
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return N;
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int type, q, psl, m, k, r, N, a; } Cand;

static Cand groups[MAXG];
static int ngroups = 0;
static Cand cands[MAXCAND];
static int ncand = 0;

static void push_group(int type, int q, int psl, int m, int k, int r, int Nv) {
    if (ngroups >= MAXG) return;
    Cand c;
    memset(&c, 0, sizeof c);
    c.type = type; c.q = q; c.psl = psl; c.m = m; c.k = k; c.r = r; c.N = Nv;
    groups[ngroups++] = c;
}

static int cmp_group(const void *a, const void *b) {
    const Cand *x = (const Cand *)a;
    const Cand *y = (const Cand *)b;
    return (x->N > y->N) - (x->N < y->N);
}

/* ------------------------------------------------------------------ two-orbit state */

/* Orbits: A_0 = [0,N), A_1 = [N,2N), B_0 = [2N,3N), B_1 = [3N,4N).
   Block (i,j) has M[i][j] darts. Row i=0 uses a darts into B_0 and d-a into B_1;
   row i=1 uses d-a into B_0 and a into B_1. Dart (i,t) joins A_i,x to B_{AJ[i][t]}, x*AS[i][t]. */

static int M_a;
static int AJ[2][MAXDEG];
static int BI[2][MAXDEG], BT[2][MAXDEG];
static int AS[2][MAXDEG];
static int RA[2][MAXDEG][MAXN];
static int RB[2][MAXDEG][MAXN];
static int bestAS[2][MAXDEG], savedAS[2][MAXDEG];

static void setup_blocks(int a) {
    M_a = a;
    for (int t = 0; t < d; t++) AJ[0][t] = (t < a) ? 0 : 1;
    for (int t = 0; t < d; t++) AJ[1][t] = (t < d - a) ? 0 : 1;
    int cnt[2] = {0, 0};
    for (int i = 0; i < 2; i++)
        for (int t = 0; t < d; t++) {
            int j = AJ[i][t];
            BI[j][cnt[j]] = i;
            BT[j][cnt[j]] = t;
            cnt[j]++;
        }
}

static void set_dart(int i, int t) {
    int s = AS[i][t], si = INV[s];
    for (int x = 0; x < N; x++) {
        RA[i][t][x] = (int)T[(size_t)x * N + s];
        RB[i][t][x] = (int)T[(size_t)x * N + si];
    }
}

static void load_all(void) {
    for (int i = 0; i < 2; i++)
        for (int t = 0; t < d; t++) set_dart(i, t);
}

static int conflict_free(int i, int t, int s) {
    for (int t2 = 0; t2 < d; t2++)
        if (t2 != t && AJ[i][t2] == AJ[i][t] && AS[i][t2] == s) return 0;
    return 1;
}

static void randomize_state(void) {
    for (int i = 0; i < 2; i++)
        for (int t = 0; t < d; t++) AS[i][t] = -1;
    for (int i = 0; i < 2; i++)
        for (int t = 0; t < d; t++) {
            int s;
            do s = rndint(N); while (!conflict_free(i, t, s));
            AS[i][t] = s;
        }
    load_all();
}

static int apply_cand(const Cand *c) {
    int ok;
    if (c->type == 0) ok = build_meta(c->m, c->k, c->r);
    else ok = build_matrix(c->q, c->psl);
    if (!ok) return 0;
    setup_blocks(c->a);
    return 1;
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXVT];
static int tick = 0;
static int qv[MAXVT];

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int N2 = 2 * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < N2) {
                int i = (v >= N) ? 1 : 0;
                int x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int u = N2 + AJ[i][t] * N + RA[i][t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - N2;
                int j = (w >= N) ? 1 : 0;
                int y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int i = BI[j][k], t = BT[j][k];
                    int u = i * N + RB[i][t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices from one representative per orbit (0 = valid). */
static long cost_now(void) {
    long VT = 4L * N;
    long c = 0;
    c += VT - ball(e_id, D);
    c += VT - ball(N + e_id, D);
    c += VT - ball(2 * N + e_id, D);
    c += VT - ball(3 * N + e_id, D);
    return c;
}

/* Simulated annealing over the 2d voltages. Returns 1 and leaves the best valid state in place. */
static int climb(double until) {
    if (N < d + 2) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_state();
    long cur = cost_now();
    long bestc = cur;
    memcpy(bestAS, AS, sizeof AS);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double tn = now();
            if (tn >= until) break;
            double f = (tn - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int i = rndint(2);
        int t = rndint(d);
        int old = AS[i][t];
        int s;
        do s = rndint(N); while (s == old || !conflict_free(i, t, s));
        AS[i][t] = s;
        set_dart(i, t);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestAS, AS, sizeof AS);
            }
        } else {
            AS[i][t] = old;
            set_dart(i, t);
        }
    }
    if (bestc != 0) return 0;
    memcpy(AS, bestAS, sizeof AS);
    load_all();
    return 1;
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 4970;
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long Nmin = ref / 4 + 1;          /* 4N must beat ref */
    if (Nmin < d + 2) Nmin = d + 2;
    long Nmax = moore / 4;
    if (Nmax > MAXN) Nmax = MAXN;
    if (Nmin > Nmax) { printf("0 0\n"); return 0; }

    /* matrix groups SL/PSL(2,q) in the window */
    static const int qs[] = {7, 11, 13};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o >= Nmin && o <= Nmax) push_group(1, (int)q, psl, 0, 0, 0, (int)o);
        }
    /* metacyclic and cyclic groups, ascending order */
    for (long Nv = Nmin; Nv <= Nmax && ngroups < MAXG; Nv++) {
        push_group(0, 0, 0, (int)Nv, 1, 1, (int)Nv);   /* cyclic Z_Nv */
        for (int k = 2; k <= Nv / 3; k++) {
            if (Nv % k) continue;
            int m = (int)(Nv / k);
            if (m < 3) continue;
            int got = 0;
            for (int r = 2; r < m && got < 2; r++) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1) continue;
                push_group(0, 0, 0, m, k, r, (int)Nv);
                got++;
            }
        }
    }
    if (ngroups == 0) { printf("0 0\n"); return 0; }
    qsort(groups, (size_t)ngroups, sizeof(Cand), cmp_group);

    /* each group gets block parameters a = d/2 and a = 1 */
    int avals[2], nav = 0;
    avals[nav++] = d / 2;
    if (d / 2 != 1) avals[nav++] = 1;
    for (int g = 0; g < ngroups; g++)
        for (int ai = 0; ai < nav && ncand < MAXCAND; ai++) {
            cands[ncand] = groups[g];
            cands[ncand].a = avals[ai];
            ncand++;
        }

    long bestN = Nmin - 1;
    int have = 0, bestIdx = -1;
    double budget0 = t_end - now();
    double base_slice = budget0 / (3.0 * (double)ncand);
    if (base_slice < 0.3) base_slice = 0.3;

    for (int round = 0; round < 10; round++) {
        for (int ci = 0; ci < ncand; ci++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *c = &cands[ci];
            if ((long)c->N <= bestN) continue;
            if (4L * c->N > moore) continue;
            if (!apply_cand(c)) continue;
            double slice = base_slice * (double)(1 << round);
            if (slice > rem) slice = rem;
            if (climb(now() + slice)) {
                have = 1;
                bestN = N;
                bestIdx = ci;
                memcpy(savedAS, AS, sizeof AS);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { printf("0 0\n"); return 0; }
    if (!apply_cand(&cands[bestIdx])) { printf("0 0\n"); return 0; }
    memcpy(AS, savedAS, sizeof AS);
    load_all();
    if (cost_now() != 0) { printf("0 0\n"); return 0; }

    printf("%d %d\n", 4 * N, 2 * N * d);
    for (int i = 0; i < 2; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++) {
                int u = i * N + x;
                int v = 2 * N + AJ[i][t] * N + RA[i][t][x];
                printf("%d %d\n", u, v);
            }
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


def _improve(best, source, args, budget, d, D):
    """Run one C engine; keep its output only if it is valid and larger than best."""
    try:
        text = lib.run_c(source, args, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            return out
    except Exception:
        pass   # keep the valid fallback
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.85 * time_limit - 1.0
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best   # already a Moore graph; nothing to search for
    ref = REF_VERTICES.get((d, D), 4970)

    # 1. Safe parent engine first, so the record is kept if it is reached quickly.
    bp = 0.4 * (deadline - time.monotonic())
    if bp > 0.2:
        best = _improve(best, C_PARENT, [d, D, seed, bp, ref], bp, d, D)

    # 2. Bold two-orbit lift search with the remaining time, aiming above the current best.
    rem = deadline - time.monotonic()
    if rem > 0.2:
        lift_ref = max(ref, best[0])
        best = _improve(best, C_LIFT, [d, D, seed, rem, lift_ref], rem, d, D)

    return best
