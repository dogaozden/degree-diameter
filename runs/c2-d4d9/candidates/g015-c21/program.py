"""Program: two engines per case, keeping the best valid graph.

Engine A (C_PARENT): the g007-c25 bi-Cayley search over metacyclic and matrix groups, kept
as the safety net that already reaches the record.

Engine B (C_LIFT, new): multi-orbit voltage lifts. The vertex set is A_{i,x}, B_{j,y} with
i, j in 0..P-1 and x, y in a group G of order N, so there are 2PN vertices. Dart t from A_i
goes to B_{(i+O_t) mod P} with voltage V[i][t]. Each vertex has degree d, and the graph is
bipartite. Left multiplication by G is an automorphism, so the diameter is <= D iff BFS
from A_{i,e} and B_{j,e} (all i, j < P) reach every vertex within D steps. Candidates are
ordered by vertex count, smallest first, so the search aims just above the record, and
simulated annealing with random restarts searches the voltages.

Safety: each engine's output is parsed and checked with lib.is_valid, and it replaces the
best graph only if it is larger. The fallback is the known start or K_{d,d}.
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
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
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

#define MAXN 2500
#define MAXP 6
#define MAXDEG 8
#define MAXV 20000
#define MAXCAND 300

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

typedef struct {
    int type, q, psl, m, k, r, N, P;
} Cand;

static Cand cand[MAXCAND];
static int ncand = 0;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void push_cand(int type, int q, int psl, int m, int k, int r, int Nv, int Pv) {
    if (ncand >= MAXCAND) return;
    Cand c;
    c.type = type; c.q = q; c.psl = psl; c.m = m; c.k = k; c.r = r; c.N = Nv; c.P = Pv;
    cand[ncand++] = c;
}

static void add_order(int Nv, int Pv) {
    static const int qs[] = {5, 7, 11, 13, 17};
    for (unsigned qi = 0; qi < 5; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o == Nv) push_cand(1, (int)q, psl, 0, 0, 0, Nv, Pv);
        }
    for (int k = 2; k <= Nv / 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 1; r < m && got < 2; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            push_cand(0, 0, 0, m, k, r, Nv, Pv);
            got++;
        }
    }
}

/* Candidates ordered by vertex count 2*P*N, smallest first, starting at the record. */
static void gen_candidates(long ref, long moore) {
    ncand = 0;
    for (long H = ref / 2; H <= moore / 2 && ncand < MAXCAND; H++) {
        for (int Pv = 1; Pv <= MAXP && ncand < MAXCAND; Pv++) {
            if (H % Pv) continue;
            long Nv = H / Pv;
            if (Nv < 3 || Nv > MAXN) continue;
            add_order((int)Nv, Pv);
        }
    }
}

/* ------------------------------------------------------------------ lift state */

static int P = 1;
static int Ov[MAXDEG];            /* base offsets: dart t goes A_i -> B_{i+Ov[t]} */
static int V[MAXP][MAXDEG];       /* voltages */
static int Sinv[MAXP][MAXDEG];    /* inverses of voltages */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int PN = P * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < PN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int j = i + Ov[t];
                    if (j >= P) j -= P;
                    int u = PN + j * N + (int)T[(size_t)x * N + V[i][t]];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int i = j - Ov[t];
                    if (i < 0) i += P;
                    int u = i * N + (int)T[(size_t)y * N + Sinv[i][t]];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices summed over the 2P orbit representatives (0 = valid). */
static long cost_now(void) {
    long total = 2L * P * N;
    long c = 0;
    for (int i = 0; i < P; i++) c += total - ball(i * N + e_id, D);
    for (int j = 0; j < P; j++) c += total - ball(P * N + j * N + e_id, D);
    return c;
}

/* Voltages of darts sharing the same offset must differ, or the lift gets multi-edges. */
static int dup_conflict(int i, int t, int x) {
    for (int t2 = 0; t2 < d; t2++)
        if (t2 != t && Ov[t2] == Ov[t] && V[i][t2] == x) return 1;
    return 0;
}

static int dup_init(int i, int t, int x) {
    for (int t2 = 0; t2 < t; t2++)
        if (Ov[t2] == Ov[t] && V[i][t2] == x) return 1;
    return 0;
}

static int dup_free(void) {
    for (int i = 0; i < P; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (Ov[t] == Ov[t2] && V[i][t] == V[i][t2]) return 0;
    return 1;
}

static int random_config(void) {
    for (int t = 0; t < d; t++) Ov[t] = rndint(P);
    for (int i = 0; i < P; i++)
        for (int t = 0; t < d; t++) {
            int tries = 0, x;
            do {
                x = rndint(N);
                tries++;
            } while (tries < 10000 && dup_init(i, t, x));
            if (tries >= 10000) return 0;
            V[i][t] = x;
            Sinv[i][t] = INV[x];
        }
    return 1;
}

/* Simulated annealing with random restarts (new offsets and voltages each epoch).
   Returns 1 and leaves the valid state in the globals Ov, V, Sinv. */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    double epoch = span / 4.0;
    if (epoch < 0.6) epoch = 0.6;
    while (now() < until - 0.02) {
        if (!random_config()) continue;
        long cur = cost_now();
        long bestc = cur;
        int bestO[MAXDEG];
        int bestV[MAXP][MAXDEG];
        memcpy(bestO, Ov, sizeof Ov);
        memcpy(bestV, V, sizeof V);
        double ep0 = now();
        double ep1 = ep0 + epoch;
        if (ep1 > until) ep1 = until;
        double eps = ep1 - ep0;
        if (eps <= 0.0) break;
        double temp = T_HI;
        long it = 0;
        while (cur > 0) {
            if ((++it & 7) == 0) {
                double tn = now();
                if (tn >= ep1) break;
                double ph = (tn - ep0) / eps * CYCLES;
                ph -= floor(ph);
                temp = T_HI * pow(T_LO / T_HI, ph);
            }
            int i = rndint(P), t = rndint(d), x = rndint(N);
            if (x == V[i][t] || dup_conflict(i, t, x)) continue;
            int old = V[i][t], oldi = Sinv[i][t];
            V[i][t] = x;
            Sinv[i][t] = INV[x];
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    memcpy(bestO, Ov, sizeof Ov);
                    memcpy(bestV, V, sizeof V);
                }
            } else {
                V[i][t] = old;
                Sinv[i][t] = oldi;
            }
        }
        if (bestc == 0) {
            memcpy(Ov, bestO, sizeof Ov);
            memcpy(V, bestV, sizeof V);
            for (int i = 0; i < P; i++)
                for (int t = 0; t < d; t++) Sinv[i][t] = INV[V[i][t]];
            return 1;
        }
    }
    return 0;
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

    rng_state ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    gen_candidates(ref, moore);
    if (ncand == 0) { print_complete(); return 0; }

    double budget0 = t_end - now();
    double base = budget0 / 60.0;
    if (base < 0.3) base = 0.3;

    int have = 0;
    long bestV_n = 0;
    Cand bestc;
    memset(&bestc, 0, sizeof bestc);
    int bO[MAXDEG];
    int bVv[MAXP][MAXDEG];
    int bP = 1;
    memset(bO, 0, sizeof bO);
    memset(bVv, 0, sizeof bVv);

    for (int round = 0; round < 10; round++) {
        for (int i = 0; i < ncand; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cand[i];
            long vtx = 2L * c->P * c->N;
            if (vtx <= bestV_n) continue;
            if (vtx > moore) continue;
            if (!apply_cand(c)) continue;
            P = c->P;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestV_n = vtx;
                bestc = *c;
                bP = P;
                memcpy(bO, Ov, sizeof Ov);
                memcpy(bVv, V, sizeof V);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&bestc)) { print_complete(); return 0; }
    P = bP;
    memcpy(Ov, bO, sizeof Ov);
    memcpy(V, bVv, sizeof V);
    for (int i = 0; i < P; i++)
        for (int t = 0; t < d; t++) Sinv[i][t] = INV[V[i][t]];
    if (!dup_free() || cost_now() != 0) { print_complete(); return 0; }

    int PN = P * N;
    printf("%d %d\n", 2 * PN, PN * d);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++) {
                int j = i + Ov[t];
                if (j >= P) j -= P;
                int y = (int)T[(size_t)x * N + V[i][t]];
                printf("%d %d\n", i * N + x, PN + j * N + y);
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
        return lib.araujo_lopez_graph(d - 2)
    return None


def _attempt(source, d, D, seed, bud, ref, best):
    """Run one C engine for about bud seconds; return the larger valid graph or best."""
    try:
        text = lib.run_c(source, [d, D, seed, round(float(bud), 3), ref], timeout=bud + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            return (n, edges)
    except Exception:
        pass   # keep the valid fallback
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing to improve

    def remaining():
        return 0.85 * time_limit - (time.monotonic() - t0) - 2.0

    budget = remaining()
    if budget <= 0.5:
        return best
    ref = REF_VERTICES.get((d, D), best[0] + 2)

    # Engine A: proven bi-Cayley search (safety net).
    best = _attempt(C_PARENT, d, D, seed, 0.4 * budget, ref, best)

    # Engine B: multi-orbit voltage lifts, with whatever time is left.
    left = remaining()
    if left > 0.5:
        best = _attempt(C_LIFT, d, D, seed, left, ref, best)
    return best
