"""Program: bi-Cayley search over several group families, with simulated annealing
inside iterative-deepening rounds.

Core construction (unchanged):
  * Group G of order N, given by a full multiplication table. Bi-Cayley graph: A_x is
    joined to B_{x*s_k} for k < d. The graph is d-regular, bipartite, with 2N vertices.
  * Left multiplication is an automorphism, so diameter <= D holds iff BFS from A_e and
    from B_e both reach all 2N vertices within D steps.

What changed (bold, higher-risk): the parent only searched metacyclic groups Z_m x| Z_k
and PSL/SL(2,q). This version adds two NON-metacyclic families to the candidate pool:
  * Affine groups Z_m^2 x| Z_k, where the generator acts on Z_m^2 by an invertible 2x2
    matrix A over Z_m of exact order k. Group order m^2 * k.
  * Heisenberg groups H(Z_m) of order m^3.
Candidates are scheduled ascending above the record (new families interleaved with
metacyclic ones) and a small set just below the record is kept as the fallback. The
fallback order mirrors the parent, which reaches the record-level order first.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
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

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define POOL 20000
#define ALL_MAX 192
#define LO_CAP 24
#define HI_META_CAP 30
#define HI_AFF_CAP 30
#define HI_HEIS_CAP 4
#define MATRIX_CAP 16

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

/* ------------------------------------------------------------------ group tables */

static int N = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
    if (!T || !INV) exit(1);   /* Python sees an error and keeps its fallback */
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
    long n = (long)m * k;
    if (n > MAXN || n < 2) return 0;
    N = (int)n;
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

/* Z_m^2 x|_A Z_k: element (v, j) with v in Z_m^2, j in Z_k, coded as (v0*m+v1)*k+j.
   (v, j)(w, l) = (v + A^j w, j + l). Needs A^k = I mod m (A of exact order k). */
static int build_affine(int m, int k, const int A[4]) {
    long n = (long)m * m * k;
    if (n > MAXN || n < 2 || k < 1) return 0;
    static int Pw[MAXN][4];
    int one = 1 % m;
    Pw[0][0] = one; Pw[0][1] = 0; Pw[0][2] = 0; Pw[0][3] = one;
    for (int j = 1; j < k; j++) {
        int p0 = Pw[j - 1][0], p1 = Pw[j - 1][1], p2 = Pw[j - 1][2], p3 = Pw[j - 1][3];
        Pw[j][0] = (p0 * A[0] + p1 * A[2]) % m;
        Pw[j][1] = (p0 * A[1] + p1 * A[3]) % m;
        Pw[j][2] = (p2 * A[0] + p3 * A[2]) % m;
        Pw[j][3] = (p2 * A[1] + p3 * A[3]) % m;
    }
    /* Check A^k = I. */
    {
        int p0 = Pw[k - 1][0], p1 = Pw[k - 1][1], p2 = Pw[k - 1][2], p3 = Pw[k - 1][3];
        int q0 = (p0 * A[0] + p1 * A[2]) % m;
        int q1 = (p0 * A[1] + p1 * A[3]) % m;
        int q2 = (p2 * A[0] + p3 * A[2]) % m;
        int q3 = (p2 * A[1] + p3 * A[3]) % m;
        if (q0 != one || q1 != 0 || q2 != 0 || q3 != one) return 0;
    }
    N = (int)n;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int j = x % k, r = x / k;
        int v0 = r / m, v1 = r % m;
        for (int y = 0; y < N; y++) {
            int l = y % k, s = y / k;
            int w0 = s / m, w1 = s % m;
            int a0 = (Pw[j][0] * w0 + Pw[j][1] * w1) % m;
            int a1 = (Pw[j][2] * w0 + Pw[j][3] * w1) % m;
            int nv0 = (v0 + a0) % m, nv1 = (v1 + a1) % m;
            int nj = (j + l) % k;
            T[(size_t)x * N + y] = (uint16_t)((nv0 * m + nv1) * k + nj);
        }
    }
    e_id = 0;
    finish_inv();
    return N;
}

/* Heisenberg group mod m: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'). Order m^3. */
static int build_heis(int m) {
    long n = (long)m * m * m;
    if (n > MAXN || n < 2) return 0;
    N = (int)n;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = x / (m * m), b = (x / m) % m, c = x % m;
        for (int y = 0; y < N; y++) {
            int a2 = y / (m * m), b2 = (y / m) % m, c2 = y % m;
            int na = (a + a2) % m;
            int nb = (b + b2) % m;
            int nc = (c + c2 + a * b2) % m;
            T[(size_t)x * N + y] = (uint16_t)((na * m + nb) * m + nc);
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
    int type;   /* 0 metacyclic, 1 matrix SL/PSL(2,q), 2 affine Z_m^2 x| Z_k, 3 Heisenberg */
    int q, psl, m, k, r, N;
    int A[4];
} Cand;

static Cand pool[POOL];
static int npool = 0;

static void pool_add(const Cand *c) {
    if (npool < POOL) pool[npool++] = *c;
}

static int apply_cand(const Cand *c) {
    switch (c->type) {
        case 0: return build_meta(c->m, c->k, c->r);
        case 1: return build_matrix(c->q, c->psl);
        case 2: return build_affine(c->m, c->k, c->A);
        default: return build_heis(c->m);
    }
}

static void add_meta(int Nval) {
    for (int k = 2; k <= Nval / 3; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            pool_add(&c);
            got++;
        }
    }
}

/* Affine groups Z_m^2 x| Z_k with A of exact order k in GL(2, Z_m). At most 2 per (m,k). */
static void add_affine(int lowN, int hiN) {
    static int cntmk[41][801];
    for (int m = 2; m <= 40 && (long)m * m * 2 <= hiN; m++) {
        long L = hiN / ((long)m * m);
        if (L > 800) L = 800;
        int one = 1 % m;
        for (int a0 = 0; a0 < m; a0++)
        for (int a1 = 0; a1 < m; a1++)
        for (int a2 = 0; a2 < m; a2++)
        for (int a3 = 0; a3 < m; a3++) {
            int ord = 0;
            int p0 = one, p1 = 0, p2 = 0, p3 = one;
            for (int j = 1; j <= L; j++) {
                int t0 = (p0 * a0 + p1 * a2) % m;
                int t1 = (p0 * a1 + p1 * a3) % m;
                int t2 = (p2 * a0 + p3 * a2) % m;
                int t3 = (p2 * a1 + p3 * a3) % m;
                p0 = t0; p1 = t1; p2 = t2; p3 = t3;
                if (p0 == one && p1 == 0 && p2 == 0 && p3 == one) { ord = j; break; }
            }
            if (ord < 2) continue;
            long nn = (long)m * m * ord;
            if (nn < lowN || nn > hiN) continue;
            if (cntmk[m][ord] >= 2) continue;
            cntmk[m][ord]++;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 2;
            c.m = m;
            c.k = ord;
            c.N = (int)nn;
            c.A[0] = a0; c.A[1] = a1; c.A[2] = a2; c.A[3] = a3;
            pool_add(&c);
        }
    }
}

static void add_heis(int lowN, int hiN) {
    for (int m = 3; m <= 14; m++) {
        long n = (long)m * m * m;
        if (n < lowN || n > hiN) continue;
        Cand c;
        memset(&c, 0, sizeof c);
        c.type = 3;
        c.m = m;
        c.N = (int)n;
        pool_add(&c);
    }
}

static void add_matrix(int lowN, int hiN) {
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            pool_add(&c);
        }
    }
}

static int cmp_asc(const void *a, const void *b) {
    int x = ((const Cand *)a)->N, y = ((const Cand *)b)->N;
    return (x > y) - (x < y);
}

static void build_pool(int lowN, int hiN, int recN) {
    npool = 0;
    add_matrix(lowN, hiN);
    for (int Nv = recN - 8; Nv < recN; Nv++)
        if (Nv >= lowN) add_meta(Nv);
    for (int Nv = recN; Nv <= hiN; Nv++) add_meta(Nv);
    add_affine(lowN, hiN);
    add_heis(lowN, hiN);
    qsort(pool, (size_t)npool, sizeof(Cand), cmp_asc);
}

/* Matrix groups first, then fallback candidates just below the record (descending),
   then candidates above the record (ascending, new families mixed with metacyclic). */
static int select_all(int lowN, int hiN, int recN, Cand *all) {
    int na = 0, nm = 0;
    for (int i = 0; i < npool && nm < MATRIX_CAP && na < ALL_MAX; i++)
        if (pool[i].type == 1) { all[na++] = pool[i]; nm++; }

    int nl = 0;
    for (int i = npool - 1; i >= 0 && nl < LO_CAP && na < ALL_MAX; i--) {
        Cand *c = &pool[i];
        if (c->type == 1 || c->N >= recN || c->N < lowN) continue;
        all[na++] = *c;
        nl++;
    }

    int nmeta = 0, naff = 0, nheis = 0;
    for (int i = 0; i < npool && na < ALL_MAX; i++) {
        Cand *c = &pool[i];
        if (c->type == 1 || c->N < recN || c->N > hiN) continue;
        if (c->type == 0 && nmeta < HI_META_CAP) nmeta++;
        else if (c->type == 2 && naff < HI_AFF_CAP) naff++;
        else if (c->type == 3 && nheis < HI_HEIS_CAP) nheis++;
        else continue;
        all[na++] = *c;
    }
    return na;
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
    int recN = recHalf + 1;   /* smallest N that beats the record vertex count */

    build_pool(lowN, hiN, recN);
    static Cand all[ALL_MAX];
    int na = select_all(lowN, hiN, recN, all);

    double budget0 = t_end - now();
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    /* Iterative deepening: each round gives every still-improving candidate a slice,
       and the slice doubles per round. */
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
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
