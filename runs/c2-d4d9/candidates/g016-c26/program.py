"""Program: two-stage search for d=4 D=9 and similar cases.

Stage 1 (proven family): the bi-Cayley search from the parent program (metacyclic and
matrix groups, 2N vertices), kept as the known-good fallback.

Stage 2 (new construction): multi-orbit voltage lifts. Take k A-orbits and k B-orbits.
A-orbit i has d darts; dart t joins A_i to B_{sig_t(i)} with voltage g_{t,i}, where
sig_t is a permutation of [k]. G = Z_m x| Z_kk acts by left multiplication, which is
an automorphism, so the graph has 2kN vertices. Diameter <= D holds iff BFS from the
identity of each of the 2k orbits reaches every vertex within D steps. C searches over
permutations, voltages and groups, using a simulated-annealing climb on the unreached
count. Orders are chosen so that 2kN is just above the record vertex count.

Safety: every C output goes through lib.is_valid, and the best valid graph so far is
kept. The fallback is K_{d,d}, or the known start when one exists.
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

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 48

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

/* PSL(2,q) or SL(2,q), q prime. */
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

static int climb(double until) {
    randomize_S();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > 4000) {
            randomize_S();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            S[k] = old;
            set_col(k);
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
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
    double usable = limit - 1.5;
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
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXK 6
#define MAXDEG 8
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 800

static int d, D, K, N;
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

/* ------------------------------------------------------------------ group */

static uint16_t *T = NULL;   /* T[x*N+y] = x*y in Z_m x|_r Z_kk */
static int *INV = NULL;

/* Element (a,b) coded as a*kk+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void build_group(int m, int kk, int r) {
    N = m * kk;
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)N * (size_t)N);
    INV = malloc(sizeof(int) * (size_t)N);
    int *pw = malloc(sizeof(int) * (size_t)kk);
    pw[0] = 1 % m;
    for (int b = 1; b < kk; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < N; y++) {
            int c = y / kk, e = y % kk;
            int aa = (int)(((long)a + (long)pw[b] * c) % m);
            int bb = (b + e) % kk;
            T[(size_t)x * N + y] = (uint16_t)(aa * kk + bb);
        }
    }
    free(pw);
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (T[(size_t)x * N + y] == 0) { INV[x] = y; break; }
    }
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int K, m, kk, r, V; } Cand;
static Cand cand[MAXCAND];
static int ncand = 0;

static void gen_cands(long ref, int kmax, long mb) {
    ncand = 0;
    for (int k = 1; k <= kmax; k++) {
        long lo = ref / (2L * k) + 1;      /* smallest N with 2kN > ref */
        long hi = mb / (2L * k);
        if (hi > MAXN) hi = MAXN;
        if (hi > lo + 80) hi = lo + 80;
        for (long Nv = lo; Nv <= hi; Nv++) {
            for (long kk = 1; kk <= Nv / 3 && ncand < MAXCAND; kk++) {
                if (Nv % kk) continue;
                long m = Nv / kk;
                if (m < 3) continue;
                int got = 0;
                for (long r = 1; r < m && got < 2 && ncand < MAXCAND; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, kk, m) != 1 % m) continue;
                    cand[ncand].K = k;
                    cand[ncand].m = (int)m;
                    cand[ncand].kk = (int)kk;
                    cand[ncand].r = (int)r;
                    cand[ncand].V = (int)(2L * k * Nv);
                    ncand++;
                    got++;
                }
            }
        }
    }
    for (int a = 1; a < ncand; a++) {
        Cand c = cand[a];
        int b = a - 1;
        while (b >= 0 && cand[b].V > c.V) { cand[b + 1] = cand[b]; b--; }
        cand[b + 1] = c;
    }
}

/* ------------------------------------------------------------------ voltage state */

/* Dart t from A-orbit i goes to B-orbit sig[t][i] with voltage gv[t][i]. */
static int sig[MAXDEG][MAXK];
static int gv[MAXDEG][MAXK];
static int sinv[MAXDEG][MAXK];   /* sinv[t][j] = i with sig[t][i] == j */
static int ginv[MAXDEG][MAXK];   /* ginv[t][i] = inverse of gv[t][i] */
static int bsig[MAXDEG][MAXK], bgv[MAXDEG][MAXK];
static int bsig_out[MAXDEG][MAXK], bgv_out[MAXDEG][MAXK];

static void derive(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) {
            sinv[t][sig[t][i]] = i;
            ginv[t][i] = INV[gv[t][i]];
        }
}

static void save_state(void) {
    memcpy(bsig, sig, sizeof sig);
    memcpy(bgv, gv, sizeof gv);
}

static void restore_state(void) {
    memcpy(sig, bsig, sizeof sig);
    memcpy(gv, bgv, sizeof gv);
    derive();
}

static void randomize_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) sig[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sig[t][i];
            sig[t][i] = sig[t][j];
            sig[t][j] = tmp;
        }
        for (int i = 0; i < K; i++) gv[t][i] = rndint(N);
    }
    derive();
}

static void mutate(void) {
    int t = rndint(d);
    if (K >= 2 && rnd01() < 0.4) {
        int i1 = rndint(K);
        int i2 = rndint(K - 1);
        if (i2 >= i1) i2++;
        int tmp = sig[t][i1];
        sig[t][i1] = sig[t][i2];
        sig[t][i2] = tmp;
    } else {
        int i = rndint(K);
        gv[t][i] = rndint(N);
    }
    derive();
}

/* Number of duplicate edges: two darts from one A-orbit with the same target and voltage. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++)
            for (int s = t + 1; s < d; s++)
                if (sig[t][i] == sig[s][i] && gv[t][i] == gv[s][i]) c++;
    return c;
}

/* ------------------------------------------------------------------ BFS cost */

/* Vertices: A-orbit i element x has id i*N+x; B-orbit j element y has id (K+j)*N+y. */
static inline int nbr(int v, int t) {
    int o = v / N;
    int x = v - o * N;
    if (o < K) {
        int j = sig[t][o];
        return (K + j) * N + (int)T[(size_t)x * N + gv[t][o]];
    } else {
        int i = sinv[t][o - K];
        return i * N + (int)T[(size_t)x * N + ginv[t][i]];
    }
}

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
            for (int t = 0; t < d; t++) {
                int u = nbr(v, t);
                if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Left multiplication by G is an automorphism, so BFS from one root per orbit suffices. */
static long cost_now(void) {
    long dup = dup_count();
    if (dup) return dup * 1000000L;
    long unreached = 0;
    int Vt = 2 * K * N;
    for (int o = 0; o < 2 * K; o++)
        unreached += (long)(Vt - ball(o * N, D));
    return unreached;
}

static int climb(double until) {
    randomize_state();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > 3000) {
            randomize_state();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        save_state();
        mutate();
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            restore_state();
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit ref kmax\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = atol(argv[5]);
    int kmax = atoi(argv[6]);

    double t0 = now();
    double usable = limit - 0.8;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2 || kmax < 1) { printf("0 0\n"); return 0; }
    if (kmax > MAXK) kmax = MAXK;
    if (ref < 1) ref = 1;

    long mb = moore_bound();
    gen_cands(ref, kmax, mb);

    int bestV = (int)ref;
    int nc = 0;
    for (int c = 0; c < ncand; c++)
        if (cand[c].V > bestV) nc++;
    if (nc == 0) { printf("0 0\n"); return 0; }

    int have = 0;
    Cand bestc;
    memset(&bestc, 0, sizeof bestc);

    double budget = t_end - now();
    double base = budget / (4.0 * (double)nc);
    if (base < 0.02) base = 0.02;

    for (int rd = 0; rd < 12; rd++) {
        int any = 0;
        for (int ci = 0; ci < ncand; ci++) {
            if (cand[ci].V <= bestV) continue;
            double remaining = t_end - now();
            if (remaining < 0.1) break;
            any = 1;
            Cand c = cand[ci];
            build_group(c.m, c.kk, c.r);
            K = c.K;
            if (2L * K * N > mb) continue;
            double slice = base * (double)(1L << rd);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestV = c.V;
                bestc = c;
                memcpy(bsig_out, sig, sizeof sig);
                memcpy(bgv_out, gv, sizeof gv);
            }
        }
        if (!any || t_end - now() < 0.1) break;
    }

    if (!have) { printf("0 0\n"); return 0; }

    build_group(bestc.m, bestc.kk, bestc.r);
    K = bestc.K;
    memcpy(sig, bsig_out, sizeof sig);
    memcpy(gv, bgv_out, sizeof gv);
    derive();
    if (dup_count() != 0 || cost_now() != 0) { printf("0 0\n"); return 0; }

    long V = 2L * K * N;
    long E = (long)K * N * d;
    printf("%ld %ld\n", V, E);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++) {
                int u = i * N + x;
                int v = (K + sig[t][i]) * N + (int)T[(size_t)x * N + gv[t][i]];
                printf("%d %d\n", u, v);
            }
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}
LIFT_KMAX = 4


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _keep(best, out, d, D):
    """Return out if it is a valid graph larger than best, otherwise best."""
    if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
        return out
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best

    ref = REF_VERTICES.get((d, D), best[0])

    def left():
        return 0.92 * time_limit - (time.monotonic() - t0) - 1.0

    # Stage 1: proven bi-Cayley family (parent engine), keeps the known record route.
    b1 = 0.4 * left()
    if b1 > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, b1, ref], timeout=b1 + 2)
            best = _keep(best, lib.parse_graph_text(text), d, D)
        except Exception:
            pass   # keep the valid fallback

    # Stage 2: multi-orbit voltage lifts over metacyclic groups (new construction).
    b2 = left() - 0.5
    if b2 > 0.5:
        try:
            text = lib.run_c(C_LIFT, [d, D, seed, b2, ref, LIFT_KMAX], timeout=b2 + 2)
            best = _keep(best, lib.parse_graph_text(text), d, D)
        except Exception:
            pass   # keep the valid fallback

    return best
