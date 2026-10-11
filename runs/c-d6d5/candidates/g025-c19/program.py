import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (voltage) lifts over a much wider family of finite groups.
#
# A base graph has K A-vertices and K B-vertices. Each of the DEG layers is a
# bijection between the A and B blocks, and each dart carries a voltage s in G.
# Dart (i, j, s) joins A_{i,g} to B_{j,g*s} for every g in G. Left
# multiplication is an automorphism, so diameter <= D iff a BFS of depth D from
# each of the 2K block representatives covers the whole graph.
#
# Groups are built inside C from several families:
#   fam 0: cyclic Z_m
#   fam 1: semidirect Z_m x| Z_k with r^k = 1 mod m (r = 1 gives a direct product)
#   fam 2: unitriangular 3x3 matrices over Z_p (Heisenberg group, order p^3)
#   fam 3: (semidirect Z_m x| Z_k) x Z_dz
#   fam 4: Z_p^2 x| Z_k, Z_k acting by a companion matrix A with A^k = I
# Each group is stored as a full multiplication table.
#
# Search: simulated annealing on a weighted cost (breakout weights), with an
# elite pool for iterated local search. The target is always "beat the best
# order found so far", and the group window is set around that target.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 5000
#define ILS_ITERS 2500
#define POOLMAX 40
#define POOLP 0.55
#define BRK 150
#define MAXG 1600
#define MAXK 6
#define NKC 6

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM;
static int K, G, T;
static int *tb = NULL;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static long long *wt, *unc;
static long long wsum_w, last_w;
static int curstamp;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static int gfam, ga, gb, gc, gd;

typedef struct {
    int fam, a, b, c, d, K, G;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;
static const int kc[NKC] = {1, 1, 2, 2, 3, 4};

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, long long e, long long m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int is_prime_i(int n) {
    if (n < 2) return 0;
    for (int p = 2; p * p <= n; p++) if (n % p == 0) return 0;
    return 1;
}

static void m2mul(const int *X, const int *Y, int p, int *Z) {
    int z0 = (X[0] * Y[0] + X[1] * Y[2]) % p;
    int z1 = (X[0] * Y[1] + X[1] * Y[3]) % p;
    int z2 = (X[2] * Y[0] + X[3] * Y[2]) % p;
    int z3 = (X[2] * Y[1] + X[3] * Y[3]) % p;
    Z[0] = z0; Z[1] = z1; Z[2] = z2; Z[3] = z3;
}

/* A = [[0,t],[1,s]], companion matrix of x^2 - s x - t over Z_p. Test A^k = I. */
static int check_companion(int p, int k, int t, int s) {
    int A[4] = {0, t, 1, s};
    int M[4] = {1, 0, 0, 1};
    for (int i = 0; i < k; i++) {
        int Z[4];
        m2mul(A, M, p, Z);
        memcpy(M, Z, sizeof Z);
    }
    return M[0] == 1 % p && M[1] == 0 && M[2] == 0 && M[3] == 1 % p;
}

/* Semidirect Z_m x| Z_k (times Z_dz); element index ((a*k+b)*dz + z), (a,b)(c,e) = (a + r^b c, b+e). */
static void fill_semi(int m, int k, int r, int dz) {
    int *Rp = malloc(sizeof(int) * (size_t)k);
    Rp[0] = 1 % m;
    for (int b = 1; b < k; b++) Rp[b] = (int)((long long)Rp[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int sx = x / dz, zx = x % dz;
        int ax = sx / k, bx = sx % k;
        for (int y = 0; y < G; y++) {
            int sy = y / dz, zy = y % dz;
            int cy = sy / k, ey = sy % k;
            int ra = (int)(((long long)ax + (long long)Rp[bx] * cy) % m);
            int rb = (bx + ey) % k;
            tb[x * G + y] = (ra * k + rb) * dz + (zx + zy) % dz;
        }
    }
    free(Rp);
}

/* Unitriangular 3x3 over Z_p: (u,v,w)(u',v',w') = (u+u', v+v', w+w'+u v'). */
static void fill_ut3(int p) {
    for (int x = 0; x < G; x++) {
        int u1 = x / (p * p), v1 = (x / p) % p, w1 = x % p;
        for (int y = 0; y < G; y++) {
            int u2 = y / (p * p), v2 = (y / p) % p, w2 = y % p;
            int u = (u1 + u2) % p, v = (v1 + v2) % p;
            int w = (w1 + w2 + u1 * v2) % p;
            tb[x * G + y] = (u * p + v) * p + w;
        }
    }
}

/* Z_p^2 x| Z_k with A = companion matrix; element ((v0*p+v1)*k + b), (v,b)(w,c) = (v + A^b w, b+c). */
static void fill_comp(int p, int k, int t, int s) {
    int *P = malloc(sizeof(int) * 4 * (size_t)k);
    int A[4] = {0, t, 1, s};
    int I4[4] = {1, 0, 0, 1};
    memcpy(P, I4, sizeof I4);
    for (int i = 1; i < k; i++) m2mul(A, P + 4 * (i - 1), p, P + 4 * i);
    for (int x = 0; x < G; x++) {
        int v0x = (x / k) / p, v1x = (x / k) % p, bx = x % k;
        const int *Pm = P + 4 * bx;
        for (int y = 0; y < G; y++) {
            int v0y = (y / k) / p, v1y = (y / k) % p, by = y % k;
            int r0 = (v0x + Pm[0] * v0y + Pm[1] * v1y) % p;
            int r1 = (v1x + Pm[2] * v0y + Pm[3] * v1y) % p;
            int rb = (bx + by) % k;
            tb[x * G + y] = (r0 * p + r1) * k + rb;
        }
    }
    free(P);
}

/* Install a group from family parameters. Returns 1 on success and sets G, tb and the group params. */
static int build_group(int fam, int a, int b, int c, int d) {
    long long nn = 0;
    int mm = 1, kk = 1, rr = 0, dz = 1, p = 0, t = 0, s = 0;
    if (fam == 0) {
        if (a < 1) return 0;
        nn = a; mm = a; kk = 1; rr = 1 % a; dz = 1;
    } else if (fam == 1 || fam == 3) {
        mm = a; kk = b; dz = (fam == 3) ? d : 1;
        if (mm < 1 || kk < 1 || dz < 1) return 0;
        nn = (long long)mm * kk * dz;
        rr = c % mm;
        if (gcd_i(rr, mm) != 1 || powmod(rr, kk, mm) != 1 % mm) return 0;
    } else if (fam == 2) {
        p = a;
        if (p < 2 || !is_prime_i(p)) return 0;
        nn = (long long)p * p * p;
    } else if (fam == 4) {
        p = a; kk = b;
        if (p < 2 || !is_prime_i(p) || kk < 1) return 0;
        nn = (long long)p * p * kk;
    } else {
        return 0;
    }
    if (nn < 1 || nn > MAXG) return 0;
    if (fam == 4) {
        t = ((c % p) + p) % p;
        s = ((d % p) + p) % p;
        if (!check_companion(p, kk, t, s)) return 0;
    }
    G = (int)nn;
    if (tb) { free(tb); tb = NULL; }
    tb = malloc(sizeof(int) * (size_t)G * G);
    if (!tb) { G = 0; return 0; }
    if (fam == 2) fill_ut3(p);
    else if (fam == 4) fill_comp(p, kk, t, s);
    else fill_semi(mm, kk, rr, dz);
    gfam = fam; ga = a; gb = b; gc = c; gd = d;
    return 1;
}

static int divisors_of(int n, int *out) {
    int c = 0;
    for (int q = 1; q <= n; q++) if (n % q == 0) out[c++] = q;
    return c;
}

/* Find (m, k, r) with m*k = n, k, m >= 2, r^k = 1 mod m, gcd(r, m) = 1. r = 1 is tried first. */
static int find_semi(int n, int *pm, int *pk, int *pr) {
    int dv[MAXG + 1];
    int nd = divisors_of(n, dv);
    for (int tr = 0; tr < 40; tr++) {
        int k = dv[rnd_int(nd)];
        int m = n / k;
        if (k < 2 || m < 2) continue;
        for (int q = 0; q < 60; q++) {
            int r = (q == 0) ? 1 : 1 + rnd_int(m - 1);
            if (gcd_i(r, m) == 1 && powmod(r, k, m) == 1 % m) {
                *pm = m; *pk = k; *pr = r;
                return 1;
            }
        }
    }
    return 0;
}

/* Random family and parameters with group order exactly n. */
static int pick_family(int n, int *fam, int *a, int *b, int *c, int *d) {
    int r = rnd_int(12);
    int m, k, rr;
    if (r <= 1) {
        *fam = 0; *a = n; *b = 0; *c = 0; *d = 0;
        return 1;
    }
    if (r <= 5) {
        if (!find_semi(n, &m, &k, &rr)) return 0;
        *fam = 1; *a = m; *b = k; *c = rr; *d = 0;
        return 1;
    }
    if (r <= 7) {
        int dv[MAXG + 1];
        int nd = divisors_of(n, dv);
        int dz = dv[rnd_int(nd)];
        if (dz < 2 || n / dz < 4) return 0;
        if (!find_semi(n / dz, &m, &k, &rr)) return 0;
        *fam = 3; *a = m; *b = k; *c = rr; *d = dz;
        return 1;
    }
    if (r == 8) {
        int p = 0;
        for (int q = 2; q * q * q <= n; q++) if (q * q * q == n) p = q;
        if (p < 2 || !is_prime_i(p)) return 0;
        *fam = 2; *a = p; *b = 0; *c = 0; *d = 0;
        return 1;
    }
    {
        int cands[64], nc = 0;
        for (int p = 2; p * p <= n; p++)
            if (n % (p * p) == 0 && is_prime_i(p) && n / (p * p) >= 2 && nc < 64)
                cands[nc++] = p;
        if (nc == 0) return 0;
        int p = cands[rnd_int(nc)];
        int k = n / (p * p);
        for (int q = 0; q < 40; q++) {
            int t = 1 + rnd_int(p - 1), s = rnd_int(p);
            if (check_companion(p, k, t, s)) {
                *fam = 4; *a = p; *b = k; *c = t; *d = s;
                return 1;
            }
        }
        return 0;
    }
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = tb[g * G + s];
}

/* Sum over block representatives of uncovered vertices; sets unc[r] and last_w (weighted). */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = N - count;
        total += N - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void alloc_run(void) {
    int N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    for (int r = 0; r < 2 * K; r++) wt[r] = 1;
    wsum_w = 2 * K;
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void free_run(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = NULL;
    wt = unc = NULL;
}

static void random_init(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    best_m = m;
    best_n = 2 * K * G;
}

static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * G > best_n) emit();
    }
}

static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Cfg *c = &pool[slot];
    c->fam = gfam; c->a = ga; c->b = gb; c->c = gc; c->d = gd;
    c->K = K; c->G = G; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].G;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)DEG * MAXK);
        pool[i].S = malloc(sizeof(int) * (size_t)DEG * MAXK);
        pool[i].cost = BIGC;
        pool[i].K = 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            Cfg *c = &pool[pi];
            if (!build_group(c->fam, c->a, c->b, c->c, c->d)) continue;
            K = c->K;
            alloc_run();
            memcpy(dJ, c->J, sizeof(int) * (size_t)T);
            memcpy(dS, c->S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_run();
            continue;
        }

        int k = kc[rnd_int(NKC)];
        int tgt = best_n + 2;
        int gneed = (tgt + 2 * k - 1) / (2 * k);
        if (gneed < 2) gneed = 2;
        int gg = gneed + rnd_int(gneed / 6 + 2);
        if (gg > MAXG) gg = MAXG;
        int fam = 0, a = 0, b = 0, c = 0, d = 0, ok = 0;
        for (int tr = 0; tr < 40 && !ok; tr++)
            if (pick_family(gg, &fam, &a, &b, &c, &d))
                ok = build_group(fam, a, b, c, d);
        if (!ok) ok = build_group(0, gg, 1, 1, 0);
        if (!ok) break;

        K = k;
        alloc_run();
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
        free_run();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (Python).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C group-lift search with the remaining time.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget; its wall-clock deadline keeps it on time.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
