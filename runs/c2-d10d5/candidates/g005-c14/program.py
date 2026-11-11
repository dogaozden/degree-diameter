import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley simulated annealing over Z_m x| Z_k2 (unchanged search).
# It builds a large algebraic-style start graph from scratch.
# ----------------------------------------------------------------------------

C_BICAYLEY = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PENALTY 1000L
#define KMAX 8
#define ELITE_ROUNDS 3
#define ELITE_ITERS 1500
#define ELITE_PATIENCE 600
#define ELITE_THR 30

static clock_t g_t0;
static double g_budget = 1.0;
static uint64_t g_rs = 88172645463325252ULL;

/* group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) */
static int GM = 1, GK = 1, GG = 1;
static int64_t PW[64];

static long g_best_n = 0;
static long g_best_m = 0;
static int *g_edges = NULL;

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    uint64_t x = g_rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    g_rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = (a + PW[b] * (int64_t)c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int64_t t = (-(PW[nb] * (int64_t)a)) % GM;
    if (t < 0) t += GM;
    return (int)(t * GK + nb);
}

static void set_group(int m, int k2, int64_t r) {
    GM = m;
    GK = k2;
    GG = m * k2;
    int64_t p = 1 % m;
    for (int t = 0; t < k2; t++) {
        PW[t] = p;
        p = (p * r) % m;
    }
}

static const int KCH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int sample_group(long target, int *mo, int *ko, int64_t *ro) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = KCH[rnd(20)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndf() < 0.3) {
            r = m - 1;
            if (gcd64(r, m) != 1 || powmod(r, 2, m) != 1 % m) continue;
        } else {
            int found = 0;
            for (int t = 0; t < 60; t++) {
                int64_t c = (m > 2) ? 2 + (int64_t)rnd((uint64_t)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        *mo = (int)m;
        *ko = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

static int popc(uint32_t x) {
    int c = 0;
    while (x) {
        c += (int)(x & 1u);
        x >>= 1;
    }
    return c;
}

/* A-block i (vertices i*GG..) joins B-block j = lay[l][i] with voltage s = S[l][i]. */
static void set_dart(int **nbr, const int *lay, const int *S, int k, int l, int i) {
    int j = lay[l * k + i];
    int s = S[l * k + i];
    int si = ginv(s);
    int Ab = i * GG, Bb = (k + j) * GG;
    int *nb = nbr[l];
    for (int g = 0; g < GG; g++) {
        nb[Ab + g] = Bb + gmul(g, s);
        nb[Bb + g] = Ab + gmul(g, si);
    }
}

/* out[v] = bitmask of representative blocks within distance D of v. */
static void compute_reach(int **nbr, int d, int k, int N, int D, uint32_t *out, uint32_t *tmp) {
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) out[b * GG] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = out[v];
            for (int l = 0; l < d; l++) r |= out[nbr[l][v]];
            tmp[v] = r;
            if (r != out[v]) changed = 1;
        }
        memcpy(out, tmp, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
}

static long unreached(const uint32_t *reach, int k, int N) {
    long s = 0;
    for (int v = 0; v < N; v++) s += popc(reach[v]);
    return 2L * k * N - s;
}

static long dupcount(const int *lay, const int *S, int d, int k) {
    int tot = d * k;
    long dup = 0;
    for (int a = 0; a < tot; a++) {
        int la = a / k, ia = a % k;
        for (int b = 0; b < a; b++) {
            int lb = b / k, ib = b % k;
            if (ia == ib && lay[la * k + ia] == lay[lb * k + ib] && S[la * k + ia] == S[lb * k + ib]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static void store_best(int **nbr, int d, int k) {
    long A = (long)k * GG;
    long n = 2 * A;
    if (n <= g_best_n) return;
    long cnt = A * d;
    int *e = malloc(sizeof(int) * 2 * (size_t)cnt);
    if (!e) return;
    long c = 0;
    for (long u = 0; u < A; u++) {
        for (int l = 0; l < d; l++) {
            e[2 * c] = (int)u;
            e[2 * c + 1] = nbr[l][u];
            c++;
        }
    }
    free(g_edges);
    g_edges = e;
    g_best_m = cnt;
    g_best_n = n;
}

static int run_trial(int d, int D, int k, int iters, int patience,
                     const int *init_lay, const int *init_S, int perturb,
                     int *out_lay, int *out_S, long *out_cost) {
    int N = 2 * k * GG;
    uint32_t full = (1u << (2 * k)) - 1u;
    int K = d * k;
    int *lay = malloc(sizeof(int) * (size_t)K);
    int *S = malloc(sizeof(int) * (size_t)K);
    int *blay = malloc(sizeof(int) * (size_t)K);
    int *bS = malloc(sizeof(int) * (size_t)K);
    int **nbr = malloc(sizeof(int *) * (size_t)d);
    uint32_t *rc = malloc(sizeof(uint32_t) * (size_t)N);
    uint32_t *rn = malloc(sizeof(uint32_t) * (size_t)N);
    uint32_t *tmp = malloc(sizeof(uint32_t) * (size_t)N);
    for (int l = 0; l < d; l++) nbr[l] = malloc(sizeof(int) * (size_t)N);

    if (init_lay && init_S) {
        memcpy(lay, init_lay, sizeof(int) * (size_t)K);
        memcpy(S, init_S, sizeof(int) * (size_t)K);
        for (int p = 0; p < perturb; p++) {
            if (k >= 2 && rndf() < 0.3) {
                int l = (int)rnd((uint64_t)d);
                int i1 = (int)rnd((uint64_t)k);
                int i2 = (int)rnd((uint64_t)(k - 1));
                if (i2 >= i1) i2++;
                int tv = lay[l * k + i1];
                lay[l * k + i1] = lay[l * k + i2];
                lay[l * k + i2] = tv;
            } else {
                S[rnd((uint64_t)K)] = (int)rnd((uint64_t)GG);
            }
        }
    } else {
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < k; i++) lay[l * k + i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = (int)rnd((uint64_t)(i + 1));
                int t = lay[l * k + i];
                lay[l * k + i] = lay[l * k + j];
                lay[l * k + j] = t;
            }
        }
        for (int q = 0; q < K; q++) S[q] = (int)rnd((uint64_t)GG);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(nbr, lay, S, k, l, i);

    compute_reach(nbr, d, k, N, D, rc, tmp);
    long cost = unreached(rc, k, N) + PENALTY * dupcount(lay, S, d, k);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    memcpy(blay, lay, sizeof(int) * (size_t)K);
    memcpy(bS, S, sizeof(int) * (size_t)K);
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (elapsed() > g_budget) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rndf() < 0.25) {
            int l = (int)rnd((uint64_t)d);
            int i1 = (int)rnd((uint64_t)k);
            int i2 = (int)rnd((uint64_t)(k - 1));
            if (i2 >= i1) i2++;
            int tv = lay[l * k + i1];
            lay[l * k + i1] = lay[l * k + i2];
            lay[l * k + i2] = tv;
            set_dart(nbr, lay, S, k, l, i1);
            set_dart(nbr, lay, S, k, l, i2);
            compute_reach(nbr, d, k, N, D, rn, tmp);
            long c2 = unreached(rn, k, N) + PENALTY * dupcount(lay, S, d, k);
            if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *p = rc;
                rc = rn;
                rn = p;
                if (cost < best_cost) {
                    best_cost = cost;
                    last = t;
                    memcpy(blay, lay, sizeof(int) * (size_t)K);
                    memcpy(bS, S, sizeof(int) * (size_t)K);
                }
            } else {
                tv = lay[l * k + i1];
                lay[l * k + i1] = lay[l * k + i2];
                lay[l * k + i2] = tv;
                set_dart(nbr, lay, S, k, l, i1);
                set_dart(nbr, lay, S, k, l, i2);
            }
            continue;
        }

        int l = 0, i = 0;
        int picked = 0;
        if (rndf() < 0.4) {
            long nbad = 0;
            for (int v = 0; v < N; v++)
                if (rc[v] != full) nbad++;
            if (nbad > 0) {
                long pick = (long)rnd((uint64_t)nbad);
                int u = -1;
                for (int v = 0; v < N; v++) {
                    if (rc[v] != full) {
                        if (pick == 0) {
                            u = v;
                            break;
                        }
                        pick--;
                    }
                }
                int block = u / GG;
                l = (int)rnd((uint64_t)d);
                if (block < k) {
                    i = block;
                } else {
                    i = -1;
                    for (int q = 0; q < k; q++) {
                        if (lay[l * k + q] == block - k) {
                            i = q;
                            break;
                        }
                    }
                    if (i < 0) i = 0;
                }
                picked = 1;
            }
        }
        if (!picked) {
            l = (int)rnd((uint64_t)d);
            i = (int)rnd((uint64_t)k);
        }

        int old = S[l * k + i];
        int nw = (int)rnd((uint64_t)GG);
        if (nw == old) continue;
        S[l * k + i] = nw;
        set_dart(nbr, lay, S, k, l, i);
        compute_reach(nbr, d, k, N, D, rn, tmp);
        long c2 = unreached(rn, k, N) + PENALTY * dupcount(lay, S, d, k);
        if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint32_t *p = rc;
            rc = rn;
            rn = p;
            if (cost < best_cost) {
                best_cost = cost;
                last = t;
                memcpy(blay, lay, sizeof(int) * (size_t)K);
                memcpy(bS, S, sizeof(int) * (size_t)K);
            }
        } else {
            S[l * k + i] = old;
            set_dart(nbr, lay, S, k, l, i);
        }
    }

    int ok = (cost == 0);
    if (ok) store_best(nbr, d, k);
    memcpy(out_lay, blay, sizeof(int) * (size_t)K);
    memcpy(out_S, bS, sizeof(int) * (size_t)K);
    *out_cost = best_cost;

    for (int l = 0; l < d; l++) free(nbr[l]);
    free(nbr);
    free(lay);
    free(S);
    free(blay);
    free(bS);
    free(rc);
    free(rn);
    free(tmp);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget min_n\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    g_rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (g_rs == 0) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    g_best_n = atol(argv[5]);
    g_t0 = clock();

    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    long trials[KMAX + 1], wins[KMAX + 1];
    for (int kk = 0; kk <= KMAX; kk++) {
        trials[kk] = 0;
        wins[kk] = 0;
    }

    int cap = d * KMAX;
    int *blay = malloc(sizeof(int) * (size_t)cap);
    int *bS = malloc(sizeof(int) * (size_t)cap);
    int *tlay = malloc(sizeof(int) * (size_t)cap);
    int *tS = malloc(sizeof(int) * (size_t)cap);

    while (elapsed() < g_budget) {
        int k;
        if (rndf() < 0.2) {
            k = 1 + (int)rnd(KMAX);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= KMAX; kk++) {
                double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.02 * rndf();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        long base = g_best_n / (2L * k);
        long span = base / 8 + 1;
        if (span < 2) span = 2;
        long target = base + 1 + (long)rnd((uint64_t)span);
        if (target < 2) target = 2;

        int m = 0, k2 = 1;
        int64_t r = 1;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        if (2L * k * GG <= g_best_n) continue;

        trials[k]++;
        long bc = 0;
        if (run_trial(d, D, k, 4000, 1200, NULL, NULL, 0, blay, bS, &bc)) {
            wins[k]++;
            continue;
        }

        int K = d * k;
        for (int rr = 0; rr < ELITE_ROUNDS && bc <= ELITE_THR && elapsed() < g_budget; rr++) {
            long bc2 = 0;
            int pert = 1 + (int)rnd(3);
            if (run_trial(d, D, k, ELITE_ITERS, ELITE_PATIENCE, blay, bS, pert, tlay, tS, &bc2)) {
                wins[k]++;
                break;
            }
            if (bc2 <= bc) {
                bc = bc2;
                memcpy(blay, tlay, sizeof(int) * (size_t)K);
                memcpy(bS, tS, sizeof(int) * (size_t)K);
            }
        }
    }

    free(blay);
    free(bS);
    free(tlay);
    free(tS);

    if (g_best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", g_best_n, g_best_m);
    for (long c = 0; c < g_best_m; c++) {
        printf("%d %d\n", g_edges[2 * c], g_edges[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (new): graph-level local search with vertex growth.
#
# Works on a general bipartite graph (no group structure). Objective: number of
# unordered vertex pairs at distance > D. Moves are degree-safe edge switches,
# endpoint moves, edge additions and deletions, accepted by simulated annealing.
# When a state reaches zero bad pairs it is saved; then one new vertex is grown
# (joined to d opposite-side vertices, displacing edges where they are full)
# and annealed again from the saved best state.
# Input: start graph on stdin ("n m" + edges). Output: best valid graph.
# ----------------------------------------------------------------------------

C_LS = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 8192
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 64

static int DEG = 1, DIAM = 1;
static int N = 0;
static int *col = NULL, *deg = NULL, *nb = NULL;
static uint64_t *RA = NULL, *RB = NULL;
static long cur = 0;
static double budget = 1.0;
static clock_t t0;
static uint64_t rs = 88172645463325252ULL;

static int bestN = 0;
static long bestM = 0;
static int *bestE = NULL;
static int bestCol[MAXN];

typedef struct { int t, a, b; } Op;
static Op ops[8];
static int nops = 0;

static double elapsed(void) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int adjacent(int a, int b) {
    const int *p = nb + (size_t)a * DEG;
    for (int i = 0; i < deg[a]; i++)
        if (p[i] == b) return 1;
    return 0;
}

static void del_one(int a, int b) {
    int *p = nb + (size_t)a * DEG;
    for (int i = 0; i < deg[a]; i++) {
        if (p[i] == b) {
            p[i] = p[deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_e(int a, int b) {
    nb[(size_t)a * DEG + deg[a]++] = b;
    nb[(size_t)b * DEG + deg[b]++] = a;
}

static void del_e(int a, int b) {
    del_one(a, b);
    del_one(b, a);
}

static void apply_add(int a, int b) {
    add_e(a, b);
    ops[nops].t = 0; ops[nops].a = a; ops[nops].b = b;
    nops++;
}

static void apply_del(int a, int b) {
    del_e(a, b);
    ops[nops].t = 1; ops[nops].a = a; ops[nops].b = b;
    nops++;
}

static void undo_all(void) {
    while (nops > 0) {
        nops--;
        if (ops[nops].t == 0) del_e(ops[nops].a, ops[nops].b);
        else add_e(ops[nops].a, ops[nops].b);
    }
}

/* Number of unordered pairs at distance > DIAM. */
static long bad_count(void) {
    int W = (N + 63) / 64;
    uint64_t *A = RA, *B = RB;
    memset(A, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) A[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *r = B + (size_t)v * W;
            const uint64_t *s = A + (size_t)v * W;
            memcpy(r, s, sizeof(uint64_t) * (size_t)W);
            const int *p = nb + (size_t)v * DEG;
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *q = A + (size_t)p[i] * W;
                for (int w = 0; w < W; w++) r[w] |= q[w];
            }
        }
        uint64_t *tmp = A;
        A = B;
        B = tmp;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        long pc = 0;
        const uint64_t *s = A + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += pop64(s[w]);
        tot += (long)N - pc;
    }
    return tot / 2;
}

static int ok_mode(int v, int side, int mode) {
    if (col[v] != side) return 0;
    if (mode == 1) return deg[v] < DEG;
    if (mode == 2) return deg[v] > 0;
    return 1;
}

/* mode 0: any vertex of side; 1: deg < DEG; 2: deg > 0. Returns -1 if none. */
static int pick_side(int side, int mode) {
    for (int t = 0; t < 40; t++) {
        int v = (int)rnd((uint64_t)N);
        if (ok_mode(v, side, mode)) return v;
    }
    int off = (int)rnd((uint64_t)N);
    for (int i = 0; i < N; i++) {
        int v = (off + i) % N;
        if (ok_mode(v, side, mode)) return v;
    }
    return -1;
}

static void move_add(void) {
    int a = pick_side(0, 1), b = pick_side(1, 1);
    if (a < 0 || b < 0 || adjacent(a, b)) return;
    apply_add(a, b);
}

static void move_switch(void) {
    int a1 = pick_side(0, 2), a2 = pick_side(0, 2);
    if (a1 < 0 || a2 < 0 || a1 == a2) return;
    int b1 = nb[(size_t)a1 * DEG + rnd((uint64_t)deg[a1])];
    int b2 = nb[(size_t)a2 * DEG + rnd((uint64_t)deg[a2])];
    if (b1 == b2) return;
    if (adjacent(a1, b2) || adjacent(a2, b1)) return;
    apply_del(a1, b1);
    apply_del(a2, b2);
    apply_add(a1, b2);
    apply_add(a2, b1);
}

static void move_endpoint(void) {
    int s = (int)rnd(2);
    int x = pick_side(s, 2);
    if (x < 0) return;
    int y = nb[(size_t)x * DEG + rnd((uint64_t)deg[x])];
    int x2 = pick_side(s, 1);
    if (x2 < 0 || x2 == x || adjacent(x2, y)) return;
    apply_del(x, y);
    apply_add(x2, y);
}

static void move_del(void) {
    int x = pick_side(0, 2);
    if (x < 0) return;
    int y = nb[(size_t)x * DEG + rnd((uint64_t)deg[x])];
    apply_del(x, y);
}

static void step(double T) {
    nops = 0;
    double r = rndf();
    if (r < 0.25) move_add();
    else if (r < 0.70) move_switch();
    else if (r < 0.95) move_endpoint();
    else move_del();
    if (nops == 0) return;
    long nbad = bad_count();
    long delta = nbad - cur;
    if (delta <= 0 || rndf() < exp(-(double)delta / T)) cur = nbad;
    else undo_all();
    nops = 0;
}

static void save_best(void) {
    if (N <= bestN) return;
    long m = 0;
    for (int v = 0; v < N; v++) m += deg[v];
    m /= 2;
    int *E = malloc(sizeof(int) * 2 * (size_t)(m > 0 ? m : 1));
    if (!E) return;
    long c = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[(size_t)v * DEG + i];
            if (v < u) {
                E[2 * c] = v;
                E[2 * c + 1] = u;
                c++;
            }
        }
    }
    free(bestE);
    bestE = E;
    bestM = c;
    bestN = N;
    for (int v = 0; v < N; v++) bestCol[v] = col[v];
}

static void load_best(void) {
    N = bestN;
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        col[v] = bestCol[v];
    }
    for (long i = 0; i < bestM; i++) add_e(bestE[2 * i], bestE[2 * i + 1]);
}

/* Add one vertex joined to DIAM-independent DEG opposite-side vertices. */
static int grow_one(void) {
    if (N < 3 || N >= MAXN - 2) return 0;
    int x = N;
    int side = (int)rnd(2);
    int picked[MAXDEG];
    int k = 0;
    long tries = 0;
    N++;
    col[x] = side;
    deg[x] = 0;
    while (k < DEG && tries < 200000) {
        tries++;
        int y = (int)rnd((uint64_t)(N - 1));
        if (col[y] == side) continue;
        int dup = 0;
        for (int j = 0; j < k; j++)
            if (picked[j] == y) { dup = 1; break; }
        if (!dup) picked[k++] = y;
    }
    if (k < DEG) {
        N--;
        return 0;
    }
    for (int i = 0; i < k; i++) {
        int y = picked[i];
        if (deg[y] >= DEG) {
            int z = nb[(size_t)y * DEG + rnd((uint64_t)deg[y])];
            del_e(y, z);
        }
        add_e(x, y);
    }
    return 1;
}

/* Anneal for at most L steps; returns 1 and saves when a valid state is reached. */
static int sa_run(long L, double T0, double T1, double tlimit) {
    if (cur == 0) {
        save_best();
        return 1;
    }
    for (long t = 0; t < L; t++) {
        if (elapsed() > tlimit) return 0;
        double T = T0 * pow(T1 / T0, (double)t / (double)L);
        step(T);
        if (cur == 0) {
            save_best();
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    budget = atof(argv[4]);
    t0 = clock();

    if (d < 1 || D < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    DEG = d;
    DIAM = D;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n >= MAXN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    col = calloc(MAXN, sizeof(int));
    deg = calloc(MAXN, sizeof(int));
    nb = malloc(sizeof(int) * (size_t)MAXN * (size_t)DEG);
    RA = malloc(sizeof(uint64_t) * (size_t)MAXN * (size_t)MAXW);
    RB = malloc(sizeof(uint64_t) * (size_t)MAXN * (size_t)MAXW);
    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *colr = malloc(sizeof(int) * (size_t)n);
    int *stk = malloc(sizeof(int) * (size_t)n);
    if (!col || !deg || !nb || !RA || !RB || !eu || !ev || !colr || !stk) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v) {
            printf("0 0\n");
            return 0;
        }
        eu[i] = u;
        ev[i] = v;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        if (deg[eu[i]] >= DEG || deg[ev[i]] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_e(eu[i], ev[i]);
    }

    /* bipartition by BFS */
    for (int v = 0; v < N; v++) colr[v] = -1;
    for (int s = 0; s < N; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[(size_t)u * DEG + i];
                if (colr[v] < 0) {
                    colr[v] = 1 - colr[u];
                    stk[sp++] = v;
                } else if (colr[v] == colr[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < N; v++) col[v] = colr[v];

    cur = bad_count();
    if (cur == 0) save_best();

    /* repair phase: reach zero bad pairs at the start size */
    if (cur > 0) {
        double limit = budget * 0.5;
        while (cur > 0 && elapsed() < limit) {
            if (sa_run(20000, 3.0, 0.3, limit)) break;
        }
    }

    /* growth phase: grow one vertex from the best valid state and anneal */
    int gfails = 0;
    while (elapsed() < budget && bestN > 0 && gfails < 50) {
        load_best();
        if (!grow_one()) {
            gfails++;
            continue;
        }
        gfails = 0;
        cur = bad_count();
        long L = 3000 + 4L * N;
        sa_run(L, 3.0, 0.3, budget);
    }

    if (bestN == 0 || bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", bestN, bestM);
    for (long c = 0; c < bestM; c++) {
        printf("%d %d\n", bestE[2 * c], bestE[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact and near-exact constructions.
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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _run_engine(source, args, stdin_graph, timeout):
    """Run a C engine and parse its output; returns (n, edges), with (0, []) for nothing found."""
    text = lib.run_c(source, args, stdin_graph=stdin_graph, timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 4.0)
    rng = random.Random(seed)

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

    def left():
        return deadline - time.monotonic()

    def elapsed_wall():
        return time.monotonic() - start

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and left() > 0:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: bi-Cayley annealing (about 40% of the remaining budget).
    if left() > 0.5:
        s1 = 0.4 * left()
        timeout = max(1.0, min(s1 + 3.0, time_limit - elapsed_wall() - 1.5))
        try:
            n, e = _run_engine(C_BICAYLEY, [d, D, seed, f"{s1:.2f}", best_n], None, timeout)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: graph-level local search with vertex growth, from the best graph so far.
    if left() > 0.5:
        s2 = left()
        timeout = max(1.0, min(s2 + 3.0, time_limit - elapsed_wall() - 1.5))
        try:
            n, e = _run_engine(C_LS, [d, D, seed, f"{s2:.2f}"], best, timeout)
            consider(n, e)
        except Exception:
            pass

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
