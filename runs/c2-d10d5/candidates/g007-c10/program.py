import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (lift search): bi-Cayley simulated annealing over Z_m x| Z_k2 in C.
# A bandit picks the base size k, groups are sampled near the current record
# order, and an elite refinement restarts from the best near-miss state.
# ----------------------------------------------------------------------------

C_LIFT = r"""
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
# Stage 2 (edge-switching growth): a different construction method.
# Start from a valid d-regular bipartite graph. Pick an edge (a,b), replace it
# by a path a-y, y-x, x-b with new vertices x (side A) and y (side B), then
# repair x and y to degree d with switches (a2,b2) -> (x,b2),(a2,y). Each switch
# keeps old degrees fixed. Accept the new pair only if the whole graph still has
# diameter <= D; otherwise undo. The graph stays bipartite by construction.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static uint64_t g_rs = 0x9E3779B97F4A7C15ULL;

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

static clock_t g_t0;
static double g_budget = 1.0;

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static int d_, D_, cap_, Wcap_;
static int n_;
static int *adj, *deg, *side;
static int *Al, nA_, *Bl, nB_;
static int lk[4096], lu[4096], lv[4096], nlog_;
static uint64_t *R1, *R2;

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[(size_t)u * d_ + i] == v) return 1;
    return 0;
}

static void raw_add(int u, int v) {
    adj[(size_t)u * d_ + deg[u]] = v;
    deg[u]++;
    adj[(size_t)v * d_ + deg[v]] = u;
    deg[v]++;
}

static void raw_del(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[(size_t)u * d_ + i] == v) {
            adj[(size_t)u * d_ + i] = adj[(size_t)u * d_ + deg[u] - 1];
            deg[u]--;
            break;
        }
    }
    for (int i = 0; i < deg[v]; i++) {
        if (adj[(size_t)v * d_ + i] == u) {
            adj[(size_t)v * d_ + i] = adj[(size_t)v * d_ + deg[v] - 1];
            deg[v]--;
            break;
        }
    }
}

static void L_add(int u, int v) {
    raw_add(u, v);
    if (nlog_ < 4096) {
        lk[nlog_] = 0;
        lu[nlog_] = u;
        lv[nlog_] = v;
        nlog_++;
    }
}

static void L_del(int u, int v) {
    raw_del(u, v);
    if (nlog_ < 4096) {
        lk[nlog_] = 1;
        lu[nlog_] = u;
        lv[nlog_] = v;
        nlog_++;
    }
}

static void undo_log(void) {
    for (int i = nlog_ - 1; i >= 0; i--) {
        if (lk[i] == 0) raw_del(lu[i], lv[i]);
        else raw_add(lu[i], lv[i]);
    }
    nlog_ = 0;
}

/* Returns 1 if the graph on vertices 0..N-1 is connected with diameter <= D_. */
static int check_valid(int N) {
    int W = (N + 63) / 64;
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s2 = cur + (size_t)adj[(size_t)v * d_ + i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *p = cur;
        cur = nxt;
        nxt = p;
    }
    for (int v = 0; v < N; v++) {
        const uint64_t *row = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) {
            uint64_t want = ~0ULL;
            if (w == W - 1 && (N % 64) != 0) want = (1ULL << (N % 64)) - 1ULL;
            if (row[w] != want) return 0;
        }
    }
    return 1;
}

static int attempt(void) {
    nlog_ = 0;
    if (nA_ == 0 || nB_ == 0) return 0;
    int a = Al[rnd((uint64_t)nA_)];
    if (deg[a] == 0) return 0;
    int b = adj[(size_t)a * d_ + rnd((uint64_t)deg[a])];
    int x = n_, y = n_ + 1;
    side[x] = 0;
    side[y] = 1;
    deg[x] = 0;
    deg[y] = 0;

    L_del(a, b);
    L_add(a, y);
    L_add(x, b);
    L_add(x, y);

    int tries = 0, ok = 1;
    while (deg[x] < d_) {
        if (++tries > 400 * d_) {
            ok = 0;
            break;
        }
        int a2 = Al[rnd((uint64_t)nA_)];
        if (deg[a2] == 0) continue;
        int b2 = adj[(size_t)a2 * d_ + rnd((uint64_t)deg[a2])];
        if (b2 >= n_) continue;
        if (has_edge(x, b2) || has_edge(y, a2)) continue;
        L_del(a2, b2);
        L_add(x, b2);
        L_add(a2, y);
    }

    if (ok) {
        int N = n_ + 2;
        if (N > cap_ || deg[x] != d_ || deg[y] != d_) ok = 0;
        else if (!check_valid(N)) ok = 0;
    }

    if (ok) {
        n_ += 2;
        Al[nA_++] = x;
        Bl[nB_++] = y;
        nlog_ = 0;
        return 1;
    }
    undo_log();
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: d D seed budget < graph\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    g_rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0xD1B54A32D192ED03ULL;
    if (g_rs == 0) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    g_t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || d_ < 1 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }

    cap_ = n0 + 4000;
    Wcap_ = (cap_ + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)cap_ * (size_t)d_);
    deg = calloc((size_t)cap_, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_);
    Al = malloc(sizeof(int) * (size_t)cap_);
    Bl = malloc(sizeof(int) * (size_t)cap_);
    R1 = malloc(sizeof(uint64_t) * (size_t)cap_ * (size_t)Wcap_);
    R2 = malloc(sizeof(uint64_t) * (size_t)cap_ * (size_t)Wcap_);
    int *q = malloc(sizeof(int) * (size_t)cap_);
    if (!adj || !deg || !side || !Al || !Bl || !R1 || !R2 || !q) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_) continue;
        if (has_edge(u, v)) continue;
        raw_add(u, v);
    }

    for (int v = 0; v < cap_; v++) side[v] = -1;
    int bip = 1;
    for (int s = 0; s < n0 && bip; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t && bip) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[(size_t)u * d_ + i];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                } else if (side[v] == side[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) {
        printf("0 0\n");
        return 0;
    }

    nA_ = 0;
    nB_ = 0;
    for (int v = 0; v < n0; v++) {
        if (side[v] == 0) Al[nA_++] = v;
        else Bl[nB_++] = v;
    }
    n_ = n0;
    nlog_ = 0;

    while (elapsed() < g_budget) {
        if (n_ + 2 > cap_) break;
        attempt();
    }

    long m = 0;
    for (int i = 0; i < nA_; i++) m += deg[Al[i]];
    printf("%d %ld\n", n_, m);
    for (int i = 0; i < nA_; i++) {
        int u = Al[i];
        for (int j = 0; j < deg[u]; j++) printf("%d %d\n", u, adj[(size_t)u * d_ + j]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs.
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
# C runners.
# ----------------------------------------------------------------------------

def _lift_search(d, D, seed, budget, min_n, timeout):
    """Run the lift-search engine; returns (n, edges), or (0, []) if nothing beats min_n."""
    text = lib.run_c(C_LIFT, [d, D, seed, f"{budget:.2f}", min_n], timeout=timeout)
    return lib.parse_graph_text(text)


def _grow(d, D, seed, graph, budget, timeout):
    """Run the edge-switching growth engine on a valid start graph; returns (n, edges)."""
    text = lib.run_c(C_GROW, [d, D, seed, f"{budget:.2f}"], stdin_graph=graph, timeout=timeout)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

    def time_left_cap(margin):
        """Timeout that stays inside the case limit."""
        used = time.monotonic() - start
        return max(1.0, min(deadline - time.monotonic() + 3.0, time_limit - used - margin))

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d < 3 or D < 3:
        return best

    # Stage 1: lift search (proven engine) takes about 55% of the remaining time.
    remaining = deadline - time.monotonic()
    if remaining > 1.5:
        lift_budget = 0.55 * remaining
        try:
            n, e = _lift_search(d, D, int(seed) & 0x7FFFFFFF, lift_budget, best_n,
                                timeout=time_left_cap(3.0) if lift_budget <= 0 else
                                max(1.0, min(lift_budget + 3.0, time_left_cap(3.0))))
            consider(n, e)
        except Exception:
            pass

    # Stage 2: edge-switching growth from the best valid graph found so far.
    remaining = deadline - time.monotonic()
    if remaining > 1.0 and best_n >= 2:
        try:
            n, e = _grow(d, D, (int(seed) * 7919 + 13) & 0x7FFFFFFF, best, remaining,
                         timeout=time_left_cap(2.0))
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
