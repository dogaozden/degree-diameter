import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over several group families, searched by annealing.
#
# Families (a group G of order G = K2*M or q*c is built as a full table):
#   gt 0: cyclic-by-cyclic semidirect product Z_M x| Z_K2 (the old family).
#   gt 1: GF(q) (additive) x| Z_c, where Z_c acts by multiplication by the
#         subgroup of order c of GF(q)*. Non-cyclic abelian and nonabelian
#         groups of exponent p, not available in the old family.
#   gt 2: GF(q) x| Z_c, where Z_c acts by Frobenius powers (c divides k, q=p^k).
#
# Each run picks a family, a base size K in {1,2,3} and a group order near the
# record. Base graph: K A-vertices and K B-vertices, DEG layers, one dart per
# (layer, A-vertex). Dart (i,j,s) joins A_{i,g} to B_{j,g*s}. Vertex 0 of each
# group block is the identity; left multiplication is an automorphism, so
# diameter <= D iff BFS of depth D from each of the 2K block identities covers
# everything.
#
# Search: simulated annealing on a breakout-weighted cost, followed by an elite
# pool with iterated local search. Deadlines use wall-clock time from program
# start.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 48
#define POOLP 0.6
#define BRK 150
#define QMAX 1800
#define GMAXT 1800
#define CANDMAX 8192
#define MAXDEG 16

typedef struct { int gt, K, G, p1, p2, p3; } GDesc;
typedef struct { int gt, p1, p2, G; } Cand;
typedef struct { GDesc d; long long cost; int *J, *S; } Cfg;

static uint64_t rs[2];
static struct timespec T0;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

/* ---------------- finite fields of prime-power order ---------------- */

static int *fexp[QMAX + 1], *flog[QMAX + 1];
static int fpr[QMAX + 1], fkk[QMAX + 1];
static int pplist[QMAX], ppk[QMAX], npp = 0;

static void factor_pp(int q, int *p, int *k) {
    int x = q, pp = q;
    for (int d = 2; d * d <= q; d++)
        if (q % d == 0) { pp = d; break; }
    int kk = 0;
    while (x % pp == 0) { x /= pp; kk++; }
    *p = pp;
    *k = (x == 1) ? kk : -1;
}

/* Multiply the field element with code a by x modulo f = x^k + sum c_i x^i. */
static int mulx(int a, int p, int k, const int *c) {
    int d[16], s[16];
    int x = a;
    for (int i = 0; i < k; i++) { d[i] = x % p; x /= p; }
    int t = d[k - 1];
    for (int i = 0; i < k; i++) {
        int v = (i > 0 ? d[i - 1] : 0) - t * c[i];
        v %= p;
        if (v < 0) v += p;
        s[i] = v;
    }
    int r = 0;
    for (int i = k - 1; i >= 0; i--) r = r * p + s[i];
    return r;
}

/* Build exp/log tables of GF(q) by finding a polynomial for which x is primitive. */
static int ensure_field(int q) {
    if (q < 2 || q > QMAX) return 0;
    if (fexp[q]) return 1;
    int p, k;
    factor_pp(q, &p, &k);
    if (k <= 0) return 0;
    int *ex = malloc(sizeof(int) * (size_t)q);
    int *lg = malloc(sizeof(int) * (size_t)q);
    int c[16];
    for (int cv = 1; cv < q; cv++) {
        int x = cv;
        for (int i = 0; i < k; i++) { c[i] = x % p; x /= p; }
        if (c[0] == 0) continue;
        ex[0] = 1;
        int ok = 1;
        for (int n = 1; n < q - 1; n++) {
            int y = mulx(ex[n - 1], p, k, c);
            if (y == 1) { ok = 0; break; }
            ex[n] = y;
        }
        if (ok && mulx(ex[q - 2], p, k, c) != 1) ok = 0;
        if (ok) {
            for (int n = 0; n < q - 1; n++) lg[ex[n]] = n;
            fexp[q] = ex;
            flog[q] = lg;
            fpr[q] = p;
            fkk[q] = k;
            return 1;
        }
    }
    free(ex);
    free(lg);
    return 0;
}

static int fadd(int p, int k, int a, int b) {
    int r = 0, pw = 1;
    for (int i = 0; i < k; i++) {
        int s = (a % p + b % p) % p;
        r += s * pw;
        pw *= p;
        a /= p;
        b /= p;
    }
    return r;
}

static int fmul(int q, int a, int b) {
    if (!a || !b) return 0;
    return fexp[q][(flog[q][a] + flog[q][b]) % (q - 1)];
}

/* Frobenius power: a^e with e = p^j mod (q-1). */
static int ffrob(int q, int a, long long e) {
    if (!a) return 0;
    return fexp[q][(int)((long long)flog[q][a] * e % (q - 1))];
}

/* ---------------- group tables ---------------- */

static void build_table(const GDesc *d) {
    int Gn = d->G;
    if (d->gt == 0) {
        int M = d->p1, K2 = d->p2, R = d->p3;
        int *rp = malloc(sizeof(int) * (size_t)K2);
        rp[0] = 1 % M;
        for (int b = 1; b < K2; b++) rp[b] = (int)((long long)rp[b - 1] * R % M);
        for (int x = 0; x < Gn; x++) {
            int a = x / K2, b = x % K2;
            for (int y = 0; y < Gn; y++) {
                int c = y / K2, e = y % K2;
                int ra = (int)(((long long)a + (long long)rp[b] * c) % M);
                gtab[(size_t)x * Gn + y] = ra * K2 + (b + e) % K2;
            }
        }
        free(rp);
    } else {
        int q = d->p1, C = d->p2;
        int p = fpr[q], k = fkk[q];
        int *act = malloc(sizeof(int) * (size_t)C * (size_t)q);
        for (int b = 0; b < C; b++) {
            long long e = 1 % (q - 1);
            if (d->gt == 2) {
                int j = b * (k / C);
                for (int i = 0; i < j; i++) e = e * p % (q - 1);
            }
            int mub = fexp[q][(int)((long long)b * ((q - 1) / C) % (q - 1))];
            for (int w = 0; w < q; w++) {
                int val = (d->gt == 1) ? fmul(q, mub, w) : ffrob(q, w, e);
                act[(size_t)b * q + w] = val;
            }
        }
        for (int x = 0; x < Gn; x++) {
            int v = x / C, b = x % C;
            for (int y = 0; y < Gn; y++) {
                int w = y / C, e2 = y % C;
                int vv = fadd(p, k, v, act[(size_t)b * q + w]);
                gtab[(size_t)x * Gn + y] = vv * C + (b + e2) % C;
            }
        }
        free(act);
    }
}

/* ---------------- configuration state ---------------- */

static int DEG, DIAM, K, G, T, MAXT;
static GDesc GD;
static int *gtab = NULL;
static int *dI = NULL, *dJ = NULL, *dS = NULL, *perm = NULL, *adj = NULL, *cnt = NULL;
static int *stamp = NULL, *fr = NULL, *nx = NULL, *bestJ = NULL, *bestS = NULL;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;
static int curstamp = 0;
static double DEADLINE;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static Cfg pool[POOLMAX];
static int npool = 0;
static Cand cands[CANDMAX];

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gtab[(size_t)g * G + s];
}

/* Returns the true cost (sum of uncovered ordered pairs over block identities).
   Sets unc[r] per block and last_w to the weighted cost. */
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

static void setup_group(const GDesc *d) {
    GD = *d;
    K = d->K;
    G = d->G;
    T = DEG * K;
    int N = 2 * K * G;
    gtab = malloc(sizeof(int) * (size_t)G * G);
    build_table(d);
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
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
}

static void free_group(void) {
    free(gtab); free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    gtab = NULL;
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = NULL;
    stamp = fr = nx = NULL;
    wt = unc = NULL;
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

static void random_init(void) {
    int p[8];
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

/* Annealing on the weighted cost with breakout weight bumps. The caller must
   have just called eval_cost(). The best state by true cost goes to bestJ/bestS. */
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
    c->d = GD;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

/* Eligible pool entry: group order must still beat the record; best of 3 samples. */
static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (2LL * pool[i].d.K * pool[i].d.G > best_n) cand[nc++] = i;
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* ---------------- random group choice ---------------- */

/* Fill cands with groups of family gt whose order lies in [lo, hi]. */
static int collect(int gt, long long lo, long long hi) {
    int nc = 0;
    if (hi > GMAXT) hi = GMAXT;
    if (lo < 2) lo = 2;
    if (gt == 0) {
        for (int K2 = 1; K2 <= 12; K2++) {
            long long mlo = (lo + K2 - 1) / K2, mhi = hi / K2;
            if (mlo < 2) mlo = 2;
            for (long long M = mlo; M <= mhi && nc < CANDMAX; M++) {
                cands[nc].gt = 0;
                cands[nc].p1 = (int)M;
                cands[nc].p2 = K2;
                cands[nc].G = (int)(M * K2);
                nc++;
            }
        }
        return nc;
    }
    for (int i = 0; i < npp && nc < CANDMAX; i++) {
        long long q = pplist[i];
        if (gt == 1) {
            for (long long c = 1; c <= q - 1 && q * c <= hi && nc < CANDMAX; c++) {
                if ((q - 1) % c) continue;
                long long Gg = q * c;
                if (Gg < lo) continue;
                cands[nc].gt = 1;
                cands[nc].p1 = (int)q;
                cands[nc].p2 = (int)c;
                cands[nc].G = (int)Gg;
                nc++;
            }
        } else {
            int kk = ppk[i];
            for (int c = 2; c <= kk && q * c <= hi && nc < CANDMAX; c++) {
                if (kk % c) continue;
                long long Gg = q * c;
                if (Gg < lo) continue;
                cands[nc].gt = 2;
                cands[nc].p1 = (int)q;
                cands[nc].p2 = c;
                cands[nc].G = (int)Gg;
                nc++;
            }
        }
    }
    return nc;
}

/* Turn a candidate into a full descriptor. Returns 0 if it cannot be realised. */
static int make_desc(GDesc *o, int K0, const Cand *c) {
    o->K = K0;
    o->gt = c->gt;
    o->G = c->G;
    o->p1 = c->p1;
    o->p2 = c->p2;
    o->p3 = 0;
    if (c->gt == 0) {
        int M = c->p1, K2 = c->p2;
        if (K2 == 1) { o->p3 = 1; return 1; }
        for (int tr = 0; tr < 200; tr++) {
            int x = 1 + rnd_int(M - 1);
            if (gcd_i(x, M) == 1 && powmod(x, K2, M) == 1 % M) {
                o->p3 = x;
                return 1;
            }
        }
        return 0;
    }
    return ensure_field(c->p1) ? 1 : 0;
}

static void make_fresh(GDesc *o) {
    int K0 = 1 + rnd_int(3);
    long long gmin = best_n / (2LL * K0) + 1;
    if (gmin < 2) gmin = 2;
    long long spread = gmin / 5 + 3;
    for (int widen = 0; widen < 5; widen++) {
        long long lo = gmin, hi = gmin + (spread << widen);
        if (hi > GMAXT) hi = GMAXT;
        for (int tr = 0; tr < 6; tr++) {
            int r = rnd_int(10);
            int gt = r < 5 ? 1 : (r < 8 ? 2 : 0);
            int nc = collect(gt, lo, hi);
            if (nc == 0) continue;
            for (int pk = 0; pk < 20; pk++) {
                const Cand *c = &cands[rnd_int(nc)];
                if (make_desc(o, K0, c)) return;
            }
        }
    }
    /* Fallback: cyclic group Z_gmin with one base pair (always valid). */
    o->K = 1;
    o->gt = 0;
    o->G = (int)gmin;
    o->p1 = (int)gmin;
    o->p2 = 1;
    o->p3 = 1;
}

/* ---------------- driver ---------------- */

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
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    MAXT = 3 * DEG;
    for (int q = 2; q <= QMAX; q++) {
        int p, k;
        factor_pp(q, &p, &k);
        if (k > 0) {
            pplist[npp] = q;
            ppk[npp] = k;
            npp++;
        }
    }
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            setup_group(&pool[pi].d);
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_group();
            continue;
        }

        GDesc gd;
        make_fresh(&gd);
        setup_group(&gd);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
        free_group();
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
# Safe baseline families.
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
# Driver: baselines in Python, then the C annealer over several group families.
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

    # The deadline inside C is measured from program start, so compile time is
    # excluded; a 1.5 s reserve covers a cold compile, parsing and validation.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
