"""Permutation-group voltage lifts with an elite pool (ILS), alternating with bad-pair-annealed
growth by two vertices.

What changed from the cyclic/semidirect-only version:
  * Voltage groups are arbitrary permutation groups. Python passes generators (affine groups
    Z_m x| <r>, AGL(1,q), dihedral groups, PSL/PGL(2,q), cyclic groups, and direct products of
    these). C computes the closure and a full multiplication table, so any group with
    order <= 600 and degree <= 128 can serve as the voltage group.
  * Lifts pick K in 1..4 base vertices per side and a group whose lift order just beats the
    current best graph.
  * Grow phase is unchanged: insert one vertex per side, rewire to restore degree, then anneal
    degree-preserving swaps until no pair is at distance > D.

Safety: K_{d,d} (or a single edge) is the fallback. Known D = 3 constructions are passed as the
start graph. Every graph returned by C is re-checked with lib.is_valid in Python.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 48
#define POOLP 0.6
#define MAXK 4
#define MAXDEG 64
#define MAXPERM 128
#define GMAX 600
#define HSZ 4096
#define MAXGRP 96
#define MAXGEN 8

typedef unsigned char uc;

/* ------------------------------------------------------------ utilities */

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE, LIFT_T;
static int DEG, DIAM;
static int lift_no_cand = 0;

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

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

/* ------------------------------------------------------------ permutation groups */

typedef struct {
    int G;
    unsigned short *mul; /* mul[x*G+y] = index of (perm x) o (perm y) */
} Grp;

static Grp grp[MAXGRP];
static int ngrp = 0;

static unsigned phash(const uc *p, int k) {
    uint32_t h = 2166136261u;
    for (int i = 0; i < k; i++) {
        h ^= p[i];
        h *= 16777619u;
    }
    return (unsigned)(h & (HSZ - 1));
}

/* Find p among the cnt stored perms; if absent and ins, append it.
 * Returns index, -1 if absent (ins = 0), or -2 if the table is full. */
static int pfind(uc *E, int *cnt, int k, int *ht, const uc *p, int ins) {
    unsigned h = phash(p, k);
    while (ht[h] >= 0) {
        if (memcmp(E + (size_t)ht[h] * k, p, (size_t)k) == 0) return ht[h];
        h = (h + 1) & (HSZ - 1);
    }
    if (!ins) return -1;
    if (*cnt >= GMAX) return -2;
    memcpy(E + (size_t)(*cnt) * k, p, (size_t)k);
    ht[h] = *cnt;
    return (*cnt)++;
}

/* Closure of the generators (perms of 0..pd-1); fills out on success. */
static int build_group(int pd, int ng, const int *gens, Grp *out) {
    static uc E[GMAX * MAXPERM];
    static int ht[HSZ];
    uc cur[MAXPERM], tmp[MAXPERM], gs[MAXPERM];
    int cnt = 0;
    for (int s = 0; s < ng; s++) {
        int seen[MAXPERM];
        memset(seen, 0, sizeof(seen));
        for (int i = 0; i < pd; i++) {
            int v = gens[s * pd + i];
            if (v < 0 || v >= pd || seen[v]) return 0;
            seen[v] = 1;
        }
    }
    for (int i = 0; i < HSZ; i++) ht[i] = -1;
    for (int i = 0; i < pd; i++) cur[i] = (uc)i;
    if (pfind(E, &cnt, pd, ht, cur, 1) < 0) return 0;
    for (int h = 0; h < cnt; h++) {
        for (int s = 0; s < ng; s++) {
            for (int i = 0; i < pd; i++) gs[i] = (uc)gens[s * pd + i];
            for (int i = 0; i < pd; i++) tmp[i] = E[(size_t)h * pd + gs[i]];
            if (pfind(E, &cnt, pd, ht, tmp, 1) < 0) return 0;
        }
    }
    int G = cnt;
    unsigned short *mul = malloc(sizeof(unsigned short) * (size_t)G * G);
    if (!mul) return 0;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++) {
            for (int i = 0; i < pd; i++) tmp[i] = E[(size_t)x * pd + E[(size_t)y * pd + i]];
            int z = pfind(E, &cnt, pd, ht, tmp, 0);
            if (z < 0) {
                free(mul);
                return 0;
            }
            mul[(size_t)x * G + y] = (unsigned short)z;
        }
    out->G = G;
    out->mul = mul;
    return 1;
}

/* Spec on argv: "ngroups", then per group "deg ngens gens...". */
static void load_groups(const char *s) {
    char *end;
    long nall = strtol(s, &end, 10);
    const char *p = end;
    static int gbuf[MAXGEN * MAXPERM];
    for (long gi = 0; gi < nall; gi++) {
        long pd = strtol(p, &end, 10);
        if (end == p) return;
        p = end;
        long ng = strtol(p, &end, 10);
        if (end == p) return;
        p = end;
        int ok = (pd >= 1 && pd <= MAXPERM && ng >= 1 && ng <= MAXGEN);
        for (long i = 0; i < ng * pd; i++) {
            long v = strtol(p, &end, 10);
            if (end == p) return;
            p = end;
            if (ok) gbuf[i] = (int)v;
        }
        if (ok && ngrp < MAXGRP) {
            Grp g;
            if (build_group((int)pd, (int)ng, gbuf, &g)) grp[ngrp++] = g;
        }
    }
}

/* ------------------------------------------------------------ general graph */

typedef struct {
    int n, cap;
    int *deg, *adj;
    unsigned char *side;
} Gr;

static Gr best;

static void gr_alloc(Gr *g, int n, int cap) {
    g->n = n;
    g->cap = cap;
    g->deg = calloc((size_t)n + 1, sizeof(int));
    g->adj = malloc(sizeof(int) * ((size_t)n * cap + 1));
    g->side = calloc((size_t)n + 1, 1);
}

static void gr_free(Gr *g) {
    free(g->deg);
    free(g->adj);
    free(g->side);
    g->deg = NULL;
    g->adj = NULL;
    g->side = NULL;
    g->n = 0;
}

static int gr_has(const Gr *g, int u, int v) {
    const int *a = g->adj + (size_t)u * g->cap;
    for (int i = 0; i < g->deg[u]; i++)
        if (a[i] == v) return 1;
    return 0;
}

static int gr_add(Gr *g, int u, int v) {
    if (g->deg[u] >= g->cap || g->deg[v] >= g->cap) return 0;
    g->adj[(size_t)u * g->cap + g->deg[u]++] = v;
    g->adj[(size_t)v * g->cap + g->deg[v]++] = u;
    return 1;
}

static void gr_del_half(Gr *g, int u, int v) {
    int *a = g->adj + (size_t)u * g->cap;
    for (int i = 0; i < g->deg[u]; i++)
        if (a[i] == v) {
            a[i] = a[--g->deg[u]];
            return;
        }
}

static void gr_del(Gr *g, int u, int v) {
    gr_del_half(g, u, v);
    gr_del_half(g, v, u);
}

static long moore_bound(void) {
    if (DIAM <= 0 || DEG <= 0) return 1;
    if (DEG == 1) return 2;
    if (DEG == 2) return 2L * DIAM;
    long s = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        s += p;
        p *= (DEG - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Number of unordered pairs at distance > DIAM; fills badv[v] if non-NULL. */
static long gr_bad(const Gr *g, int *badv) {
    int n = g->n;
    if (n <= 0) return 0;
    int W = (n + 63) / 64;
    size_t sz = (size_t)n * W;
    uint64_t *cur = calloc(sz, sizeof(uint64_t));
    uint64_t *nxt = calloc(sz, sizeof(uint64_t));
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[(size_t)v * g->cap + i];
                const uint64_t *s = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        if (badv) badv[v] = n - c;
        total += n - c;
    }
    free(cur);
    free(nxt);
    return total / 2;
}

static int gr_valid(const Gr *g) {
    int n = g->n;
    if (n <= 0) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > DEG || g->deg[v] > g->cap) return 0;
        const int *a = g->adj + (size_t)v * g->cap;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = a[i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (a[j] == u) return 0;
        }
    }
    return gr_bad(g, NULL) == 0;
}

static void build_complete(Gr *g) {
    gr_alloc(g, 2 * DEG, DEG);
    for (int v = 0; v < 2 * DEG; v++) g->side[v] = (unsigned char)(v >= DEG);
    for (int a = 0; a < DEG; a++)
        for (int b = 0; b < DEG; b++) gr_add(g, a, DEG + b);
}

static void print_gr(const Gr *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[(size_t)u * g->cap + i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++) {
            int v = g->adj[(size_t)u * g->cap + i];
            if (u < v) printf("%d %d\n", u, v);
        }
}

/* ------------------------------------------------------------ group lifts */

/* Base: K vertices per side, group G with table MUL. Dart t = l*K + i joins
 * A-block dI[t] to B-block K + dJ[t] via the permutation g -> g * dS[t]. */
static int K, G, T, CG = -1;
static unsigned short *MUL;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static int curstamp;

static inline int gmul(int x, int y) { return (int)MUL[(size_t)x * G + y]; }

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void alloc_config(void) {
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
    curstamp = 0;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = NULL;
}

static void setup_config(int k, int gid) {
    K = k;
    CG = gid;
    G = grp[gid].G;
    MUL = grp[gid].mul;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

/* Cost = sum over the 2K block representatives of vertices beyond distance DIAM.
 * Left multiplication is an automorphism, so one representative per block suffices.
 * BIGC marks configurations with duplicate darts. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
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
            int *tmp = f;
            f = h;
            h = tmp;
            fsz = nsz;
        }
        total += N - count;
    }
    return total;
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
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > LIFT_T) break;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05);
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
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
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
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

static void emit_current(Gr *out) {
    int N = 2 * K * G;
    gr_alloc(out, N, DEG);
    for (int v = K * G; v < N; v++) out->side[v] = 1;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            gr_add(out, dI[t] * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
}

static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (2LL * K * G > (long long)best.n) {
        Gr c;
        emit_current(&c);
        if (gr_valid(&c)) {
            gr_free(&best);
            best = c;
        } else {
            gr_free(&c);
        }
    }
}

/* ------------------------------------------------------------ elite pool */

typedef struct {
    int K, gid;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

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
    c->K = K;
    c->gid = CG;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * grp[pool[i].gid].G;
        if (nn > (long long)best.n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* Groups g with 2*k*G > nb; with band, also 2*k*G <= nb*1.25 + 60. */
static int collect_groups(int k, long nb, int *cand, int band) {
    int nc = 0;
    for (int g = 0; g < ngrp; g++) {
        long N = 2L * k * grp[g].G;
        if (N <= nb) continue;
        if (band && N > nb + nb / 4 + 60) continue;
        cand[nc++] = g;
    }
    return nc;
}

/* ------------------------------------------------------------ lift phase */

static void lift_search(double until) {
    static const int kc[7] = {1, 1, 2, 2, 3, 3, 4};
    int cand[MAXGRP];
    LIFT_T = until;
    lift_no_cand = 0;
    while (elapsed() < until) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg *c = &pool[pi];
            setup_config(c->K, c->gid);
            memcpy(dJ, c->J, sizeof(int) * (size_t)T);
            memcpy(dS, c->S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
            continue;
        }

        int k = 1, nc = 0;
        for (int attempt = 0; attempt < 8 && nc == 0; attempt++) {
            k = kc[rnd_int(7)];
            nc = collect_groups(k, (long)best.n, cand, 1);
        }
        for (int kk = 1; kk <= MAXK && nc == 0; kk++) {
            k = kk;
            nc = collect_groups(k, (long)best.n, cand, 0);
        }
        if (nc == 0) {
            lift_no_cand = 1;
            return;
        }
        int gid = cand[rnd_int(nc)];
        setup_config(k, gid);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
        free_config();
    }
}

/* ------------------------------------------------------------ grow phase */

static int grow_once(double until) {
    int n = best.n;
    if (n <= 0 || (long)(n + 2) > moore_bound()) return 0;
    int N = n + 2;
    Gr w;
    gr_alloc(&w, N, DEG);
    for (int v = 0; v < n; v++) {
        w.deg[v] = best.deg[v];
        w.side[v] = best.side[v];
        memcpy(w.adj + (size_t)v * DEG, best.adj + (size_t)v * best.cap, sizeof(int) * best.deg[v]);
    }
    int x = n, y = n + 1;
    w.side[x] = 0;
    w.side[y] = 1;
    gr_add(&w, x, y);

    int *used = calloc((size_t)N, sizeof(int));
    used[x] = 1;
    used[y] = 1;
    int k = 0;
    for (int tries = 0; k < DEG - 1 && tries < 100000; tries++) {
        int a = rnd_int(n);
        if (w.side[a] != 0 || used[a] || w.deg[a] == 0) continue;
        int b = w.adj[(size_t)a * DEG + rnd_int(w.deg[a])];
        if (b >= n || used[b]) continue;
        gr_del(&w, a, b);
        gr_add(&w, x, b);
        gr_add(&w, y, a);
        used[a] = 1;
        used[b] = 1;
        k++;
    }

    int *badv = malloc(sizeof(int) * (size_t)N);
    long bad = gr_bad(&w, badv);
    double Tm = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && elapsed() > until) break;
        int v = rnd_int(N);
        for (int tr = 0; tr < 30 && badv[v] == 0; tr++) v = rnd_int(N);
        if (w.deg[v] == 0) continue;
        int u = w.adj[(size_t)v * DEG + rnd_int(w.deg[v])];
        int s = rnd_int(N);
        if (s == v || w.side[s] != w.side[v] || w.deg[s] == 0) continue;
        int t = w.adj[(size_t)s * DEG + rnd_int(w.deg[s])];
        if (t == u || gr_has(&w, v, t) || gr_has(&w, s, u)) continue;
        gr_del(&w, v, u);
        gr_del(&w, s, t);
        gr_add(&w, v, t);
        gr_add(&w, s, u);
        long nb = gr_bad(&w, badv);
        if (nb <= bad || rnd_unit() < exp((double)(bad - nb) / Tm)) {
            bad = nb;
        } else {
            gr_del(&w, v, t);
            gr_del(&w, s, u);
            gr_add(&w, v, u);
            gr_add(&w, s, t);
        }
        Tm *= 0.9995;
        if (Tm < 0.05) Tm = 1.0;
    }

    int ok = (bad == 0) && gr_valid(&w);
    free(used);
    free(badv);
    if (ok) {
        gr_free(&best);
        best = w;
    } else {
        gr_free(&w);
    }
    return ok;
}

static void grow_phase(double until) {
    while (elapsed() < until) {
        if (best.n <= 0 || (long)(best.n + 2) > moore_bound()) break;
        double left = until - elapsed();
        double slice = left < 3.0 ? left : (left / 4 > 3.0 ? left / 4 : 3.0);
        grow_once(elapsed() + slice);
    }
}

/* ------------------------------------------------------------ input */

static void read_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || m < 0) return;
    int *eu = malloc(sizeof(int) * ((size_t)m + 1));
    int *ev = malloc(sizeof(int) * ((size_t)m + 1));
    int ok = 1;
    for (int e = 0; e < m && ok; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) ok = 0;
        else if (eu[e] < 0 || ev[e] < 0 || eu[e] >= n || ev[e] >= n || eu[e] == ev[e]) ok = 0;
    }
    Gr g;
    gr_alloc(&g, n, DEG);
    for (int e = 0; e < m && ok; e++)
        if (!gr_add(&g, eu[e], ev[e])) ok = 0;

    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        q[tail++] = s;
        while (head < tail && ok) {
            int v = q[head++];
            for (int i = 0; i < g.deg[v]; i++) {
                int u = g.adj[(size_t)v * g.cap + i];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    q[tail++] = u;
                } else if (col[u] == col[v]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (ok)
        for (int v = 0; v < n; v++) g.side[v] = (unsigned char)col[v];
    if (ok && gr_valid(&g)) {
        gr_free(&best);
        best = g;
    } else {
        gr_free(&g);
    }
    free(col);
    free(q);
    free(eu);
    free(ev);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [group_spec] < start_graph\n");
        return 2;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)DEG * MAXK);
        pool[i].S = malloc(sizeof(int) * (size_t)DEG * MAXK);
        pool[i].cost = BIGC;
        pool[i].K = 1;
        pool[i].gid = 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (argc >= 6) load_groups(argv[5]);
    read_start();

    if (DIAM >= 2) {
        double t_now = elapsed();
        double span = DEADLINE - t_now;
        if (span > 0) {
            lift_search(t_now + span * 0.3);
            if (best.n <= 0) lift_search(DEADLINE);
            while (best.n > 0 && elapsed() < DEADLINE) {
                int before = best.n;
                double left = DEADLINE - elapsed();
                grow_phase(elapsed() + left * 0.5);
                if (elapsed() >= DEADLINE) break;
                left = DEADLINE - elapsed();
                lift_search(elapsed() + left * 0.3);
                if (lift_no_cand && best.n == before) break;
            }
        }
    }

    if (best.n <= 0) build_complete(&best);
    if (!gr_valid(&best)) {
        gr_free(&best);
        build_complete(&best);
        if (!gr_valid(&best)) {
            printf("0 0\n");
            return 0;
        }
    }
    print_gr(&best);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: permutation-group library, known constructions and fallbacks.
# ----------------------------------------------------------------------------

_GMIN, _GMAX = 40, 440     # target voltage-group orders
_MAXPERM = 128             # degree limit of the permutation representation
_MAX_GROUPS = 50
_MAX_SPEC_INTS = 14000     # keeps the argv string well under the OS limit


def _ord_mod(r, m):
    """Multiplicative order of the unit r modulo m."""
    t, x = 1, r % m
    while x != 1 % m:
        x = (x * r) % m
        t += 1
    return t


def _field_ord(F, g):
    t, x = 1, g
    while x != 1:
        x = F.mul(x, g)
        t += 1
    return t


def _affine_mod(m, r):
    """Z_m x| <r> acting on m points: x -> x+1 and x -> r x."""
    return (m * _ord_mod(r, m), m,
            [[(x + 1) % m for x in range(m)], [(r * x) % m for x in range(m)]])


def _dihedral(m):
    """Dihedral group of order 2m acting on m points."""
    return (2 * m, m, [[(x + 1) % m for x in range(m)], [(-x) % m for x in range(m)]])


def _cyclic(m):
    return (m, m, [[(x + 1) % m for x in range(m)]])


def _field_affine(F, g):
    """Translations of GF(q) times multiplication by g (AGL-type subgroup)."""
    q = F.q
    gens = [[F.add(x, F.p ** i) for x in range(q)] for i in range(F.k)]
    gens.append([F.mul(g, x) for x in range(q)])
    return (q * _field_ord(F, g), q, gens)


def _pgl2(q, square):
    """PGL(2, q) (or PSL(2, q) when square) acting on the projective line (inf = q)."""
    F = lib.GF(q)
    INF = q
    prim = F.primitive_element()
    g = F.mul(prim, prim) if square else prim
    t = [INF if x == INF else F.add(x, 1) for x in range(q + 1)]
    ms = [INF if x == INF else F.mul(g, x) for x in range(q + 1)]

    def inv_map(x):
        if x == INF:
            return 0
        if x == 0:
            return INF
        return F.neg(F.inv(x))

    iv = [inv_map(x) for x in range(q + 1)]
    est = q * (q * q - 1) // (2 if (square and q % 2 == 1) else 1)
    return (est, q + 1, [t, ms, iv])


def _product(A, B):
    """Direct product on disjoint supports."""
    ka, kb = A[1], B[1]
    gens = [g + list(range(ka, ka + kb)) for g in A[2]]
    gens += [list(range(ka)) + [ka + x for x in g] for g in B[2]]
    return (A[0] * B[0], ka + kb, gens)


def _group_spec(seed):
    """Permutation-group candidates for the C lift search, as one argv string."""
    rng = random.Random(seed * 7919 + 17)
    base = []
    for m in range(2, 61):
        for r in range(1, m):
            if math.gcd(r, m) == 1:
                g = _affine_mod(m, r)
                if _GMIN <= g[0] <= _GMAX:
                    base.append(g)
    for m in range(3, _MAXPERM + 1):
        g = _dihedral(m)
        if _GMIN <= g[0] <= _GMAX:
            base.append(g)
    for m in range(_GMIN, min(_GMAX, _MAXPERM) + 1):
        base.append(_cyclic(m))
    for q in range(4, 65):
        if lib.is_prime_power(q):
            F = lib.GF(q)
            gs = list(range(2, q))
            rng.shuffle(gs)
            for g in gs[:6]:
                cand = _field_affine(F, g)
                if _GMIN <= cand[0] <= _GMAX:
                    base.append(cand)
    for q in (4, 5, 7, 8, 9):
        for square in (False, True):
            cand = _pgl2(q, square)
            if _GMIN <= cand[0] <= _GMAX:
                base.append(cand)

    pool = [g for g in base if _GMIN <= g[0] <= _GMAX and g[1] <= _MAXPERM]
    small = [_cyclic(c) for c in range(2, 7)] + [_dihedral(m) for m in range(3, 5)]
    prods = []
    for A in pool:
        for B in small:
            order = A[0] * B[0]
            if _GMIN <= order <= _GMAX and A[1] + B[1] <= _MAXPERM:
                prods.append(_product(A, B))
    for _ in range(600):
        A, B = rng.choice(pool), rng.choice(pool)
        order = A[0] * B[0]
        if _GMIN <= order <= _GMAX and A[1] + B[1] <= _MAXPERM:
            prods.append(_product(A, B))

    allg = pool + prods
    rng.shuffle(allg)
    chosen, total = [], 0
    for g in allg:
        if len(chosen) >= _MAX_GROUPS:
            break
        cost = 2 + g[1] * len(g[2])
        if total + cost > _MAX_SPEC_INTS:
            continue
        chosen.append(g)
        total += cost

    ints = [len(chosen)]
    for _, deg, gens in chosen:
        ints.append(deg)
        ints.append(len(gens))
        for g in gens:
            ints.extend(g)
    return " ".join(map(str, ints))


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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _known_start(d, D):
    """Best construction Python builds directly for D = 3, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    start = None
    known = _known_start(d, D)
    if known is not None and lib.is_valid(known[0], known[1], d, D):
        start = known
        if known[0] > best[0]:
            best = known

    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if remaining < 2.0:
        return best
    try:
        spec = _group_spec(seed)
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", spec],
                        stdin_graph=start, timeout=remaining + 8.0)
        n, e = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass   # keep the valid fallback

    return best
