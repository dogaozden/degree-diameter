"""Bi-Cayley lifts over the non-solvable groups PSL(2,p) and PGL(2,p), searched in C.

A lift with k base blocks per side has vertices A_{i,g} and B_{j,h} for g, h in G. Layer l
joins A_{i,g} to B_{sigma_l(i), g*s_{l,i}}, and every layer is a permutation of the blocks, so
the graph is bipartite and d-regular. Left multiplication is an automorphism, so a diameter
check needs one BFS per block representative. Non-solvable groups have far fewer relations
than the metabelian groups used before, which leaves the random search more room.

Fallbacks: K_{d,d} always, plus the projective-plane and Araujo-Pardo-Lopez constructions for D = 3.
Every candidate is checked with lib.is_valid before it is kept.
"""
import itertools
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

#define MAXN 20000
#define MAXD 32
#define MAXK 8
#define MAXCFG 16
#define GMAX 3600
#define EPOCH 4000

typedef struct {
    int p, G, id;
    int *mat;     /* G*4 normalized matrix entries */
    int *idx;     /* p^4 map: normalized code -> element index, or -1 */
    int *inv_p;   /* inverses mod p */
} Group;

static int dd, D;
static int GG, KK, NN, IDG;
static uint16_t *Rt = NULL;   /* Rt[s*G + g] = g*s */
static int *InvT = NULL;      /* InvT[s] = index of s^{-1} */
static int *ADJ = NULL;       /* ADJ[v*dd + l] = neighbour of v in layer l */
static unsigned *VIS = NULL;
static int *QU = NULL;
static unsigned GEN = 0;
static int SIG[MAXD][MAXK], VOL[MAXD][MAXK];
static int BSIG[MAXD][MAXK], BVOL[MAXD][MAXK];
static uint64_t rs = 88172645463325252ULL;

static int best_n = 0;
static long best_m = 0;
static int best_e[2 * (MAXN * MAXD / 2)];
static int cfg_t[MAXCFG], cfg_p[MAXCFG], cfg_k[MAXCFG];
static int ncfg = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ---------- group PSL(2,p) (typ 0) or PGL(2,p) (typ 1) as normalized matrices ---------- */

static int norm_idx(const Group *gr, int a, int b, int c, int e) {
    int p = gr->p;
    int v[4] = {a % p, b % p, c % p, e % p};
    int f = -1;
    for (int t = 0; t < 4; t++)
        if (v[t]) { f = v[t]; break; }
    if (f < 0) return -1;
    int iv = gr->inv_p[f];
    for (int t = 0; t < 4; t++) v[t] = v[t] * iv % p;
    return gr->idx[((v[0] * p + v[1]) * p + v[2]) * p + v[3]];
}

static int gmul(const Group *gr, int i, int j) {
    int p = gr->p;
    const int *A = gr->mat + 4 * i, *B = gr->mat + 4 * j;
    int a = (A[0] * B[0] + A[1] * B[2]) % p;
    int b = (A[0] * B[1] + A[1] * B[3]) % p;
    int c = (A[2] * B[0] + A[3] * B[2]) % p;
    int e = (A[2] * B[1] + A[3] * B[3]) % p;
    return norm_idx(gr, a, b, c, e);
}

static int build_group(Group *gr, int typ, int p) {
    memset(gr, 0, sizeof *gr);
    gr->p = p;
    int P4 = p * p * p * p;
    gr->inv_p = calloc((size_t)p, sizeof(int));
    for (int x = 1; x < p; x++)
        for (int y = 1; y < p; y++)
            if (x * y % p == 1) gr->inv_p[x] = y;
    int *isq = calloc((size_t)p, sizeof(int));
    for (int y = 0; y < p; y++) isq[y * y % p] = 1;
    gr->idx = malloc(sizeof(int) * (size_t)P4);
    for (int t = 0; t < P4; t++) gr->idx[t] = -1;
    gr->mat = malloc(sizeof(int) * 4 * (size_t)P4);
    int G = 0;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int e = 0; e < p; e++) {
                    int det = ((a * e - b * c) % p + p) % p;
                    if (!det) continue;
                    int v[4] = {a, b, c, e};
                    int f = -1;
                    for (int t = 0; t < 4; t++)
                        if (v[t]) { f = v[t]; break; }
                    if (f != 1) continue;               /* projective normalization */
                    if (typ == 0 && !isq[det]) continue; /* PSL: square determinant */
                    memcpy(gr->mat + 4 * G, v, sizeof v);
                    gr->idx[((a * p + b) * p + c) * p + e] = G;
                    G++;
                }
    free(isq);
    gr->G = G;
    gr->id = gr->idx[(p * p * p) + 1];   /* code of the identity (1,0,0,1) */
    return G;
}

static void free_group(Group *gr) {
    free(gr->mat);
    free(gr->idx);
    free(gr->inv_p);
    memset(gr, 0, sizeof *gr);
}

static void build_tables(const Group *gr) {
    int G = gr->G, p = gr->p;
    Rt = malloc(sizeof(uint16_t) * (size_t)G * (size_t)G);
    InvT = malloc(sizeof(int) * (size_t)G);
    for (int s = 0; s < G; s++) {
        for (int g = 0; g < G; g++)
            Rt[(size_t)s * G + g] = (uint16_t)gmul(gr, g, s);
        const int *A = gr->mat + 4 * s;
        InvT[s] = norm_idx(gr, A[3], (p - A[1]) % p, (p - A[2]) % p, A[0]);
    }
}

/* ---------- lift state ---------- */

static void set_block(int l, int i) {
    int j = SIG[l][i], s = VOL[l][i];
    const uint16_t *Rs = Rt + (size_t)s * GG;
    const uint16_t *Ri = Rt + (size_t)InvT[s] * GG;
    int bA = i * GG, bB = (KK + j) * GG;
    for (int g = 0; g < GG; g++)
        ADJ[(size_t)(bA + g) * dd + l] = bB + Rs[g];
    for (int h = 0; h < GG; h++)
        ADJ[(size_t)(bB + h) * dd + l] = bA + Ri[h];
}

/* True if (s, v) already occurs at block i in some layer t < lim with t != skip. */
static int conflict(int lim, int skip, int i, int s, int v) {
    for (int t = 0; t < lim; t++)
        if (t != skip && SIG[t][i] == s && VOL[t][i] == v) return 1;
    return 0;
}

static void random_init(void) {
    for (int l = 0; l < dd; l++) {
        int perm[MAXK];
        for (int i = 0; i < KK; i++) perm[i] = i;
        for (int i = KK - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[r];
            perm[r] = t;
        }
        for (int i = 0; i < KK; i++) SIG[l][i] = perm[i];
    }
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < KK; i++) {
            int v;
            do {
                v = rndint(GG);
            } while (conflict(l, -1, i, SIG[l][i], v));
            VOL[l][i] = v;
        }
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < KK; i++) set_block(l, i);
}

static void save_best(void) {
    memcpy(BSIG, SIG, sizeof SIG);
    memcpy(BVOL, VOL, sizeof VOL);
}

static void restore_best(void) {
    memcpy(SIG, BSIG, sizeof SIG);
    memcpy(VOL, BVOL, sizeof VOL);
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < KK; i++) set_block(l, i);
}

/* Number of (source, vertex) pairs at distance > D, over one source per block.
 * Left multiplication is an automorphism that is transitive on each block. */
static long evaluate(void) {
    long total = 0;
    for (int b = 0; b < 2 * KK; b++) {
        int src = b * GG + IDG;
        GEN++;
        if (GEN == 0) {
            memset(VIS, 0, sizeof(unsigned) * (size_t)NN);
            GEN = 1;
        }
        int head = 0, tail = 1;
        VIS[src] = GEN;
        QU[0] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                const int *nb = ADJ + (size_t)QU[head] * dd;
                for (int t = 0; t < dd; t++) {
                    int u = nb[t];
                    if (VIS[u] != GEN) {
                        VIS[u] = GEN;
                        QU[tail++] = u;
                    }
                }
            }
        }
        total += NN - tail;
    }
    return total;
}

static long step(long cost, double T) {
    if (KK >= 2 && rnd01() < 0.1) {
        int l = rndint(dd);
        int i1 = rndint(KK);
        int i2 = rndint(KK - 1);
        if (i2 >= i1) i2++;
        int s1 = SIG[l][i1], s2 = SIG[l][i2];
        if (conflict(dd, l, i1, s2, VOL[l][i1]) || conflict(dd, l, i2, s1, VOL[l][i2]))
            return cost;
        SIG[l][i1] = s2;
        SIG[l][i2] = s1;
        set_block(l, i1);
        set_block(l, i2);
        long c2 = evaluate();
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) return c2;
        SIG[l][i1] = s1;
        SIG[l][i2] = s2;
        set_block(l, i1);
        set_block(l, i2);
        return cost;
    }
    int l = rndint(dd), i = rndint(KK), g = rndint(GG);
    if (g == VOL[l][i]) return cost;
    if (conflict(dd, l, i, SIG[l][i], g)) return cost;
    int old = VOL[l][i];
    VOL[l][i] = g;
    set_block(l, i);
    long c2 = evaluate();
    if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) return c2;
    VOL[l][i] = old;
    set_block(l, i);
    return cost;
}

static void store_result(void) {
    int half = KK * GG;
    for (int v = 0; v < half; v++) {
        const int *nb = ADJ + (size_t)v * dd;
        for (int t = 0; t < dd; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (nb[t] == nb[t2]) return;   /* multi-edge: reject */
    }
    if (NN <= best_n) return;
    long m = 0;
    for (int v = 0; v < half; v++) {
        const int *nb = ADJ + (size_t)v * dd;
        for (int t = 0; t < dd; t++) {
            best_e[2 * m] = v;
            best_e[2 * m + 1] = nb[t];
            m++;
        }
    }
    best_n = NN;
    best_m = m;
}

static void run_config(int typ, int p, int k, double deadline) {
    if (p < 3 || k < 1 || k > MAXK) return;
    Group gr;
    int G = build_group(&gr, typ, p);
    if (G <= 0 || G > GMAX || 2 * k * G > MAXN || 2 * k * G <= best_n) {
        free_group(&gr);
        return;
    }
    GG = G;
    KK = k;
    NN = 2 * k * G;
    IDG = gr.id;
    build_tables(&gr);
    free_group(&gr);

    ADJ = malloc(sizeof(int) * (size_t)NN * dd);
    VIS = calloc((size_t)NN, sizeof(unsigned));
    QU = malloc(sizeof(int) * (size_t)NN);

    random_init();
    long cost = evaluate();
    long bestc = cost;
    save_best();
    int it = 0;
    const double T0 = 3.0, T1 = 0.2;
    while (cost > 0 && now() < deadline) {
        double T = T0 * pow(T1 / T0, (double)it / EPOCH);
        cost = step(cost, T);
        if (cost < bestc) {
            bestc = cost;
            save_best();
        }
        if (++it >= EPOCH) {
            it = 0;
            if (cost > bestc) {
                restore_best();
                cost = evaluate();
            }
        }
    }
    if (cost == 0) store_result();

    free(Rt);   Rt = NULL;
    free(InvT); InvT = NULL;
    free(ADJ);  ADJ = NULL;
    free(VIS);  VIS = NULL;
    free(QU);   QU = NULL;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    dd = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (argc >= 6) {
        const char *s = argv[5];
        while (*s && ncfg < MAXCFG) {
            int t, p, k, nr = 0;
            if (sscanf(s, "%d,%d,%d%n", &t, &p, &k, &nr) != 3 || nr <= 0) break;
            cfg_t[ncfg] = t;
            cfg_p[ncfg] = p;
            cfg_k[ncfg] = k;
            ncfg++;
            s += nr;
            if (*s == ';') s++;
        }
    }
    if (dd < 2 || dd > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double t_end = t0 + limit * 0.95 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    for (int ci = 0; ci < ncfg; ci++) {
        double left = t_end - now();
        if (left < 0.3) break;
        double slice = left / (ncfg - ci);
        run_config(cfg_t[ci], cfg_p[ci], cfg_k[ci], now() + slice);
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", best_n, best_m);
    for (long e = 0; e < best_m; e++)
        printf("%d %d\n", best_e[2 * e], best_e[2 * e + 1]);
    return 0;
}
'''


_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23)
_MAX_GROUP = 3600
_MAX_CONFIGS = 8


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_order(typ, p):
    """Order of PSL(2,p) (typ 0) or PGL(2,p) (typ 1)."""
    full = p * (p * p - 1)
    return full // 2 if typ == 0 else full


def _configs(d, D, best_n):
    """(type, p, k) lift configurations whose order lies in a useful band, smallest first."""
    moore = lib.moore_bound(d, D)
    lo = max(best_n + 1, int(0.2 * moore))
    hi = min(int(0.4 * moore), 20000)
    cands = []
    for p in _PRIMES:
        for typ in (0, 1):
            G = _group_order(typ, p)
            if G > _MAX_GROUP:
                continue
            for k in range(1, 7):
                n = 2 * k * G
                if lo <= n <= hi:
                    cands.append((n, typ, p, k))
    cands.sort()
    return [(t, p, k) for _, t, p, k in cands[:_MAX_CONFIGS]]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bi-Cayley lifts over PSL(2,p) / PGL(2,p), searched in one C run.
    configs = _configs(d, D, best_n) if d >= 2 else []
    budget = max(1.0, 0.8 * time_limit - 2.0)
    remaining = budget - (time.monotonic() - t0)
    if configs and remaining > 3.0:
        spec = ";".join(f"{t},{p},{k}" for t, p, k in configs)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), spec],
                             timeout=remaining + 5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
