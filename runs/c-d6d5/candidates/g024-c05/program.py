"""Group-table voltage lifts with breakout annealing, ILS and a catalogue of non-abelian groups.

Bold change: instead of only metacyclic groups Z_m x| Z_k, the search now draws from a
catalogue of groups given as multiplication tables: metacyclic groups, cyclic groups,
the permutation groups S4, A5, S5, PSL(2,7) and PGL(2,7), and their direct products
with cyclic groups. The C engine works on any table (lift darts are right multiplications,
and left-multiplication automorphisms make BFS from one vertex per block exact). Python
validates every returned graph with lib.is_valid, so a wrong table or a C failure falls
back to the best construction found so far.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine. stdin carries groups as edge pairs: header "n m" then m pairs whose
# flattened integers are: ngroups, then for each group: order, order*order table
# entries (table[x*order+y] = x*y). Dart t = (i, j, s) joins A_{i,g} to
# B_{j,g*s} for all g. Each layer is a permutation, so every vertex has degree DEG.
# Vertex ids: A_{i,g} = i*G + g, B_{j,h} = (K+j)*G + h.
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
#define MAXK 3
#define MAXGRP 64
#define MAXORD 1200
#define NCAP 4000

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
static int ng = 0;
static int gord[MAXGRP];
static int *gtab[MAXGRP];

static int CG, GG, K, T, N;
static int *MT;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static int curstamp;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

typedef struct { int g, k; long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

static int read_groups(void) {
    int hdr = 0, m = 0;
    if (scanf("%d %d", &hdr, &m) != 2 || m <= 0) return 0;
    (void)hdr;
    size_t total = 2 * (size_t)m;
    int *buf = malloc(sizeof(int) * total);
    if (!buf) return 0;
    size_t avail = 0;
    while (avail < total && scanf("%d", &buf[avail]) == 1) avail++;
    if (avail == 0) { free(buf); return 0; }
    size_t pos = 0;
    int want = buf[pos++];
    int got = 0;
    for (int gi = 0; gi < want && gi < MAXGRP; gi++) {
        if (pos >= avail) break;
        int o = buf[pos++];
        if (o < 1 || o > MAXORD) break;
        size_t sz = (size_t)o * (size_t)o;
        if (pos + sz > avail) break;
        int bad = 0;
        for (size_t q = 0; q < sz; q++)
            if (buf[pos + q] < 0 || buf[pos + q] >= o) { bad = 1; break; }
        if (bad) break;
        gtab[got] = malloc(sizeof(int) * sz);
        memcpy(gtab[got], buf + pos, sizeof(int) * sz);
        gord[got] = o;
        got++;
        pos += sz;
    }
    free(buf);
    ng = got;
    return ng > 0;
}

static void build_perm(int t) {
    const int s = dS[t];
    int *pm = perm + (size_t)t * GG;
    for (int g = 0; g < GG; g++) pm[g] = MT[g * GG + s];
}

/* Returns the true cost (sum of uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * GG, bj = (K + dJ[t]) * GG;
        const int *pm = perm + (size_t)t * GG;
        for (int g = 0; g < GG; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * GG;
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

static void setup_run(int gi, int k) {
    CG = gi; GG = gord[gi]; MT = gtab[gi]; K = k;
    T = DEG * K;
    N = 2 * K * GG;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * GG);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int r = 0; r < 2 * K; r++) wt[r] = 1;
    wsum_w = 2 * K;
    last_w = 0;
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
            dS[t] = rnd_int(GG);
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
            dS[t] = rnd_int(GG);
            build_perm(t);
        }
    }
}

/* Annealing on the weighted cost with breakout weight bumps. Best state by true cost
   goes to bestJ/bestS. Caller must have just called eval_cost(). */
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
            int news = rnd_int(GG);
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
    int m = T * GG;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < GG; g++) {
            best_e[idx++] = dI[t] * GG + g;
            best_e[idx++] = (K + dJ[t]) * GG + perm[(size_t)t * GG + g];
        }
    best_m = m;
    best_n = N;
}

static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (N > best_n) emit();
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
    c->g = CG; c->k = K; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].k * gord[pool[i].g];
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

/* Fresh start: prefer (group, K) pairs whose order already beats the best found. */
static void pick_fresh(int *gi_out, int *k_out) {
    static int cg[MAXGRP * MAXK];
    static int ck[MAXGRP * MAXK];
    int nc = 0;
    for (int pass = 0; pass < 2 && nc == 0; pass++) {
        for (int gi = 0; gi < ng; gi++)
            for (int k = 1; k <= MAXK; k++) {
                long long nn = 2LL * k * gord[gi];
                if (pass == 0 && nn <= best_n) continue;
                if (nn > NCAP) continue;
                cg[nc] = gi;
                ck[nc] = k;
                nc++;
            }
    }
    if (nc == 0) { *gi_out = 0; *k_out = 1; return; }
    int idx = rnd_int(nc);
    *gi_out = cg[idx];
    *k_out = ck[idx];
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n] < groups\n");
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
    int MAXT = 3 * DEG;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
        pool[i].g = 0;
        pool[i].k = 1;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (!read_groups()) {
        printf("0 0\n");
        return 0;
    }

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search from an elite configuration. */
            int pg = pool[pi].g, pk = pool[pi].k;
            setup_run(pg, pk);
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)T);
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
        int gi = 0, k = 1;
        pick_fresh(&gi, &k);
        setup_run(gi, k);
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
# Baseline constructions (safe fallbacks).
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
# Group catalogue: multiplication tables (numpy int64, shape (order, order)).
# ----------------------------------------------------------------------------

def _perm_group_table(gens, cap=400):
    """Multiplication table of the permutation group generated by gens (None if larger than cap)."""
    n = len(gens[0])
    ident = tuple(range(n))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[i] for i in x)
                if y not in index:
                    if len(elems) >= cap:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    m = len(elems)
    T = np.empty((m, m), dtype=np.int64)
    for i, a in enumerate(elems):
        for j, b in enumerate(elems):
            T[i, j] = index[tuple(a[k] for k in b)]
    return T


def _base_gens():
    """Generators of a few small non-abelian groups as permutations."""
    inf = 7
    t = tuple((x + 1) % 7 if x < 7 else inf for x in range(8))
    s2 = tuple((2 * x) % 7 if x < 7 else inf for x in range(8))
    s3 = tuple((3 * x) % 7 if x < 7 else inf for x in range(8))
    u = tuple(0 if x == 7 else (7 if x == 0 else (-pow(x, -1, 7)) % 7) for x in range(8))
    return {
        "S4": [(1, 0, 2, 3), (1, 2, 3, 0)],
        "A5": [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)],
        "S5": [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)],
        "PSL27": [t, s2, u],
        "PGL27": [t, s3, u],
    }


def _base_tables():
    out = {}
    for name, gens in _base_gens().items():
        T = _perm_group_table(gens, cap=400)
        if T is not None:
            out[name] = T
    return out


def _cyclic_table(n):
    idx = np.arange(n)
    return (idx[:, None] + idx[None, :]) % n


def _times_cyclic(T, c):
    """Direct product of a table with Z_c."""
    if c == 1:
        return T
    n = T.shape[0]
    Ca = (np.arange(c)[:, None] + np.arange(c)[None, :]) % c
    return (T[:, None, :, None] * c + Ca[None, :, None, :]).reshape(n * c, n * c)


def _semidirect_table(m, k, r):
    order, mul, _ = lib.semidirect_group(m, k, r)
    T = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        row = T[x]
        for y in range(order):
            row[y] = mul(x, y)
    return T


def _pick_groups(best_n, rng, budget=900_000, max_groups=8):
    """Choose a few groups whose order may beat best_n (K <= 3 means order >= best_n / 6)."""
    lo = max(8, best_n // 6 + 1)
    hi = 700
    bases = _base_tables()

    nonab = []
    for name, T in bases.items():
        o = T.shape[0]
        for c in range(1, hi // o + 1):
            if lo <= o * c <= hi:
                nonab.append(("prod", name, c, o * c))
    rng.shuffle(nonab)

    semi = []
    for _ in range(300):
        k = rng.randint(2, 12)
        m_lo = max(2, -(-lo // k))
        m_hi = hi // k
        if m_hi < m_lo:
            continue
        m = rng.randint(m_lo, m_hi)
        rs_ = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs_:
            continue
        r = rng.choice(rs_)
        semi.append(("semi", m, k, r, m * k))
    for _ in range(4):
        n = rng.randint(lo, hi)
        semi.append(("cyc", n, 0, 0, n))
    rng.shuffle(semi)

    order = nonab[:3] + semi[:4] + nonab[3:] + semi[4:]
    chosen = []
    used = 0
    for spec in order:
        if len(chosen) >= max_groups:
            break
        o = spec[-1]
        if used + o * o > budget:
            continue
        if spec[0] == "prod":
            T = _times_cyclic(bases[spec[1]], spec[2])
        elif spec[0] == "semi":
            T = _semidirect_table(spec[1], spec[2], spec[3])
        else:
            T = _cyclic_table(spec[1])
        chosen.append((o, T))
        used += o * o
    return chosen


def _payload(groups):
    """Encode groups as an (n, edges) pair that lib.run_c writes as "n m" plus m pairs."""
    flat = [len(groups)]
    for o, T in groups:
        flat.append(int(o))
        flat.extend(T.reshape(-1).tolist())
    if len(flat) % 2:
        flat.append(0)
    return (1, [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)])


# ----------------------------------------------------------------------------
# Driver.
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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    rng = random.Random(seed * 1000003 + d * 1009 + D)
    try:
        groups = _pick_groups(best_n, rng)
    except Exception:
        groups = []

    if groups:
        payload = _payload(groups)
        # Margin covers process start, the cached compile, parsing and validation.
        remaining = 0.9 * time_limit - (time.monotonic() - start) - 3.0
        if remaining >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                                stdin_graph=payload, timeout=remaining + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
