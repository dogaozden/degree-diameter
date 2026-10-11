import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an arbitrary finite group given by its
# multiplication table (passed in from Python). Groups include semidirect
# products Z_m x| Z_k and non-metacyclic groups such as SL(2,3) x Z_k,
# GL(2,3) x Z_k, SL(2,5) x Z_k, GL(2,5), SL(2,7), AGL(2,3).
#
# Base: K A-vertices and K B-vertices. Vertex A_i,g = i*G + g and
# B_j,h = (K+j)*G + h, with identity = index 0. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Layers (DEG of them, each a permutation i -> j)
# make every vertex have degree DEG. Left multiplication is an automorphism,
# so diameter <= D iff BFS of depth D from each of the 2K block
# representatives covers everything.
#
# Search: simulated annealing on the cost (uncovered ordered pairs) with
# breakout weights, plus iterated local search from an elite pool.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXGRP 64
#define MAXK 4
#define POOLMAX 40
#define POOLP 0.6
#define BRK 150
#define ITERS 6000
#define ILS_ITERS 3000

static struct timespec T0;
static double DEADLINE;
static uint64_t rs[2];

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

typedef struct { int G, K; int *MT; } Group;
static Group grp[MAXGRP];
static int NG = 0;

static int DEG, DIAM;
static int G, K, T, N, GI;
static int *MT;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static long long *wt, *unc;
static long long wsum_w, last_w;
static int best_n, best_m;
static int *best_e = NULL;

typedef struct { int gi, K, G; long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;
static int MAXT;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = MT[g * G + s];
}

static void setup_group(int gi) {
    GI = gi;
    G = grp[gi].G;
    K = grp[gi].K;
    MT = grp[gi].MT;
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * (size_t)G);
    adj = malloc(sizeof(int) * (size_t)N * (size_t)DEG);
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

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = NULL;
    wt = unc = NULL;
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
    for (int i = 0; i < N; i++) cnt[i] = 0;
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
        total += unc[r];
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
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
        }
    }
    for (int t = 0; t < T; t++) {
        int ok = 0;
        for (int tr = 0; tr < 1000 && !ok; tr++) {
            dS[t] = rnd_int(G);
            ok = 1;
            for (int u = 0; u < t; u++)
                if (dI[u] == dI[t] && dJ[u] == dJ[t] && dS[u] == dS[t]) { ok = 0; break; }
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
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

/* Annealing on the weighted cost with breakout weight bumps. */
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
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = 2 * K * G;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the best so far. */
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
    c->gi = GI; c->K = K; c->G = G; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (2LL * pool[i].K * pool[i].G > best_n) cand[nc++] = i;
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

static int pick_group(void) {
    int cand[MAXGRP], nc = 0;
    for (int g = 0; g < NG; g++)
        if (2LL * grp[g].K * grp[g].G > best_n) cand[nc++] = g;
    if (nc == 0) return -1;
    return cand[rnd_int(nc)];
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [best_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    best_e = NULL;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    MAXT = DEG * MAXK;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }

    /* Input: stdin is "n m" then m pairs; the pairs carry a flat integer stream:
       NG, then per group: G K and G*G table entries (row-major, identity = 0). */
    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) hm = 0;
    (void)hn;
    int nv = 2 * hm;
    int *vals = malloc(sizeof(int) * (size_t)(nv > 0 ? nv : 1));
    int got = 0;
    for (int i = 0; i < nv; i++) {
        if (scanf("%d", &vals[i]) != 1) break;
        got++;
    }
    int pos = 0;
    if (got > 0) {
        int want = vals[pos++];
        for (int g = 0; g < want && NG < MAXGRP; g++) {
            if (pos + 2 > got) break;
            int gg = vals[pos], kk = vals[pos + 1];
            pos += 2;
            if (gg < 2 || kk < 1 || kk > MAXK) break;
            long long need = (long long)gg * gg;
            if ((long long)pos + need > got) break;
            int ok = 1;
            for (long long i = 0; i < need; i++) {
                int v = vals[pos + i];
                if (v < 0 || v >= gg) { ok = 0; break; }
            }
            if (!ok) break;
            grp[NG].G = gg;
            grp[NG].K = kk;
            grp[NG].MT = malloc(sizeof(int) * (size_t)need);
            memcpy(grp[NG].MT, vals + pos, sizeof(int) * (size_t)need);
            NG++;
            pos += (int)need;
        }
    }
    free(vals);

    while (elapsed() < DEADLINE && NG > 0) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg c = pool[pi];
            setup_group(c.gi);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
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

        int gi = pick_group();
        if (gi < 0) break;
        setup_group(gi);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
        free_config();
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
# Group library in Python: multiplication tables with identity at index 0.
# ----------------------------------------------------------------------------

_BASE_ORDERS = {"SL23": 24, "GL23": 48, "SL25": 120, "GL25": 480, "SL27": 336, "AGL23": 432}
_BASE_CACHE = {}


def _table(elems, mul):
    """Flat row-major multiplication table of a list of elements (identity first)."""
    idx = {e: i for i, e in enumerate(elems)}
    return [idx[mul(x, y)] for x in elems for y in elems]


def _mat_group(p, special):
    """GL(2,p) or SL(2,p) as 4-tuples; identity first."""
    I = (1, 0, 0, 1)
    els = [I]
    for a, b, c, d in itertools.product(range(p), repeat=4):
        if (a, b, c, d) == I:
            continue
        det = (a * d - b * c) % p
        if det == 0 or (special and det != 1):
            continue
        els.append((a, b, c, d))

    def mul(x, y):
        return ((x[0] * y[0] + x[1] * y[2]) % p, (x[0] * y[1] + x[1] * y[3]) % p,
                (x[2] * y[0] + x[3] * y[2]) % p, (x[2] * y[1] + x[3] * y[3]) % p)

    return els, mul


def _affine2(p):
    """AGL(2,p) = F_p^2 x| GL(2,p) as 6-tuples (v0, v1, a, b, c, d); identity first."""
    lin, lmul = _mat_group(p, False)
    els = [(v0, v1) + M for M in lin for v0 in range(p) for v1 in range(p)]

    def mul(x, y):
        M = x[2:]
        N = y[2:]
        mw0 = (M[0] * y[0] + M[1] * y[1]) % p
        mw1 = (M[2] * y[0] + M[3] * y[1]) % p
        return ((x[0] + mw0) % p, (x[1] + mw1) % p) + lmul(M, N)

    return els, mul


def _base_table(name):
    """(order, flat table) of a base non-metacyclic group, cached."""
    if name not in _BASE_CACHE:
        if name == "SL23":
            els, mul = _mat_group(3, True)
        elif name == "GL23":
            els, mul = _mat_group(3, False)
        elif name == "SL25":
            els, mul = _mat_group(5, True)
        elif name == "GL25":
            els, mul = _mat_group(5, False)
        elif name == "SL27":
            els, mul = _mat_group(7, True)
        else:
            els, mul = _affine2(3)
        if len(els) != _BASE_ORDERS[name]:
            raise ValueError("unexpected group order")
        _BASE_CACHE[name] = (len(els), _table(els, mul))
    return _BASE_CACHE[name]


def _direct_table(base_flat, b, k):
    """Flat table of B x Z_k; element (x, i) has index x*k + i."""
    G = b * k
    out = [0] * (G * G)
    for x in range(b):
        for i in range(k):
            row = (x * k + i) * G
            for y in range(b):
                prod = base_flat[x * b + y] * k
                col = y * k
                for j in range(k):
                    out[row + col + j] = prod + (i + j) % k
    return out


def _sd_table(m, k, r):
    """Flat table of Z_m x| Z_k with action r (lib.semidirect_group)."""
    order, mul, _ = lib.semidirect_group(m, k, r)
    return order, [mul(x, y) for x in range(order) for y in range(order)]


def _candidates(lo, hi):
    """Group descriptors with order in [lo, hi]."""
    cands = []
    for name, b in _BASE_ORDERS.items():
        for k in range(1, hi // b + 1):
            if lo <= b * k <= hi:
                cands.append(("prod", name, k, b * k))
    for G in range(lo, hi + 1):
        for k in range(1, G + 1):
            if G % k:
                continue
            m = G // k
            if m < 2:
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cands.append(("sd", m, k, r, G))
    return cands


def _build(c):
    """(order, flat table) for a candidate descriptor."""
    if c[0] == "prod":
        _, name, k, G = c
        b, flat = _base_table(name)
        return G, _direct_table(flat, b, k)
    _, m, k, r, G = c
    return _sd_table(m, k, r)


def _pick_spread(cands, count, rng):
    """Pick about `count` candidates spread evenly over their orders."""
    if not cands:
        return []
    cands = sorted(cands, key=lambda c: (c[-1], rng.random()))
    n = len(cands)
    if n <= count:
        return cands
    idx = sorted({round(i * (n - 1) / (count - 1)) for i in range(count)})
    picks = [cands[i] for i in idx]
    prods = [c for c in cands if c[0] == "prod"]
    for c in rng.sample(prods, min(2, len(prods))):
        if c not in picks:
            picks.append(c)
    return picks


def _choose_groups(best_n, seed):
    """List of (K, G, flat table) for the C engine: K=1 and K=2 bases, spread over orders."""
    rng = random.Random(seed * 1000003 + 7)
    plan = ((1, best_n // 2 + 1, 500, 8), (2, best_n // 4 + 1, 250, 4))
    out = []
    for K, lo, hi, count in plan:
        lo = max(lo, 2)
        if hi < lo:
            continue
        cands = _candidates(lo, hi)
        for c in _pick_spread(cands, count, rng):
            G, flat = _build(c)
            if G * G <= 300000:
                out.append((K, G, flat))
    return out


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Driver: baselines, then the table-driven C search over non-metacyclic and
# semidirect groups.
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
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if best_n >= lib.moore_bound(d, D):
        return best

    groups = []
    if time_limit - (time.monotonic() - start) > 8.0:
        try:
            groups = _choose_groups(best_n, seed)
        except Exception:
            groups = []

    elapsed_now = time.monotonic() - start
    remaining = 0.85 * time_limit - elapsed_now - 2.0
    if groups and remaining >= 1.0:
        flat = [len(groups)]
        for K, G, table in groups:
            flat.append(G)
            flat.append(K)
            flat.extend(table)
        if len(flat) % 2:
            flat.append(0)
        pairs = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
        hard = min(remaining + 3.0, time_limit - elapsed_now - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            stdin_graph=(0, pairs), timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
