"""Group-lift search over arbitrary finite groups (not just metacyclic ones).

Change from the parent: the C engine now reads multiplication tables of many
groups from stdin (cyclic, semidirect, permutation and matrix groups, and direct
products, all of order <= 480). Each annealing run picks a group and a base size
K in {1,2,3}, then anneals voltages (K-block lifts, A_g ~ B_{g s}) with breakout
weights and an elite pool. Groups are no longer restricted to the Z_m x| Z_k family.

Safety: Python baselines (projective plane, Araujo-Pardo-Lopez, W(q)) and K_{d,d}
are kept as fallbacks. Every C result goes through lib.is_valid before it is used.
"""
import itertools
import math
import random
import time

import lib


_MAXO = 480          # largest group order passed to the C engine
_BUDGET = 2_400_000  # total table entries (sum of order^2) sent on stdin

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define POOLMAX 32
#define POOLP 0.5
#define BRK 150
#define ITERS 5000
#define ILS_ITERS 2500
#define MAXK 3
#define NTRIES 200

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

static int DEG, DIAM, NG;
static int *gord;
static int **gtab;

/* current run state */
static int GI, O, K, T, N, curstamp;
static int *gt;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static long long *wt, *unc;
static long long wsum_w, last_w;

static int best_n, best_m;
static int *best_e = NULL;

typedef struct { int gi, k; long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * O;
    for (int g = 0; g < O; g++) pm[g] = gt[(size_t)g * O + s];
}

/* Layers: dart t = l*K + i has dI = i and dJ = a permutation of the K B-blocks per layer,
   so each A-vertex and each B-vertex has degree DEG. Returns the true cost (uncovered
   ordered pairs from the 2K block representatives). Sets unc[] and last_w. */
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
        int ai = dI[t] * O, bj = (K + dJ[t]) * O;
        const int *pm = perm + (size_t)t * O;
        for (int g = 0; g < O; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * O;
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

static void setup_run(int gi, int k) {
    GI = gi;
    O = gord[gi];
    gt = gtab[gi];
    K = k;
    T = DEG * K;
    N = 2 * K * O;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * O);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
    last_w = 0;
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

static void emit(void) {
    int m = T * O;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < O; g++) {
            best_e[idx++] = dI[t] * O + g;
            best_e[idx++] = (K + dJ[t]) * O + perm[(size_t)t * O + g];
        }
    best_m = m;
    best_n = N;
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
            dS[t] = rnd_int(O);
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
            dS[t] = rnd_int(O);
            build_perm(t);
        }
    }
}

/* Annealing on weighted cost with breakout weights. Caller must have just called
   eval_cost(). Best state (true cost) goes to bestJ/bestS. */
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
            int news = rnd_int(O);
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
        if (N > best_n) emit();
    }
}

static void pool_add(int gi, int k, long long cost, const int *J, const int *S) {
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
    c->gi = gi;
    c->k = k;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].k * gord[pool[i].gi];
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

/* Fresh group choice: prefer N = 2*K*O in (best_n, 4/3 best_n + 40]; otherwise any N > best_n. */
static int choose_fresh(int *gi_out, int *k_out) {
    static const int kc[5] = {1, 1, 2, 2, 3};
    long long hi = (long long)best_n + best_n / 3 + 40;
    for (int tr = 0; tr < NTRIES; tr++) {
        int k = kc[rnd_int(5)];
        int gi = rnd_int(NG);
        long long nn = 2LL * k * gord[gi];
        if (nn > best_n && nn <= hi) {
            *gi_out = gi;
            *k_out = k;
            return 1;
        }
    }
    int seen = 0;
    for (int gi = 0; gi < NG; gi++)
        for (int k = 1; k <= MAXK; k++) {
            long long nn = 2LL * k * gord[gi];
            if (nn > best_n) {
                seen++;
                if (rnd_int(seen) == 0) { *gi_out = gi; *k_out = k; }
            }
        }
    return seen > 0;
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

    /* Input: "n m" then 2m ints: flat stream [NG, (o, o*o table entries) ...]. */
    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) hm = 0;
    if (hm < 0) hm = 0;
    int *buf = malloc(sizeof(int) * (size_t)(2 * hm + 2));
    int got = 0;
    for (int i = 0; i < 2 * hm; i++) {
        if (scanf("%d", &buf[i]) != 1) break;
        got++;
    }
    NG = 0;
    if (got >= 1) {
        int ng = buf[0];
        if (ng < 0) ng = 0;
        gord = malloc(sizeof(int) * (size_t)(ng + 1));
        gtab = malloc(sizeof(int *) * (size_t)(ng + 1));
        int pos = 1;
        for (int g = 0; g < ng; g++) {
            if (pos >= got) break;
            int o = buf[pos++];
            if (o < 1 || (long long)pos + (long long)o * o > got) break;
            gtab[NG] = malloc(sizeof(int) * (size_t)o * (size_t)o);
            memcpy(gtab[NG], buf + pos, sizeof(int) * (size_t)o * (size_t)o);
            gord[NG] = o;
            NG++;
            pos += o * o;
        }
    }
    free(buf);
    if (NG == 0) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)(MAXK * DEG));
        pool[i].S = malloc(sizeof(int) * (size_t)(MAXK * DEG));
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search from an elite configuration. */
            Cfg *c = &pool[pi];
            int gi = c->gi, k = c->k;
            setup_run(gi, k);
            memcpy(dJ, c->J, sizeof(int) * (size_t)T);
            memcpy(dS, c->S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(gi, k, bc, bestJ, bestS);
            free_run();
            continue;
        }
        int gi, k;
        if (!choose_fresh(&gi, &k)) break;
        setup_run(gi, k);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(gi, k, bc, bestJ, bestS);
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
# Safe baseline families (unchanged from the parent).
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
# Finite groups as multiplication tables (lists of lists, element i = index).
# ----------------------------------------------------------------------------

def _perm_mul(p, q):
    """Composition of permutations given as tuples (associative)."""
    return tuple(q[i] for i in p)


def _mat2_mul(p):
    """Multiplication of 2x2 matrices mod p, stored as 4-tuples (a, b, c, d)."""
    def mul(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d * g) % p, (c * f + d * h) % p)
    return mul


def _closure(gens, mul, ident, cap):
    """Elements generated from ident by right multiplication; None if more than cap."""
    elems = [ident]
    idx = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in idx:
                    if len(elems) >= cap:
                        return None
                    idx[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems, idx


def _group_table(gens, mul, ident, cap=_MAXO):
    """Multiplication table of the group generated by gens, or None if its order exceeds cap."""
    res = _closure(gens, mul, ident, cap)
    if res is None:
        return None
    elems, idx = res
    return [[idx[mul(a, b)] for b in elems] for a in elems]


def _wr_gens(k, with_sym):
    """Generators of Z_2 wr Z_k (or Z_2 wr S_k when with_sym) as permutations of 2k points."""
    n = 2 * k
    a = tuple([1, 0] + list(range(2, n)))
    b = [0] * n
    for i in range(k):
        for s in (0, 1):
            b[2 * i + s] = 2 * ((i + 1) % k) + s
    gens = [a, tuple(b)]
    if with_sym:
        c = list(range(n))
        for s in (0, 1):
            c[s] = 2 + s
            c[2 + s] = s
        gens.append(tuple(c))
    return gens


def _base_tables():
    """Small non-abelian and mixed groups, each as a table (order <= _MAXO)."""
    def pg(n, gens):
        return _group_table(gens, _perm_mul, tuple(range(n)))

    out = [
        pg(3, [(1, 0, 2), (1, 2, 0)]),              # S3
        pg(4, [(1, 0, 2, 3), (1, 2, 3, 0)]),        # S4
        pg(4, [(1, 2, 0, 3), (1, 0, 3, 2)]),        # A4
    ]
    for n in (3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 20, 30):   # dihedral groups D_n
        out.append(pg(n, [tuple((i + 1) % n for i in range(n)),
                          tuple((-i) % n for i in range(n))]))
    for p, g in ((5, 2), (7, 3), (11, 2), (13, 2), (17, 3)):  # AGL(1, p)
        out.append(pg(p, [tuple((i + 1) % p for i in range(p)),
                          tuple((g * i) % p for i in range(p))]))
    for k in (2, 3, 4, 5):                          # Z_2 wr Z_k
        out.append(pg(2 * k, _wr_gens(k, False)))
    for k in (3, 4):                                # Z_2 wr S_k
        out.append(pg(2 * k, _wr_gens(k, True)))
    I2 = (1, 0, 0, 1)
    m3, m5 = _mat2_mul(3), _mat2_mul(5)
    out.append(_group_table([(1, 1, 0, 1), (0, 2, 1, 0)], m3, I2))          # SL(2,3)
    out.append(_group_table([(1, 1, 0, 1), (0, 1, 1, 0), (2, 0, 0, 1)], m3, I2))  # GL(2,3)
    out.append(_group_table([(1, 1, 0, 1), (0, 4, 1, 0)], m5, I2))          # SL(2,5)
    out.append(_group_table([(1, 1, 0, 1), (0, 1, 1, 0), (2, 0, 0, 1)], m5, I2))  # GL(2,5)
    return [t for t in out if t is not None]


def _cyclic(m):
    """Cyclic group Z_m as a table."""
    return [[(a + b) % m for b in range(m)] for a in range(m)]


def _direct(A, B):
    """Direct product of two tables; element (a, b) has index a*len(B) + b."""
    oa, ob = len(A), len(B)
    return [[A[a1][a2] * ob + B[b1][b2] for a2 in range(oa) for b2 in range(ob)]
            for a1 in range(oa) for b1 in range(ob)]


def _semidirect_table(m, k, r):
    """Table of Z_m x|_r Z_k from lib (identity at index 0)."""
    o, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(a, b) for b in range(o)] for a in range(o)]


def _make_groups(seed, gtime):
    """Collect group tables within the entry budget and the time budget."""
    t0 = time.monotonic()
    rng = random.Random(1000003 * seed + 17)
    base = _base_tables()
    specs = [(len(t), (lambda t=t: t)) for t in base]

    # Metacyclic semidirect products Z_m x|_r Z_k, biased to orders 100..480.
    made, tries = 0, 0
    while made < 60 and tries < 3000:
        tries += 1
        o = rng.randint(100, _MAXO)
        ks = [k for k in range(1, 9) if o % k == 0]
        k = rng.choice(ks)
        m = o // k
        if m < 2:
            continue
        r = 1 if (k == 1 or m == 2) else rng.randint(2, m - 1)
        if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
            continue
        specs.append((o, (lambda m=m, k=k, r=r: _semidirect_table(m, k, r))))
        made += 1

    # Direct products of base groups, and base groups times cyclic groups.
    for _ in range(150):
        X = rng.choice(base)
        if rng.random() < 0.5:
            Y = rng.choice(base)
            o = len(X) * len(Y)
            if o > _MAXO or o < 12:
                continue
            specs.append((o, (lambda X=X, Y=Y: _direct(X, Y))))
        else:
            m = rng.randint(2, _MAXO)
            o = len(X) * m
            if o > _MAXO or o < 12:
                continue
            specs.append((o, (lambda X=X, m=m: _direct(X, _cyclic(m)))))

    rng.shuffle(specs)
    tables = []
    total = 0
    for o, th in specs:
        if time.monotonic() - t0 > gtime or len(tables) >= 80:
            break
        if total + o * o > _BUDGET:
            continue
        tab = th()
        if tab is None:
            continue
        tables.append(tab)
        total += o * o
    return tables


def _pack(tables):
    """Flat integer stream [NG, o1, table1..., o2, table2...] as (u, v) pairs for lib.run_c."""
    flat = [len(tables)]
    for tab in tables:
        flat.append(len(tab))
        for row in tab:
            flat.extend(row)
    if len(flat) % 2:
        flat.append(0)
    return list(zip(flat[0::2], flat[1::2]))


# ----------------------------------------------------------------------------
# Driver
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

    # Build group tables (time-guarded), then give C the rest of the budget.
    try:
        gtime = min(7.0, 0.12 * time_limit)
        tables = _make_groups(seed, gtime)
    except Exception:
        tables = []

    if tables:
        elapsed = time.monotonic() - start
        remaining = min(0.88 * time_limit - elapsed - 1.0, time_limit - elapsed - 6.0)
        if remaining >= 2.0:
            try:
                pairs = _pack(tables)
                hard = min(remaining + 3.0, time_limit - elapsed - 3.0)
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                                stdin_graph=(0, pairs), timeout=hard)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
