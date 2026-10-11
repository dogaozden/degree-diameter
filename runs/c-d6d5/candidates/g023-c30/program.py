import itertools
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over two kinds of groups.
#   type 0: metacyclic Z_m x| Z_k2 (computed by formula, as in the parent).
#   type 1: arbitrary finite groups given as Cayley tables (sent by Python).
# Base: K A-blocks and K B-blocks. Vertices A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h.
# Dart t = (i, j, s) joins A_{i,g} to B_{j,g*s} for all g. Each layer is a
# permutation, so every vertex has degree DEG. Left multiplication is an
# automorphism, so diameter <= D iff BFS of depth D from each of the 2K block
# representatives (the identity of each block) covers all vertices.
# Search: simulated annealing on the weighted uncovered-pair count with breakout
# weights, plus an elite pool with iterated local search.
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
#define POOLP 0.5
#define TABP 0.6
#define BRK 150
#define KMAX 4
#define MAXTAB 32

typedef struct { int type, G, M, K2, R, tab; } Grp;
typedef struct { Grp g; int K; long long cost; int *J, *S; } Cfg;

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;
static long long NCAP;
static int best_n, best_m;
static int *best_e = NULL;
static int MAXT = 0;

static int ntab = 0;
static int tabG[MAXTAB];
static int *tabdat[MAXTAB];

static Grp cg;
static int G, K, T, M, K2, R;
static int *Rpow = NULL;
static int *dI = NULL, *dJ = NULL, *dS = NULL, *bestJ = NULL, *bestS = NULL;
static int *perm = NULL, *adj = NULL, *cnt = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;
static int curstamp = 0;
static Cfg pool[POOLMAX];
static int npool = 0;

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

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group multiplication: metacyclic formula (type 0) or Cayley table (type 1). */
static inline int gmul(int x, int y) {
    if (cg.type == 0) {
        int a = x / K2, b = x % K2;
        int c = y / K2, e = y % K2;
        int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
        int rb = (b + e) % K2;
        return ra * K2 + rb;
    }
    return tabdat[cg.tab][(size_t)x * G + y];
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void set_group(Grp g) {
    cg = g;
    G = g.G; M = g.M; K2 = g.K2; R = g.R;
    free(Rpow);
    Rpow = malloc(sizeof(int) * (size_t)(K2 > 0 ? K2 : 1));
    Rpow[0] = (g.type == 0) ? 1 % M : 0;
    if (g.type == 0)
        for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = NULL;
    perm = adj = NULL;
    cnt = stamp = fr = nx = NULL;
    wt = unc = NULL;
}

static void begin(Grp g, int k) {
    set_group(g);
    K = k;
    T = DEG * K;
    int N = 2 * K * G;
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
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void end_config(void) { free_config(); }

/* Returns the sum of uncovered ordered pairs over block representatives.
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
        total += unc[r];
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void random_init(void) {
    int p[KMAX];
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

/* Random kicks that keep every layer a permutation. */
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

/* Annealing on the weighted cost with breakout weight bumps.
   Caller must have just called eval_cost(). Best state by true cost goes to bestJ/bestS. */
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
        if (2LL * K * G > best_n) emit();
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
    c->g = cg;
    c->K = K;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

/* Pick an elite entry whose group order still beats the best (best of 3 samples). */
static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].g.G;
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

/* Input: "n m" then m pairs (2m integers). Integers: NG, then per group G and G*G table entries. */
static void read_tables(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || m0 <= 0) return;
    size_t cap = 2 * (size_t)m0;
    int *L = malloc(sizeof(int) * cap);
    size_t nl;
    for (nl = 0; nl < cap; nl++)
        if (scanf("%d", &L[nl]) != 1) break;
    if (nl == 0) { free(L); return; }
    int NG = L[0];
    size_t idx = 1;
    for (int gi = 0; gi < NG && ntab < MAXTAB; gi++) {
        if (idx >= nl) break;
        int g = L[idx++];
        if (g <= 0 || idx + (size_t)g * g > nl) break;
        int *tb = malloc(sizeof(int) * (size_t)g * g);
        memcpy(tb, L + idx, sizeof(int) * (size_t)g * g);
        tabdat[ntab] = tb;
        tabG[ntab] = g;
        ntab++;
        idx += (size_t)g * g;
    }
    free(L);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n ncap]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    NCAP = argc > 6 ? atoll(argv[6]) : 1000000000LL;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MAXT = DEG * KMAX;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
        pool[i].K = 0;
    }
    read_tables();
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg c = pool[pi];
            begin(c.g, c.K);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            end_config();
            continue;
        }

        /* Feasible (table group, K) pairs: group order K*G must give a graph beating best_n. */
        int fti[MAXTAB * KMAX], fk[MAXTAB * KMAX], nf = 0;
        for (int ti = 0; ti < ntab; ti++)
            for (int k = 1; k <= KMAX; k++) {
                long long nn = 2LL * k * tabG[ti];
                if (nn > best_n && nn <= NCAP) {
                    fti[nf] = ti;
                    fk[nf] = k;
                    nf++;
                }
            }

        if (nf > 0 && rnd_unit() < TABP) {
            int pick = rnd_int(nf);
            Grp g = {1, tabG[fti[pick]], 0, 1, 0, fti[pick]};
            begin(g, fk[pick]);
            random_init();
            long long cost = eval_cost();
            long long bc = run_sa(ITERS, 1.0, cost);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            end_config();
            continue;
        }

        /* Fresh random metacyclic lift over a group of order near the best. */
        int k = kc[rnd_int(5)];
        long long gmin = best_n / (2 * k) + 1;
        long long spread = gmin / 6 + 2;
        long long gg_ord = gmin + rnd_int((int)spread);
        if (gg_ord < 2) gg_ord = 2;
        int opts[12], no = 0;
        for (int c = 1; c <= 12; c++)
            if (gg_ord % c == 0 && gg_ord / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = (int)(gg_ord / c2), r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                c2 = 1;
                m = (int)gg_ord;
                r = 1;
            }
        }
        Grp mg = {0, m * c2, m, c2, r, -1};
        begin(mg, k);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
        end_config();
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

KMAX = 4                       # must match KMAX in C_SOURCE
MAX_TABLE_ENTRIES = 1_300_000  # total Cayley-table entries sent to C


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
# Finite groups as permutation groups, converted to Cayley tables for C.
# ----------------------------------------------------------------------------

def _prim_root(p):
    """A primitive root modulo the prime p."""
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = x * g % p
            seen.add(x)
        if len(seen) == p - 1:
            return g
    return 1


def _psl_gens(p, pgl):
    """Generators of PSL(2,p) (or PGL(2,p)) on the p+1 points of the projective line; infinity = p."""
    g = _prim_root(p)
    s = g * g % p
    inf = p
    tr = [(i + 1) % p for i in range(p)] + [inf]

    def scale(a):
        return [a * i % p for i in range(p)] + [inf]

    inv = [inf] + [(-pow(i, p - 2, p)) % p for i in range(1, p)] + [0]
    return [tr, scale(g if pgl else s), inv]


def _agl1_gens(p):
    """Generators of AGL(1,p) acting on p points."""
    g = _prim_root(p)
    return [[(i + 1) % p for i in range(p)], [g * i % p for i in range(p)]]


def _psl28_gens():
    """Generators of PSL(2,8) = PGL(2,8) on the 9 points of the projective line over GF(8)."""
    F = lib.GF(8)
    w = F.primitive_element()
    inf = 8
    tr = [F.add(i, 1) for i in range(8)] + [inf]
    sc = [F.mul(w, i) for i in range(8)] + [inf]
    inv = [inf] + [F.inv(i) for i in range(1, 8)] + [0]
    return [tr, sc, inv]


def _agl23_gens():
    """Generators of AGL(2,3) acting on the 9 points of Z_3^2 (index 3x+y)."""
    def perm(f):
        out = [0] * 9
        for x in range(3):
            for y in range(3):
                x2, y2 = f(x, y)
                out[3 * x + y] = 3 * (x2 % 3) + (y2 % 3)
        return tuple(out)

    fs = [lambda x, y: (x + 1, y),
          lambda x, y: (x, y + 1),
          lambda x, y: (x + y, y),
          lambda x, y: (y, x),
          lambda x, y: (2 * x, y)]
    return [perm(f) for f in fs]


# (name, builder returning (generators, number of points)).
_GROUP_SPECS = [
    ("A6", lambda: ([(1, 2, 0, 3, 4, 5), (0, 2, 3, 4, 5, 1)], 6)),
    ("PSL28", lambda: (_psl28_gens(), 9)),
    ("AGL23", lambda: (_agl23_gens(), 9)),
    ("PGL27", lambda: (_psl_gens(7, True), 8)),
    ("PSL211", lambda: (_psl_gens(11, False), 12)),
    ("AGL119", lambda: (_agl1_gens(19), 19)),
    ("S5", lambda: ([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)], 5)),
    ("PSL27", lambda: (_psl_gens(7, False), 8)),
    ("AGL123", lambda: (_agl1_gens(23), 23)),
]


def _closure(gens, npts, limit):
    """Elements of the group generated by gens (identity first), or None if more than limit."""
    gens = [tuple(g) for g in gens]
    ident = tuple(range(npts))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[v] for v in x)
                if y not in index:
                    if len(elems) >= limit:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems


def _cayley_table(elems):
    """Multiplication table tab[x, y] = index of x*y (composition), identity index 0; None on error."""
    G = len(elems)
    npts = len(elems[0])
    E = np.array(elems, dtype=np.int64)
    w = np.array([npts ** i for i in range(npts)], dtype=np.int64)
    codes = E @ w
    order = np.argsort(codes)
    sc = codes[order]
    tab = np.empty((G, G), dtype=np.int64)
    for x in range(G):
        comp = E[x][E]              # comp[y, i] = x(y(i))
        cc = comp @ w
        pos = np.minimum(np.searchsorted(sc, cc), G - 1)
        if not np.array_equal(sc[pos], cc):
            return None
        tab[x] = order[pos]
    return tab


def _group_tables(ncap, best_n):
    """Cayley tables of the named groups that can yield a graph with more than best_n vertices."""
    out, total = [], 0
    for _, spec in _GROUP_SPECS:
        gens, npts = spec()
        elems = _closure(gens, npts, ncap // 2 + 1)
        if elems is None:
            continue
        G = len(elems)
        if not any(best_n < 2 * k * G <= ncap for k in range(1, KMAX + 1)):
            continue
        if total + G * G > MAX_TABLE_ENTRIES:
            continue
        tab = _cayley_table(elems)
        if tab is None:
            continue
        out.append((G, tab))
        total += G * G
    return out


def _stream_pairs(groups):
    """Flatten [count, (G, table...)...] into pairs for the stdin graph slot."""
    vals = [len(groups)]
    for G, tab in groups:
        vals.append(G)
        vals.extend(tab.ravel().tolist())
    if len(vals) % 2:
        vals.append(0)
    return list(zip(vals[0::2], vals[1::2]))


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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    ncap = lib.moore_bound(d, D)
    if best_n >= ncap:
        return best

    try:
        groups = _group_tables(ncap, best_n)
    except Exception:
        groups = []
    pairs = _stream_pairs(groups)

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n, ncap],
                            stdin_graph=(0, pairs), timeout=remaining + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
