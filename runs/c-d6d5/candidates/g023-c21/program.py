import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New construction family: bi-Cayley (voltage) lifts over FINITE GROUPS given
# by their multiplication tables. The groups are chosen so that the family is
# different from the earlier semidirect-only search:
#   * affine Frobenius groups F_q x| H, H a subgroup of GF(q)^* (q a prime
#     power, so the translation group is elementary abelian, not cyclic),
#   * semidirect products Z_m x| Z_k and cyclic groups (kept for coverage).
#
# Graph: base has K vertices on each side. Vertices A_i,x = i*G + x and
# B_j,y = (K+j)*G + y. Dart t = (i, j, s) joins A_i,x to B_j,x*s for all x.
# Each layer l gives every A vertex one dart and every B vertex one dart
# (its target map over i is a permutation), so the graph is DEG-regular and
# bipartite. Left multiplication is an automorphism for any group, so the
# diameter is <= D iff a BFS of depth D from each of the 2K block
# representatives reaches everything.
#
# Search: simulated annealing on the number of uncovered ordered pairs, with
# breakout weights, plus an elite pool (iterated local search). Each restart
# picks a (group, K) pair whose order is near the target.
#
# Input stream (via lib.run_c's edge-list slot): header "NG m", then for each
# group "G" followed by G*G mul-table entries row-major (identity not needed).
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
#define POOLP 0.6
#define BRK 150
#define MAXKK 3
#define MAXNG 32

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

static int DEG, DIAM, NG, MOORE, AIM, BESTN, BESTM;
static int *gord = NULL;
static int **gmt = NULL;
static double DEADLINE;

static int G, K, T, N, CG;
static const int *MT = NULL;
static int *dI = NULL, *dJ = NULL, *dS = NULL, *perm = NULL, *adj = NULL, *cnt = NULL;
static int *stamp = NULL, *fr = NULL, *nx = NULL, *bestJ = NULL, *bestS = NULL;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;
static int curstamp = 0;
static int *best_e = NULL;

typedef struct { int g, k; long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * (size_t)G;
    for (int g = 0; g < G; g++) pm[g] = MT[(size_t)g * G + s];
}

/* Returns the true cost (uncovered ordered pairs over block reps).
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
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * (size_t)G;
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

static void setup(int g, int k) {
    CG = g;
    G = gord[g];
    K = k;
    MT = gmt[g];
    T = DEG * K;
    N = 2 * K * G;
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
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
    curstamp = 0;
}

static void free_cfg(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = NULL;
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
    BESTM = m;
    BESTN = 2 * K * G;
}

static void random_init(void) {
    int p[MAXKK];
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

static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (2 * K * G > BESTN) emit();
}

static void pool_add(int g, int k, long long cost, const int *J, const int *S, int tt) {
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
    c->g = g;
    c->k = k;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)tt);
    memcpy(c->S, S, sizeof(int) * (size_t)tt);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].k * gord[pool[i].g];
        if (nn > BESTN) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* Fresh (group, K) choice: count must beat BESTN and stay within MOORE.
   Prefer counts inside a window around AIM. Returns 0 if none exist. */
static int pick_fresh(int *og, int *ok) {
    static int pg[128], pk[128], cw[128];
    int np = 0, nw = 0;
    int wlo = AIM - AIM / 8, whi = AIM + AIM / 8 + 4;
    for (int g = 0; g < NG; g++)
        for (int k = 1; k <= MAXKK; k++) {
            long long n2 = 2LL * k * gord[g];
            if (n2 <= BESTN || n2 > MOORE) continue;
            if (np >= 128) break;
            pg[np] = g;
            pk[np] = k;
            if (n2 >= wlo && n2 <= whi) cw[nw++] = np;
            np++;
        }
    if (np == 0) return 0;
    int i = nw > 0 ? cw[rnd_int(nw)] : rnd_int(np);
    *og = pg[i];
    *ok = pk[i];
    return 1;
}

static int read_groups(int ng) {
    gord = malloc(sizeof(int) * (size_t)ng);
    gmt = malloc(sizeof(int *) * (size_t)ng);
    int got = 0;
    for (int g = 0; g < ng; g++) {
        int go = 0;
        if (scanf("%d", &go) != 1 || go < 1 || go > 4000) break;
        gmt[g] = malloc(sizeof(int) * (size_t)go * (size_t)go);
        int bad = 0;
        for (long long i = 0; i < (long long)go * go; i++)
            if (scanf("%d", &gmt[g][i]) != 1) { bad = 1; break; }
        if (bad) { free(gmt[g]); break; }
        gord[g] = go;
        got++;
    }
    return got;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: prog d D seed time start_n aim moore\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    BESTN = atoi(argv[5]);
    AIM = atoi(argv[6]);
    MOORE = atoi(argv[7]);
    BESTM = 0;
    best_e = NULL;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int ng0 = 0, mtok = 0;
    if (scanf("%d %d", &ng0, &mtok) != 2 || ng0 < 1) {
        printf("0 0\n");
        return 0;
    }
    if (ng0 > MAXNG) ng0 = MAXNG;
    NG = read_groups(ng0);

    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)DEG * MAXKK);
        pool[i].S = malloc(sizeof(int) * (size_t)DEG * MAXKK);
        pool[i].cost = BIGC;
        pool[i].g = 0;
        pool[i].k = 1;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (NG > 0 && elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search from an elite configuration. */
            int cg_ = pool[pi].g, ck_ = pool[pi].k;
            int tt = DEG * ck_;
            setup(cg_, ck_);
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)tt);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)tt);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(cg_, ck_, bc, bestJ, bestS, tt);
            free_cfg();
            continue;
        }
        int g = 0, k = 1;
        if (!pick_fresh(&g, &k)) break;
        setup(g, k);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(g, k, bc, bestJ, bestS, T);
        free_cfg();
    }

    if (BESTM > 0 && best_e != NULL) {
        printf("%d %d\n", BESTN, BESTM);
        for (int i = 0; i < BESTM; i++)
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

RECORDS = {(6, 5): 684}   # known record orders used only to aim the search
MAX_CELLS = 1_200_000     # cap on total mul-table entries sent to C
_FIELDS = {}


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
# Group tables (numpy). Each returns a G x G table with entry [x, y] = x*y.
# ----------------------------------------------------------------------------

def _field(q):
    if q not in _FIELDS:
        _FIELDS[q] = lib.GF(q)
    return _FIELDS[q]


def _divisors(n):
    return [h for h in range(1, n + 1) if n % h == 0]


def _affine_table(q, h):
    """Frobenius group F_q x| H: elements (a, b) mean z -> a z + b, a in H (order h).
    Product (a, b)(c, e) = (a c, a e + b). Index = aidx * q + b."""
    F = _field(q)
    g = F.primitive_element()
    step = (q - 1) // h
    H = np.array([F.pow(g, i * step) for i in range(h)], dtype=np.int64)
    lut = np.full(q, -1, dtype=np.int64)
    lut[H] = np.arange(h, dtype=np.int64)
    A = lut[F.mul_table[H[:, None], H[None, :]]]              # (h, h): index of a*c
    AE = F.mul_table[H[:, None], np.arange(q)[None, :]]       # (h, q): a*e
    Y = F.add_table[AE[:, None, :], np.arange(q)[None, :, None]]  # (h, q, q): [ai, b, e] = a*e + b
    T4 = A[:, None, :, None] * q + Y[:, :, None, :]           # (h, q, h, q)
    return T4.reshape(h * q, h * q).astype(np.int64)


def _semi_table(m, k, r):
    """Z_m x| Z_k: (a, b)(c, e) = (a + r^b c, b + e), index a*k + b."""
    Rp = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(m * k, dtype=np.int64)
    a, b = x // k, x % k
    ra = (a[:, None] + Rp[b][:, None] * a[None, :]) % m
    rb = (b[:, None] + b[None, :]) % k
    return (ra * k + rb).astype(np.int64)


def _score(G, best_n, aim):
    """Distance from aim of the best usable vertex count 2*K*G (K = 1..3) that beats best_n."""
    vals = [2 * k * G for k in (1, 2, 3) if 2 * k * G > best_n]
    if not vals:
        return None
    return min(abs(v - aim) for v in vals)


def _tables(best_n, aim, moore):
    """Pick a diverse set of groups and return their mul tables (affine groups first)."""
    lo = max(2, best_n // 6)
    hi = moore // 2
    if hi < lo:
        return []
    aff, semi = [], []
    for q in range(2, min(hi, 400) + 1):
        if not lib.is_prime_power(q):
            continue
        for h in _divisors(q - 1):
            G = q * h
            if lo <= G <= hi:
                s = _score(G, best_n, aim)
                if s is not None:
                    aff.append((s, ("aff", q, h), G))
    for k in range(1, 13):
        for m in range(2, hi // k + 1):
            G = m * k
            if G < lo:
                continue
            s = _score(G, best_n, aim)
            if s is None:
                continue
            rs = [1]
            if k > 1:
                for r in range(2, min(m, 80)):
                    if len(rs) >= 3:
                        break
                    if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                        rs.append(r)
            for r in rs:
                semi.append((s, ("semi", m, k, r), G))
    aff.sort(key=lambda t: t[0])
    semi.sort(key=lambda t: t[0])
    chosen = aff[:7] + semi[:5]
    tables, cells = [], 0
    for _, spec, G in chosen:
        if cells + G * G > MAX_CELLS:
            continue
        if spec[0] == "aff":
            tbl = _affine_table(spec[1], spec[2])
        else:
            tbl = _semi_table(spec[1], spec[2], spec[3])
        tables.append(tbl)
        cells += G * G
    return tables


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D                      # even cycle: diameter D, Moore bound for d = 2
        return n, [(i, (i + 1) % n) for i in range(n)]

    moore = lib.moore_bound(d, D)
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

    if best_n >= moore:
        return best

    aim = max(RECORDS.get((d, D), 0), best_n + 2)
    try:
        tables = _tables(best_n, aim, moore)
    except Exception:
        tables = []

    remaining = 0.88 * time_limit - (time.monotonic() - start) - 2.0
    if tables and remaining >= 3.0:
        # Pack the group tables into the edge-list slot: header "NG m" and then
        # the flat integer stream [G1, table1..., G2, table2..., ...].
        flat = []
        for tbl in tables:
            flat.append(int(tbl.shape[0]))
            flat.extend(tbl.ravel().tolist())
        if len(flat) % 2:
            flat.append(0)
        pairs = list(zip(flat[0::2], flat[1::2]))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n, aim, moore],
                            stdin_graph=(len(tables), pairs),
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
