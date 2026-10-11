import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New family: voltage lifts over arbitrary finite groups given by their full
# multiplication tables. Groups are built in Python (PSL/SL(2,p), A_n, S_n,
# metacyclic Z_m x| Z_k, cyclic) and handed to the C annealer, which chooses
# the group and the base size K (1..3) by itself.
#
# Graph: vertices A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s)
# joins A_i,g to B_j,g*s for every g. Each of the DEG layers contributes one
# dart per base vertex, so every vertex has degree DEG. Left multiplication is
# an automorphism, so the diameter is <= D iff BFS of depth D from each of the
# 2K block representatives reaches everything.
#
# The C engine keeps the breakout-weighted annealing and the elite pool with
# iterated local search of the earlier version, now over several groups at once.
# Stdin carries the group count and then, per group, its order followed by its
# multiplication table (identity = element 0, table row-major).
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
#define POOLMAX 40
#define POOLP 0.6
#define BRK 150
#define KMAX 3
#define MAXGROUPS 64

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

static int G, K, T;
static int *TAB;
static int *dI, *dJ, *dS, *bestJ, *bestS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp;
static long long *wt, *unc;
static long long wsum_w, last_w;
static int best_n, best_m;
static int *best_e;

typedef struct { int gi, k; long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = TAB[g * G + s];
}

/* Returns the true cost (uncovered ordered pairs from block representatives).
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
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = NULL;
    wt = unc = NULL;
}

static void setup_group(int gi, int k) {
    G = gord[gi];
    TAB = gtab[gi];
    K = k;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
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

/* Voltage changes and within-layer target swaps; both keep each layer a permutation. */
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
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * G > best_n) emit();
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
    best_e = NULL;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    /* Stdin: group count, a dummy edge-count token, then the groups. */
    int ng_read = 0, mdummy = 0;
    if (scanf("%d", &ng_read) != 1) ng_read = 0;
    if (scanf("%d", &mdummy) != 1) mdummy = 0;
    if (ng_read > MAXGROUPS) ng_read = MAXGROUPS;
    gord = malloc(sizeof(int) * MAXGROUPS);
    gtab = malloc(sizeof(int *) * MAXGROUPS);
    NG = 0;
    for (int gi = 0; gi < ng_read; gi++) {
        int g = 0;
        if (scanf("%d", &g) != 1 || g < 1 || g > 2000) break;
        int *tb = malloc(sizeof(int) * (size_t)g * (size_t)g);
        int ok = 1;
        for (size_t i = 0; i < (size_t)g * (size_t)g && ok; i++)
            if (scanf("%d", &tb[i]) != 1) ok = 0;
        if (!ok) { free(tb); break; }
        gord[NG] = g;
        gtab[NG] = tb;
        NG++;
    }
    if (NG == 0) {
        printf("0 0\n");
        return 0;
    }

    int MAXT = DEG * KMAX;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
        pool[i].gi = 0;
        pool[i].k = 1;
    }
    npool = 0;

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg *c = &pool[pi];
            int gi = c->gi, k = c->k;
            setup_group(gi, k);
            memcpy(dJ, c->J, sizeof(int) * (size_t)T);
            memcpy(dS, c->S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(gi, k, bc, bestJ, bestS);
            free_config();
            continue;
        }

        /* Fresh random lift over a random eligible (group, K) pair. */
        int cg[MAXGROUPS * KMAX], ck[MAXGROUPS * KMAX];
        int nc = 0;
        for (int gi = 0; gi < NG; gi++)
            for (int k = 1; k <= KMAX; k++)
                if (2LL * k * gord[gi] > best_n) {
                    cg[nc] = gi;
                    ck[nc] = k;
                    nc++;
                }
        if (nc == 0) break;
        int pick = rnd_int(nc);
        setup_group(cg[pick], ck[pick]);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(cg[pick], ck[pick], bc, bestJ, bestS);
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
# Group construction (Python). Each group is (order, table) with table a flat
# row-major list, identity at index 0, element x*y at table[x*n + y].
# ----------------------------------------------------------------------------

MAXG = 700


def _closure_table(gens, mul, ident):
    """Group generated by gens (finite, so closure under right multiplication suffices)."""
    index = {ident: 0}
    elems = [ident]
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in index:
                    if len(elems) >= MAXG:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    n = len(elems)
    tab = []
    for a in elems:
        tab.extend(index[mul(a, b)] for b in elems)
    return n, tab


def _mm(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def _sl2(p, proj):
    """SL(2,p), or PSL(2,p) = SL(2,p)/{+-I} when proj is True."""
    def neg(x):
        return tuple((-v) % p for v in x)

    if proj:
        def mul(x, y):
            z = _mm(x, y, p)
            return min(z, neg(z))
    else:
        def mul(x, y):
            return _mm(x, y, p)
    gens = [(1, 1, 0, 1), (0, p - 1, 1, 0)]
    return _closure_table(gens, mul, (1, 0, 0, 1))


def _perm_mul(x, y):
    return tuple(x[i] for i in y)


def _cycle(n, cyc):
    p = list(range(n))
    for a, b in zip(cyc, cyc[1:] + cyc[:1]):
        p[a] = b
    return tuple(p)


def _sym(n, alt):
    """S_n, or A_n, as a permutation group."""
    ident = tuple(range(n))
    if alt:
        second = list(range(1, n)) if n % 2 == 0 else list(range(n))
        gens = [_cycle(n, [0, 1, 2]), _cycle(n, second)]
    else:
        gens = [_cycle(n, [0, 1]), _cycle(n, list(range(n)))]
    return _closure_table(gens, _perm_mul, ident)


def _cyc(n):
    return n, [(a + b) % n for a in range(n) for b in range(n)]


def _semi(m, k, r):
    n, mul, _ = lib.semidirect_group(m, k, r)
    return n, [mul(a, b) for a in range(n) for b in range(n)]


def _unit_of_order_dividing(m, k):
    for r in range(2, m):
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
            return r
    return None


def _specs():
    """(estimated order, thunk) pairs for the group families."""
    out = [
        (60, lambda: _sl2(5, True)),
        (120, lambda: _sl2(5, False)),
        (168, lambda: _sl2(7, True)),
        (336, lambda: _sl2(7, False)),
        (660, lambda: _sl2(11, True)),
        (60, lambda: _sym(5, True)),
        (120, lambda: _sym(5, False)),
        (360, lambda: _sym(6, True)),
        (342, lambda: _cyc(342)),
    ]
    for m, k in [(19, 18), (19, 9), (37, 9), (37, 12), (37, 18), (29, 14), (31, 10),
                 (31, 15), (43, 7), (43, 14), (61, 6), (73, 4), (41, 10), (23, 11),
                 (17, 16), (17, 8), (13, 12), (11, 10), (7, 6)]:
        r = _unit_of_order_dividing(m, k)
        if r is not None:
            out.append((m * k, lambda m=m, k=k, r=r: _semi(m, k, r)))
    return out


def _pick_groups(best_n, seed, start, time_limit):
    lo = max(8, best_n // 6 + 1)
    specs = [s for s in _specs() if lo <= s[0] <= MAXG]
    rng = random.Random(seed)
    rng.shuffle(specs)
    groups = []
    total = 0
    for order, thunk in specs:
        if time.monotonic() - start > 0.2 * time_limit or len(groups) >= 16:
            break
        if total > 2_000_000:
            break
        try:
            res = thunk()
        except Exception:
            res = None
        if res is None:
            continue
        n, tab = res
        if n < lo or n > MAXG or total + n * n > 2_000_000:
            continue
        groups.append((n, tab))
        total += n * n
    return groups


def _flatten(groups):
    flat = []
    for n, tab in groups:
        flat.append(n)
        flat.extend(tab)
    if len(flat) % 2:
        flat.append(0)
    return flat


class _Pairs:
    """Lazy sequence of consecutive integer pairs, so the flat stream can be sent via lib.run_c."""

    def __init__(self, flat):
        self.flat = flat

    def __len__(self):
        return len(self.flat) // 2

    def __iter__(self):
        f = self.flat
        for i in range(0, len(f), 2):
            yield (f[i], f[i + 1])


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
# Driver: baselines in Python, then one C run over several groups.
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

    # Give the C search nearly all of the budget.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0 and D >= 3:
        try:
            groups = _pick_groups(best_n, seed, start, time_limit)
            if groups:
                flat = _flatten(groups)
                stdin = (len(groups), _Pairs(flat))
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                                stdin_graph=stdin, timeout=remaining + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
