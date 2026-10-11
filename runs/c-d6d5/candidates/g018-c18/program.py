import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: bi-Cayley lifts over an ARBITRARY finite group.
#
# The parent only used metacyclic groups Z_m x| Z_k. This version builds the
# group as a multiplication table in Python, so it can use non-metacyclic
# groups too: generalized dihedral groups (Z_a x Z_b) x| Z_2 with inversion,
# and direct products of metacyclic factors. The table is passed to C on stdin.
#
# Graph: K base A-vertices and K base B-vertices, each with |G| copies. Dart
# (i, j, s) joins A_{i,g} to B_{j,g*s}. Each layer is a permutation, so every
# vertex has degree DEG. Left multiplication by G is an automorphism that fixes
# the sides, so diameter <= D iff BFS of depth D from A_{i,e} and B_{j,e}
# covers all vertices. Identity must be element 0 (checked in Python).
#
# C search: simulated annealing with breakout weights and iterated local search
# over one group and one K per run. A zero-cost configuration is valid and is
# printed at once, which frees the remaining budget for the next run.
#
# Fallbacks: K_{d,d}, PG(2,q) incidence (D >= 3). Every output is checked with
# lib.is_valid before it is kept.
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
#define POOLMAX 32
#define POOLP 0.6
#define BRK 150
#define KMAX 8

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

static int DEG, DIAM, K, G, T, N;
static int *mul;                 /* mul[x*G+y] = x*y, identity is 0 */
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static int curstamp = 0;
static long long *wt, *unc;
static long long wsum = 0, last_w = 0;

typedef struct { long long cost; int *J; int *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = mul[g * G + s];
}

/* Returns the true cost (sum of uncovered vertices over the 2K block BFS).
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
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            if (cnt[a] >= DEG || cnt[b] >= DEG) { last_w = BIGC; return BIGC; }
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

static void alloc_all(void) {
    T = DEG * K;
    N = 2 * K * G;
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
    for (int r = 0; r < 2 * K; r++) { wt[r] = 1; unc[r] = 0; }
    wsum = 2 * K;
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)T);
        pool[i].S = malloc(sizeof(int) * (size_t)T);
        pool[i].cost = BIGC;
    }
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

/* Random kicks: voltage changes and within-layer target swaps (both keep layers permutations). */
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
   The caller must have just called eval_cost(). Returns the best true cost,
   with the best state in bestJ/bestS. */
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
                wcur = 0;
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum++; }
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum / (2.0 * K);
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
    pool[slot].cost = cost;
    memcpy(pool[slot].J, J, sizeof(int) * (size_t)T);
    memcpy(pool[slot].S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int bi = rnd_int(npool);
    for (int s = 0; s < 2; s++) {
        int c = rnd_int(npool);
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* Load the zero-cost configuration and print the graph in the standard text format. */
static void finish_and_print(void) {
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    printf("%d %d\n", N, T * G);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", dI[t] * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog d D seed time_limit start_n K  (group table on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = atoi(argv[5]);
    K = atoi(argv[6]);

    int gn = 0, gm = 0;
    if (scanf("%d %d", &gn, &gm) != 2 || gn < 1 || (long long)gn * gn != (long long)gm) {
        printf("0 0\n");
        return 0;
    }
    G = gn;
    if (DEG < 1 || DIAM < 1 || K < 1 || K > KMAX || 2LL * K * G <= start_n) {
        printf("0 0\n");
        return 0;
    }
    mul = malloc(sizeof(int) * (size_t)G * G);
    for (int i = 0; i < gm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= gm || v < 0 || v >= G) {
            printf("0 0\n");
            return 0;
        }
        mul[u] = v;
    }

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    alloc_all();

    while (elapsed() < DEADLINE) {
        if (npool > 0 && rnd_unit() < POOLP) {
            int pi = pick_pool();
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            if (bc == 0) { finish_and_print(); return 0; }
            pool_add(bc, bestJ, bestS);
        } else {
            random_init();
            long long cst = eval_cost();
            long long bc = run_sa(ITERS, 1.0, cst);
            if (bc == 0) { finish_and_print(); return 0; }
            pool_add(bc, bestJ, bestS);
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Group tables built in Python. Every group has identity element 0.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [x for x in range(1, n + 1) if n % x == 0]


def _metas(G):
    """Descriptors of metacyclic groups Z_m x|_r Z_k of order G (k=1 gives cyclic)."""
    out = []
    for k in _divisors(G):
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append(("meta", m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("meta", m, k, r))
    return out


def _factor(desc):
    """Return (order, mul) for a group descriptor."""
    kind = desc[0]
    if kind == "meta":
        _, m, k, r = desc
        order, mul, _ = lib.semidirect_group(m, k, r)
        return order, mul
    if kind == "gd":
        # (Z_a x Z_b) x| Z_2 with the involution acting by inversion. Element index v*2 + s.
        _, a, b = desc

        def mul(x, y):
            s1, v1 = x % 2, x // 2
            s2, v2 = y % 2, y // 2
            x1, y1 = divmod(v1, b)
            x2, y2 = divmod(v2, b)
            sg = -1 if s1 else 1
            nx_ = (x1 + sg * x2) % a
            ny_ = (y1 + sg * y2) % b
            return (nx_ * b + ny_) * 2 + (s1 ^ s2)

        return 2 * a * b, mul
    if kind == "prod":
        o1, m1 = _factor(desc[1])
        o2, m2 = _factor(desc[2])

        def mul(x, y):
            a1, b1 = divmod(x, o2)
            a2, b2 = divmod(y, o2)
            return m1(a1, a2) * o2 + m2(b1, b2)

        return o1 * o2, mul
    raise ValueError(kind)


def _table(desc):
    """Flat multiplication table, or None if the identity is not element 0."""
    order, mul = _factor(desc)
    if any(mul(0, y) != y or mul(y, 0) != y for y in range(order)):
        return None
    return order, [mul(x, y) for x in range(order) for y in range(order)]


def _pick_desc(G, rng):
    """Pick a group of order G, preferring non-metacyclic ones when available."""
    metas = _metas(G)
    nonmeta = []
    if G % 2 == 0 and G >= 4:
        half = G // 2
        nonmeta += [("gd", a, half // a) for a in _divisors(half)]
    for o1 in _divisors(G):
        o2 = G // o1
        if o1 >= 2 and o2 >= 2 and o1 <= o2:
            m1, m2 = _metas(o1), _metas(o2)
            if m1 and m2:
                nonmeta.append(("prod", rng.choice(m1), rng.choice(m2)))
    if nonmeta and rng.random() < 0.8:
        return rng.choice(nonmeta)
    return rng.choice(metas)


def _group_table(G, seed, cache):
    """Cached (order, flat table) for a group of order G, or None."""
    if G in cache:
        return cache[G]
    res = None
    if 2 <= G and G * G <= 300000:
        rng = random.Random(seed * 1000003 + G * 7 + 1)
        for _ in range(4):
            tab = _table(_pick_desc(G, rng))
            if tab is not None:
                res = tab
                break
    cache[G] = res
    return res


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    if best_n >= lib.moore_bound(d, D):
        return best

    # Bi-Cayley runs over new group families. Each run has a group order G and
    # K base vertices per side, and yields 2*K*G vertices. Order the plan so that
    # K=1 runs (the record-level target) come first and K=2,3 run in between.
    cache = {}
    plan = [(1, best_n // 2 + 1), (2, best_n // 4 + 1), (1, best_n // 2 + 2),
            (3, best_n // 6 + 1), (1, best_n // 2 + 3), (2, best_n // 4 + 2)]
    for idx, (K, G) in enumerate(plan):
        if G < 2 or 2 * K * G <= best_n:
            continue
        tab = _group_table(G, seed, cache)
        if tab is None:
            continue
        order, flat = tab
        left = 0.9 * time_limit - 1.0 - (time.monotonic() - start)
        budget = left / (len(plan) - idx)
        if budget < 2.0:
            break
        pairs = list(enumerate(flat))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n, K],
                            stdin_graph=(order, pairs), timeout=budget + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass
        if best_n >= lib.moore_bound(d, D):
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
