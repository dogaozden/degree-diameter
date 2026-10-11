import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an ARBITRARY finite group given by its
# multiplication table (sent from Python). Base graph: K A-vertices and K
# B-vertices, DEG layers, each layer a permutation of the B-vertices.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h, with G the group order.
# Dart t = (i, j, s) joins A_i,g to B_j,(g*s) for all g. Left multiplication
# is an automorphism, so the diameter is at most DIAM iff a BFS of depth DIAM
# from each of the 2K block representatives covers everything.
#
# Search: simulated annealing on the number of uncovered ordered pairs, with
# breakout weights, plus an elite pool with iterated local search. Stops as
# soon as a valid lift is found.
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
#define MAXK 8

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

static int DEG, DIAM, K, G, T, NV;
static int *tab;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static int curstamp;
static long long *wt, *unc;
static long long wsum_w, last_w;
static int best_n, best_m;
static int *best_e;
static int *poolJ, *poolS;
static long long poolC[POOLMAX];
static int pool_n;

static void reset_weights(void) {
    for (int r = 0; r < 2 * K; r++) wt[r] = 1;
    wsum_w = 2 * K;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = tab[(size_t)g * G + s];
}

/* Returns the sum of uncovered ordered pairs over the 2K block representatives.
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    int N = NV;
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

static void alloc_all(void) {
    int N = NV;
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
    poolJ = malloc(sizeof(int) * (size_t)POOLMAX * T);
    poolS = malloc(sizeof(int) * (size_t)POOLMAX * T);
    for (int t = 0; t < T; t++) {
        dI[t] = t % K;
        dJ[t] = 0;
        dS[t] = 0;
    }
    curstamp = 0;
    pool_n = 0;
    reset_weights();
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

/* Random kicks: target swaps within a layer and voltage changes. */
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
   Caller must have called reset_weights() and eval_cost() just before. */
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
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    best_m = m;
    best_n = NV;
}

/* Returns 1 if a valid lift was found (the search then stops). */
static int finish_run(long long bc) {
    if (bc != 0) return 0;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (NV > best_n) emit();
    return 1;
}

static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (pool_n < POOLMAX) {
        slot = pool_n++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (poolC[i] > poolC[slot]) slot = i;
        if (poolC[slot] <= cost) return;
    }
    poolC[slot] = cost;
    memcpy(poolJ + (size_t)slot * T, J, sizeof(int) * (size_t)T);
    memcpy(poolS + (size_t)slot * T, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int bi = rnd_int(pool_n);
    for (int s = 0; s < 2; s++) {
        int c = rnd_int(pool_n);
        if (poolC[c] < poolC[bi]) bi = c;
    }
    return bi;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog d D seed time K start_n\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    best_n = atoi(argv[6]);
    best_m = 0;
    best_e = NULL;

    long long n0 = 0, m0 = 0;
    if (scanf("%lld %lld", &n0, &m0) != 2 || DEG < 1 || DIAM < 1 || K < 1 || K > MAXK ||
        n0 < 1 || n0 > 4000 || m0 != n0 * n0) {
        printf("0 0\n");
        return 0;
    }
    G = (int)n0;
    tab = malloc(sizeof(int) * (size_t)m0);
    for (long long i = 0; i < m0; i++) {
        long long u = 0, v = 0;
        if (scanf("%lld %lld", &u, &v) != 2 || v < 0 || v >= n0) {
            printf("0 0\n");
            return 0;
        }
        tab[i] = (int)v;
    }
    NV = 2 * K * G;

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    alloc_all();

    while (elapsed() < DEADLINE) {
        int stop = 0;
        if (pool_n > 0 && rnd_unit() < POOLP) {
            int pi = pick_pool();
            memcpy(dJ, poolJ + (size_t)pi * T, sizeof(int) * (size_t)T);
            memcpy(dS, poolS + (size_t)pi * T, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            reset_weights();
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            stop = finish_run(bc);
            if (!stop) pool_add(bc, bestJ, bestS);
        } else {
            random_init();
            reset_weights();
            long long cost = eval_cost();
            long long bc = run_sa(ITERS, 1.0, cost);
            stop = finish_run(bc);
            if (!stop) pool_add(bc, bestJ, bestS);
        }
        if (stop) break;
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


MAX_ORDER = 800      # largest group order we build tables for
MAX_GROUPS = 6       # groups tried per case (time is split between them)
MAX_K = 8            # largest base-graph size (A and B vertices per side)


# ----------------------------------------------------------------------------
# Safe baselines (unchanged from the parent).
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
# Group library: multiplication tables of finite groups (numpy int arrays).
# Element 0 is always the identity.
# ----------------------------------------------------------------------------

def _closure(gens, n):
    """All elements of the permutation group generated by gens (tuples on range(n)), identity first.

    Returns an (N, n) int array, or None if the group is larger than MAX_ORDER.
    """
    e = tuple(range(n))
    elems, seen, frontier = [e], {e}, [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[i] for i in x)  # g after x
                if y not in seen:
                    if len(elems) >= MAX_ORDER:
                        return None
                    seen.add(y)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return np.array(elems, dtype=np.int64)


def _mult_table(E):
    """Multiplication table tab[i, j] = index of (elem_i o elem_j) for a permutation-group array E."""
    N, n = E.shape
    pw = np.array([n ** i for i in range(n)], dtype=np.int64)
    codes = E @ pw
    order = np.argsort(codes)
    sc = codes[order]
    tab = np.empty((N, N), dtype=np.int64)
    for i in range(N):
        comp = E[i][E]  # comp[j, k] = E[i][E[j, k]]
        pos = np.searchsorted(sc, comp @ pw)
        tab[i] = order[pos]
    return tab


def _perm_table(gens, n):
    E = _closure(gens, n)
    if E is None:
        return None
    return _mult_table(E)


def _sym_gens(n):
    t = list(range(n))
    t[0], t[1] = 1, 0
    c = [(i + 1) % n for i in range(n)]
    return [tuple(t), tuple(c)]


def _alt_gens(n):
    gens = []
    for i in range(2, n):
        p = list(range(n))
        p[0] = 1
        p[1] = i
        p[i] = 0
        gens.append(tuple(p))
    return gens


def _prim_root(p):
    """A primitive root modulo the prime p."""
    primes = [q for q in range(2, p) if (p - 1) % q == 0 and all(q % s for s in range(2, q))]
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in primes):
            return g
    return 1


def _psl_gens(p, extra_scalar=False):
    """Generators of PSL(2, p) acting on the projective line (points 0..p-1 and p = infinity).

    With extra_scalar, adds z -> g z for a primitive root g, giving PGL(2, p).
    """
    inf = p
    T = tuple([(z + 1) % p for z in range(p)] + [inf])
    S = tuple([inf if z == 0 else (-pow(z, p - 2, p)) % p for z in range(p)] + [0])
    gens = [T, S]
    if extra_scalar:
        g = _prim_root(p)
        gens.append(tuple([(g * z) % p for z in range(p)] + [inf]))
    return gens


def _sd_table(m, k, r):
    """Table of Z_m x|_r Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c, b + e)."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    Rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    ra = (a[:, None] + Rp[b][:, None] * a[None, :]) % m
    rb = (b[:, None] + b[None, :]) % k
    return ra * k + rb


def _named_specs():
    """Named groups: (name, order, builder)."""
    return [
        ("A5", 60, lambda: _perm_table(_alt_gens(5), 5)),
        ("S5", 120, lambda: _perm_table(_sym_gens(5), 5)),
        ("PSL7", 168, lambda: _perm_table(_psl_gens(7), 8)),
        ("PGL7", 336, lambda: _perm_table(_psl_gens(7, True), 8)),
        ("A6", 360, lambda: _perm_table(_alt_gens(6), 6)),
        ("PSL11", 660, lambda: _perm_table(_psl_gens(11), 12)),
        ("S6", 720, lambda: _perm_table(_sym_gens(6), 6)),
    ]


def _sd_specs(rng, lo, hi, count):
    """Random semidirect products Z_m x| Z_k with orders in [lo, hi]."""
    specs, seen, tries = [], set(), 0
    while len(specs) < count and tries < 5000:
        tries += 1
        m = rng.randint(3, 400)
        k = rng.randint(2, 24)
        N = m * k
        if N < lo or N > hi or (m, k) in seen:
            continue
        r = None
        for _ in range(80):
            c = rng.randint(1, m - 1)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                r = c
                break
        if r is None:
            continue
        seen.add((m, k))
        specs.append((f"sd{m}x{k}r{r}", N,
                      lambda m=m, k=k, r=r: _sd_table(m, k, r)))
    return specs


def _group_specs(rng):
    return _named_specs() + _sd_specs(rng, 60, MAX_ORDER, 60)


def _group_plan(best_n, moore, rng):
    """Pick up to MAX_GROUPS (name, K, builder) entries whose lifts have order just above a target.

    The target is about 0.45 of the Moore bound, and must exceed the current best.
    For each group, K is the smallest base size that reaches the target.
    """
    target = max(best_n + 1, int(0.45 * moore))
    opts = []
    for name, N, builder in _group_specs(rng):
        K = max(1, -(-target // (2 * N)))
        if K > MAX_K:
            continue
        verts = 2 * K * N
        if verts <= best_n:
            continue
        opts.append((verts, name, K, builder))
    opts.sort(key=lambda t: (t[0], t[1]))
    plan, seen = [], set()
    for verts, name, K, builder in opts:
        if name in seen:
            continue
        seen.add(name)
        plan.append((name, K, builder))
        if len(plan) >= MAX_GROUPS:
            break
    return plan


def _table_edges(tab):
    """Encode a group table as the (u, v) pairs that the C engine reads: pair k = (k // N, tab[k])."""
    N = tab.shape[0]
    us = np.repeat(np.arange(N, dtype=np.int64), N)
    return list(zip(us.tolist(), tab.ravel().tolist()))


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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Reserve time for the one-off C compile, parsing and validation.
    deadline = start + 0.85 * time_limit - 1.0
    if deadline - time.monotonic() < 2.0:
        return best

    plan = _group_plan(best_n, moore, random.Random(seed * 1000003 + 7))
    for idx, (name, K, builder) in enumerate(plan):
        left = deadline - time.monotonic()
        slots = len(plan) - idx
        slice_s = left / slots
        if slice_s < 1.5:
            break
        try:
            tab = builder()
            if tab is None:
                continue
            N = int(tab.shape[0])
            if 2 * K * N <= best_n:
                continue
            edges = _table_edges(tab)
            out = lib.run_c(C_SOURCE, [d, D, seed + idx, f"{slice_s:.2f}", K, best_n],
                            stdin_graph=(N, edges), timeout=slice_s + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass
        if best_n >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
