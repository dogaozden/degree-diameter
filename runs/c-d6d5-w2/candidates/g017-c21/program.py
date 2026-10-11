import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over metacyclic groups Z_m x|_r Z_k, searched by
# annealing over a general block multigraph.
#
# Structure: K A-blocks and K B-blocks. There are T = K*DEG darts (i, j, s).
# Dart t joins A_{i,g} to B_{j,g*s} for every g in the group. Every A-block
# and every B-block has exactly DEG darts, so every vertex has degree DEG.
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
# depth D from each of the 2K block representatives covers all vertices.
#
# Moves (differ from the layered search in the previous version):
#   - change the voltage s of one dart;
#   - swap the B-endpoints of two arbitrary darts (a double-edge switch on the
#     block multigraph). This keeps all block degrees fixed but reaches
#     non-layered block structures.
#
# Search: breakout-weighted simulated annealing (weights rise on uncovered
# blocks when the true cost stalls), restarts from random multigraphs, and an
# elite pool for iterated local search. Groups and orders are supplied as
# argv tokens "m:k:r", so this engine needs no stdin graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define KMAX 4
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 32
#define POOLP 0.5
#define BRK 150
#define MAXGRP 512

typedef struct { int m, k, r; } Grp;
typedef struct { int K, gi; long long cost; int *I, *J, *S; } Cfg;

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

static int DEG, DIAM, best_n, best_m, ngrp = 0;
static Grp grp[MAXGRP];
static int TMAX = 0, GMAX = 0, NMAX = 0;

static int Kb, M, KK, R, G, T, N;
static int *Rpow;
static int *di, *dj, *ds, *bi, *bj, *bs, *perm;
static int *adj, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;
static long long wt[2 * KMAX], unc[2 * KMAX];
static long long wsum = 0, last_w = 0;
static int *best_e = NULL;
static Cfg pool[POOLMAX];
static int npool = 0;

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

/* (a,b)*(c,e) = (a + R^b c, b + e), element index a*KK + b. */
static inline int gmul(int x, int y) {
    int a = x / KK, b = x % KK;
    int c = y / KK, e = y % KK;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % KK;
    return ra * KK + rb;
}

static void build_perm(int t) {
    int s = ds[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (di[t1] == di[t2] && dj[t1] == dj[t2] && ds[t1] == ds[t2]) {
                for (int r = 0; r < 2 * Kb; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = di[t] * G, bb = (Kb + dj[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * Kb; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)NMAX);
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
    for (int r = 0; r < 2 * Kb; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void alloc_all(void) {
    TMAX = KMAX * DEG;
    NMAX = 2 * KMAX * GMAX;
    di = malloc(sizeof(int) * (size_t)TMAX);
    dj = malloc(sizeof(int) * (size_t)TMAX);
    ds = malloc(sizeof(int) * (size_t)TMAX);
    bi = malloc(sizeof(int) * (size_t)TMAX);
    bj = malloc(sizeof(int) * (size_t)TMAX);
    bs = malloc(sizeof(int) * (size_t)TMAX);
    perm = malloc(sizeof(int) * (size_t)TMAX * GMAX);
    adj = malloc(sizeof(int) * (size_t)NMAX * DEG);
    cnt = malloc(sizeof(int) * (size_t)NMAX);
    stamp = calloc((size_t)NMAX, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NMAX);
    nx = malloc(sizeof(int) * (size_t)NMAX);
    Rpow = malloc(sizeof(int) * (size_t)(GMAX + 1));
    best_e = malloc(sizeof(int) * 2 * (size_t)TMAX * GMAX);
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].I = malloc(sizeof(int) * (size_t)TMAX);
        pool[i].J = malloc(sizeof(int) * (size_t)TMAX);
        pool[i].S = malloc(sizeof(int) * (size_t)TMAX);
        pool[i].cost = BIGC;
        pool[i].K = 0;
        pool[i].gi = 0;
    }
}

static void setup(int K, int gi) {
    Kb = K;
    M = grp[gi].m;
    KK = grp[gi].k;
    R = grp[gi].r;
    G = M * KK;
    T = Kb * DEG;
    N = 2 * Kb * G;
    Rpow[0] = 1 % M;
    for (int b = 1; b < KK; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    for (int b = 0; b < 2 * KMAX; b++) wt[b] = 1;
    wsum = 2 * Kb;
}

static void emit(void) {
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = di[t] * G + g;
            best_e[idx++] = (Kb + dj[t]) * G + perm[(size_t)t * G + g];
        }
    best_m = T * G;
    best_n = N;
}

static void random_init(void) {
    int *Bl = malloc(sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) {
        di[t] = t / DEG;
        Bl[t] = t / DEG;
    }
    for (int i = T - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int tmp = Bl[i]; Bl[i] = Bl[j]; Bl[j] = tmp;
    }
    for (int t = 0; t < T; t++) {
        dj[t] = Bl[t];
        ds[t] = rnd_int(G);
    }
    free(Bl);
    for (int t = 0; t < T; t++) build_perm(t);
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (rnd_unit() < 0.5) {
            int t1 = rnd_int(T), t2 = rnd_int(T);
            if (t1 == t2 || dj[t1] == dj[t2]) continue;
            int tmp = dj[t1]; dj[t1] = dj[t2]; dj[t2] = tmp;
        } else {
            int t = rnd_int(T);
            ds[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Annealing on the weighted cost with breakout bumps. The caller must have just
   evaluated the start state. The best state by true cost goes to bi/bj/bs. */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bi, di, sizeof(int) * (size_t)T);
    memcpy(bj, dj, sizeof(int) * (size_t)T);
    memcpy(bs, ds, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * Kb; r++)
                    if (unc[r] > 0) { wt[r]++; wsum++; }
                wcur = 0;
                for (int r = 0; r < 2 * Kb; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum / (2.0 * Kb);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (rnd_unit() < 0.5) {
            int t1 = rnd_int(T), t2 = rnd_int(T);
            if (t1 == t2 || dj[t1] == dj[t2]) continue;
            int tmp = dj[t1]; dj[t1] = dj[t2]; dj[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dj[t1]; dj[t1] = dj[t2]; dj[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = ds[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            ds[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                ds[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bi, di, sizeof(int) * (size_t)T);
            memcpy(bj, dj, sizeof(int) * (size_t)T);
            memcpy(bs, ds, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(di, bi, sizeof(int) * (size_t)T);
    memcpy(dj, bj, sizeof(int) * (size_t)T);
    memcpy(ds, bs, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (2LL * Kb * G > best_n) emit();
}

static void pool_add(long long cost, int K, int gi) {
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
    c->gi = gi;
    c->cost = cost;
    memcpy(c->I, bi, sizeof(int) * (size_t)(K * DEG));
    memcpy(c->J, bj, sizeof(int) * (size_t)(K * DEG));
    memcpy(c->S, bs, sizeof(int) * (size_t)(K * DEG));
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * grp[pool[i].gi].m * grp[pool[i].gi].k;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int pick = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[pick].cost) pick = c;
    }
    return pick;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog d D seed time_limit start_n ng [m:k:r ...]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = atoi(argv[5]);
    best_m = 0;
    int ng = atoi(argv[6]);
    if (DEG < 1 || DIAM < 1 || ng < 1) {
        printf("0 0\n");
        return 0;
    }
    if (ng > argc - 7) ng = argc - 7;
    for (int i = 0; i < ng && ngrp < MAXGRP; i++) {
        int m, k, r;
        if (sscanf(argv[7 + i], "%d:%d:%d", &m, &k, &r) != 3) continue;
        if (m < 1 || k < 1 || m * k < 2) continue;
        if (k == 1) {
            r = 1;
        } else {
            if (m < 2) continue;
            if (r < 1 || r >= m) continue;
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
        }
        grp[ngrp].m = m;
        grp[ngrp].k = k;
        grp[ngrp].r = r;
        if (m * k > GMAX) GMAX = m * k;
        ngrp++;
    }
    if (ngrp == 0) {
        printf("0 0\n");
        return 0;
    }
    alloc_all();
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            int K = pool[pi].K, gi = pool[pi].gi;
            setup(K, gi);
            memcpy(di, pool[pi].I, sizeof(int) * (size_t)T);
            memcpy(dj, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(ds, pool[pi].S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, K, gi);
            continue;
        }
        int gi = rnd_int(ngrp);
        int valid[KMAX], nv = 0;
        for (int K = 1; K <= KMAX; K++)
            if (2LL * K * grp[gi].m * grp[gi].k > best_n) valid[nv++] = K;
        if (nv == 0) continue;
        int K = valid[rnd_int(nv)];
        setup(K, gi);
        random_init();
        long long cst = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cst);
        finish_run(bc);
        pool_add(bc, K, gi);
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
# Python side: group families and safe fallbacks.
# ----------------------------------------------------------------------------

KMAX = 4


def _group_list(best_n, seed, cap=400):
    """Metacyclic groups Z_m x|_r Z_k (r = 1 gives direct products) with orders
    fitting K * |G| > best_n for some K <= KMAX, returned as (m, k, r) triples."""
    rng = random.Random(seed)
    lo = max(2, best_n // (2 * KMAX) + 1)
    hi = best_n // 2 + 40
    out = []
    for order in range(lo, hi + 1):
        for k in range(1, min(order, 12) + 1):
            if order % k:
                continue
            m = order // k
            if k == 1:
                out.append((m, 1, 1))
                continue
            if m < 2:
                continue
            roots = [r for r in range(2, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            picks = [1] + (rng.sample(roots, min(2, len(roots))) if roots else [])
            out.extend((m, k, r) for r in picks)
    rng.shuffle(out)
    return out[:cap]


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
# Driver: baselines first, then the C search over groups and block multigraphs.
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

    if best_n >= lib.moore_bound(d, D):
        return best

    # The C deadline counts from its own start, so the compile step is outside it.
    # The reserve covers parsing and validation. The subprocess timeout kills a
    # hung run early enough that the fallback still returns in time.
    elapsed = time.monotonic() - start
    remaining = 0.92 * time_limit - elapsed - 2.0
    if remaining >= 1.0 and d >= 2 and D >= 2:
        groups = _group_list(best_n, seed)
        if groups:
            args = [d, D, seed, f"{remaining:.2f}", best_n, len(groups)]
            args += [f"{m}:{k}:{r}" for m, k, r in groups]
            timeout = max(1.0, 0.97 * time_limit - (time.monotonic() - start))
            try:
                out = lib.run_c(C_SOURCE, args, timeout=timeout)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
