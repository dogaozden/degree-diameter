import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over a base of K A-vertices and K B-vertices, with the
# voltage group chosen from a list of finite groups given on the command line.
# Group families (multiplication computed in C from a few integers):
#   type 0: Z_m x|_r Z_k  (r = 1 gives the abelian product Z_m x Z_k)
#   type 1: dihedral group D_m of order 2m
#   type 2: affine group AGL(1,p) = {x -> ax+b}, order p(p-1)
# Left multiplication is an automorphism of every lift, so diameter <= D iff
# BFS of depth D from one vertex in each of the 2K blocks covers the graph.
# Search: simulated annealing on the weighted uncovered-pair cost with breakout
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
#define POOLP 0.6
#define BRK 150
#define MAXGRP 2048
#define MAXORD 2048
#define MAXK 3
#define NMAX (2 * MAXK * MAXORD)

typedef struct { int type, p1, p2, r, order; } Grp;

static Grp grp[MAXGRP];
static int ngrp = 0;

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
static int cur, K, G, T, N;
static int Rpow[MAXORD];
static int *dI, *dJ, *dS, *bestJ, *bestS;
static int *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;
static long long wt[2 * MAXK], unc[2 * MAXK];
static long long wsum_w = 0, last_w = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

typedef struct { int gid, K; long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

/* Group multiplication for the current group (element indices 0..order-1). */
static int gm(int x, int y) {
    const Grp *g = &grp[cur];
    if (g->type == 0) {
        int m = g->p1, k = g->p2;
        int a = x / k, b = x % k, c = y / k, e = y % k;
        int ra = (int)(((long long)a + (long long)Rpow[b] * c) % m);
        return ra * k + (b + e) % k;
    } else if (g->type == 1) {
        int m = g->p1;
        int a = x >> 1, s = x & 1, c = y >> 1, t = y & 1;
        int ca = s ? (m - c) % m : c;
        return ((a + ca) % m) * 2 + (s ^ t);
    } else {
        int p = g->p1;
        int a1 = x / p + 1, b1 = x % p, a2 = y / p + 1, b2 = y % p;
        int a = (a1 * a2) % p;
        int b = (a1 * b2 + b1) % p;
        return (a - 1) * p + b;
    }
}

static int grp_consistent(const Grp *g) {
    if (g->type == 0) return g->p1 >= 2 && g->p2 >= 1 && g->p1 * g->p2 == g->order;
    if (g->type == 1) return g->p1 >= 2 && 2 * g->p1 == g->order;
    if (g->type == 2) return g->p1 >= 3 && g->p1 * (g->p1 - 1) == g->order;
    return 0;
}

static void parse_groups(const char *s) {
    ngrp = 0;
    while (*s && ngrp < MAXGRP) {
        int t, p1, p2, r, o, n = 0;
        if (sscanf(s, "%d:%d:%d:%d:%d%n", &t, &p1, &p2, &r, &o, &n) != 5 || n <= 0) break;
        Grp g = {t, p1, p2, r, o};
        if (o >= 1 && o <= MAXORD && grp_consistent(&g)) grp[ngrp++] = g;
        s += n;
        if (*s == '|') s++;
        else break;
    }
}

static void setup_group(int gid, int k) {
    cur = gid;
    K = k;
    G = grp[gid].order;
    T = DEG * K;
    N = 2 * K * G;
    if (grp[gid].type == 0) {
        int m = grp[gid].p1, kk = grp[gid].p2, r = grp[gid].r;
        Rpow[0] = 1 % m;
        for (int b = 1; b < kk; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * r % m);
    }
    for (int b = 0; b < 2 * K; b++) { wt[b] = 1; unc[b] = 0; }
    wsum_w = 2 * K;
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void build_perm(int t) {
    int *pm = perm + (size_t)t * G;
    int s = dS[t];
    for (int g = 0; g < G; g++) pm[g] = gm(g, s);
}

/* Sum of uncovered ordered pairs over the 2K block representatives.
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
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * NMAX);
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

/* Voltage changes and within-layer target swaps keep every layer a permutation. */
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

/* A zero-cost run is a valid graph (no duplicate darts, diameter <= DIAM). */
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
    c->gid = cur;
    c->K = K;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * grp[pool[i].gid].order;
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

/* Group of order with 2*k*order > best_n. Prefer groups just above the record
   threshold, since those give the most improvement per run. */
static int pick_group(int k) {
    static int near[MAXGRP], far[MAXGRP];
    int nn = 0, nf = 0;
    for (int g = 0; g < ngrp; g++) {
        double v = 2.0 * k * grp[g].order;
        if (v > (double)best_n) {
            if (v <= 1.15 * (double)best_n + 12.0) near[nn++] = g;
            else far[nf++] = g;
        }
    }
    if (nn == 0 && nf == 0) return -1;
    if (nn > 0 && (nf == 0 || rnd_unit() < 0.7)) return near[rnd_int(nn)];
    return far[rnd_int(nf)];
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n groups]\n");
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
    parse_groups(argc > 6 ? argv[6] : "");

    int TM = MAXK * DEG;
    dI = malloc(sizeof(int) * (size_t)TM);
    dJ = malloc(sizeof(int) * (size_t)TM);
    dS = malloc(sizeof(int) * (size_t)TM);
    bestJ = malloc(sizeof(int) * (size_t)TM);
    bestS = malloc(sizeof(int) * (size_t)TM);
    perm = malloc(sizeof(int) * (size_t)TM * MAXORD);
    adj = malloc(sizeof(int) * (size_t)NMAX * DEG);
    cnt = malloc(sizeof(int) * (size_t)NMAX);
    stamp = calloc((size_t)NMAX, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NMAX);
    nx = malloc(sizeof(int) * (size_t)NMAX);
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)TM);
        pool[i].S = malloc(sizeof(int) * (size_t)TM);
        pool[i].cost = BIGC;
    }

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            Cfg *c = &pool[pi];
            setup_group(c->gid, c->K);
            memcpy(dJ, c->J, sizeof(int) * (size_t)T);
            memcpy(dS, c->S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            continue;
        }

        int k = kc[rnd_int(5)];
        int gid = pick_group(k);
        if (gid < 0) {
            for (int c = 1; c <= MAXK; c++) {
                int g2 = pick_group(c);
                if (g2 >= 0) { gid = g2; k = c; break; }
            }
        }
        if (gid < 0) break;
        setup_group(gid, k);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
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
# Group families for the C engine, passed as "type:p1:p2:r:order" items.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    return all(p % q for q in range(2, int(math.isqrt(p)) + 1))


def _group_specs(lo, hi, seed, cap_per_order=2):
    """Groups of order in [lo, hi]: semidirect Z_m x| Z_k, dihedral D_m, and AGL(1,p).

    Up to cap_per_order random specs are kept per order, so every order is covered.
    """
    rng = random.Random(seed)
    by_order = {}

    def add(o, spec):
        by_order.setdefault(o, []).append(spec)

    for m in range(2, hi + 1):
        for k in range(1, hi // m + 1):
            o = m * k
            if o < lo or o > hi:
                continue
            if k == 1:
                add(o, (0, m, 1, 1, o))
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    add(o, (0, m, k, r, o))
    for m in range(2, hi // 2 + 1):
        o = 2 * m
        if lo <= o <= hi:
            add(o, (1, m, 0, 0, o))
    for p in range(3, hi + 1):
        o = p * (p - 1)
        if o > hi:
            break
        if o >= lo and _is_prime(p):
            add(o, (2, p, 0, 0, o))

    specs = []
    for o in sorted(by_order):
        opts = by_order[o]
        if len(opts) > cap_per_order:
            opts = rng.sample(opts, cap_per_order)
        specs.extend(opts)
    return specs


def _spec_text(specs):
    return "|".join(f"{t}:{a}:{b}:{r}:{o}" for t, a, b, r, o in specs)


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C group-lift search.
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
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    elapsed = time.monotonic() - start
    remaining = 0.9 * time_limit - elapsed - 1.0
    if remaining >= 1.0:
        # A group of order G gives 2*K*G vertices, so only orders above best_n / 6
        # matter for K <= 3. The largest useful order is about moore / 2.
        lo = max(2, best_n // 6)
        hi = min(moore // 2, 1200)
        specs = _group_specs(lo, hi, seed) if hi >= lo else []
        if specs:
            hard = min(remaining + 3.0, time_limit - elapsed - 1.5)
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, seed, f"{remaining:.2f}", best_n, _spec_text(specs)],
                                timeout=hard)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
