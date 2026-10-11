import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an arbitrary finite group given by its
# multiplication table. The table comes from Python (cyclic, semidirect
# Z_m x| Z_k, and affine groups AGL(1,q) for prime powers q), so the search is
# no longer restricted to semidirect products of cyclic groups.
#
# Model: base has K A-vertices and K B-vertices. Layer l (0..DEG-1) puts one
# dart from each A_i to a B_{p_l(i)}, with p_l a permutation, and a group
# element s. Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g in G.
# Every vertex gets degree DEG. Left multiplication is an automorphism, so the
# diameter is at most DIAM iff a BFS of depth DIAM from each of the 2K block
# representatives (element 0 of each block) covers the whole graph.
#
# Search: simulated annealing on the number of uncovered (rep, vertex) pairs,
# with breakout weights on blocks that stay uncovered. Duplicate darts are
# penalised. Each run starts from a random lift over a random eligible group
# (group order chosen so that the order 2KG beats the current best).
#
# Input (stdin, carried in the graph text format): the first two integers are
# a header, then NG, then for each group K, G and G*G table entries.
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
#define BRK 120
#define MAXGRP 64
#define MAXG 1200

typedef struct { int K, G; int *tab; } Grp;

static Grp grp[MAXGRP];
static int ngrp = 0;
static int DEG, DIAM;
static double DEADLINE;
static struct timespec T0;
static uint64_t rs[2];
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static int K, G, N, T;
static const int *TAB;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fq, *nq, *bestJ, *bestS;
static long long *wt, *unc;
static int curstamp;
static long long last_w;

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

static void alloc_run(int k, int g, const int *tab) {
    K = k; G = g; N = 2 * K * G; T = DEG * K; TAB = tab;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * (size_t)G);
    adj = malloc(sizeof(int) * (size_t)N * (size_t)DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fq = malloc(sizeof(int) * (size_t)N);
    nq = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    for (int r = 0; r < 2 * K; r++) { wt[r] = 1; unc[r] = 0; }
    for (int t = 0; t < T; t++) dI[t] = t % K;
    curstamp = 0;
}

static void free_run(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fq); free(nq);
    free(wt); free(unc);
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = TAB[g * G + s];
}

/* Total uncovered (rep, vertex) pairs plus duplicate-dart penalty; sets unc[] and last_w. */
static long long eval_cost(void) {
    long long dups = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) dups++;
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
    long long total = dups * (long long)N;
    long long w = dups * (long long)N * 2;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fq, *h = nq;
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
        w += wt[r] * unc[r];
    }
    last_w = w;
    return total;
}

static void random_init(void) {
    int p[8];
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

/* Annealing on the weighted cost with breakout weights. Returns best true cost; best state in bestJ/bestS. */
static long long run_sa(int iters) {
    long long cost = eval_cost();
    long long wcur = last_w;
    long long bestc = cost, prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) wt[r]++;
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        long long sumw = 0;
        for (int r = 0; r < 2 * K; r++) sumw += wt[r];
        double sc = (double)sumw / (2.0 * K);
        double fr = (double)it / (double)iters;
        double temp = (2.0 * (1.0 - fr) + 0.05) * sc;
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
    best_n = N;
}

static void read_input(void) {
    long long n, m;
    if (scanf("%lld %lld", &n, &m) != 2) return;
    size_t cap = 1 << 16, len = 0;
    long long *buf = malloc(sizeof(long long) * cap);
    long long x;
    while (scanf("%lld", &x) == 1) {
        if (len == cap) {
            cap *= 2;
            buf = realloc(buf, sizeof(long long) * cap);
        }
        buf[len++] = x;
    }
    if (len == 0) { free(buf); return; }
    size_t p = 0;
    long long NG = buf[p++];
    for (long long gi = 0; gi < NG; gi++) {
        if (p + 2 > len) break;
        long long kk = buf[p++], gg = buf[p++];
        if (gg < 1 || gg > MAXG || kk < 1 || kk > 3) break;
        size_t sz = (size_t)gg * (size_t)gg;
        if (p + sz > len) break;
        if (ngrp < MAXGRP) {
            int *tab = malloc(sizeof(int) * sz);
            for (size_t i = 0; i < sz; i++) tab[i] = (int)buf[p + i];
            grp[ngrp].K = (int)kk;
            grp[ngrp].G = (int)gg;
            grp[ngrp].tab = tab;
            ngrp++;
        }
        p += sz;
    }
    free(buf);
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
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    read_input();
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    while (elapsed() < DEADLINE) {
        int cand[MAXGRP], nc = 0;
        for (int gi = 0; gi < ngrp; gi++)
            if (2LL * grp[gi].K * grp[gi].G > best_n) cand[nc++] = gi;
        if (nc == 0) break;
        int gi = cand[rnd_int(nc)];
        alloc_run(grp[gi].K, grp[gi].G, grp[gi].tab);
        random_init();
        long long bc = run_sa(ITERS);
        if (bc == 0) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(dS, bestS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            if (N > best_n) emit();
        }
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

MAXG = 1100


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
# Group multiplication tables (flat, index x*G + y = x*y).
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    """Table of Z_m x|_r Z_k, element (a, b) coded as a*k + b, (a,b)(c,e) = (a + r^b c, b + e)."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    B = idx % k
    Rp = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    ra = (A[:, None] + Rp[B][:, None] * A[None, :]) % m
    rb = (B[:, None] + B[None, :]) % k
    return (ra * k + rb).ravel()


def _agl_table(q):
    """Table of AGL(1, q) = {x -> a x + b : a != 0}, code (a-1)*q + b, composed as functions."""
    F = lib.GF(q)
    G = q * (q - 1)
    idx = np.arange(G, dtype=np.int64)
    A = idx // q + 1
    B = idx % q
    MT = np.asarray(F.mul_table, dtype=np.int64)
    AD = np.asarray(F.add_table, dtype=np.int64)
    newA = MT[A[:, None], A[None, :]]
    newB = AD[MT[A[:, None], B[None, :]], B[:, None]]
    return ((newA - 1) * q + newB).ravel()


def _find_r(m, k, rng):
    """Random r with gcd(r, m) = 1 and r^k = 1 mod m, or None."""
    if k == 1 or m < 3:
        return 1
    for _ in range(80):
        r = rng.randrange(2, m)
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            return r
    return None


def _group_pool(best_n, rng):
    """Return a list of (K, G, table) for groups whose lifts could beat best_n."""
    specs = []
    KS = [1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12]
    for K in (1, 2, 3):
        lo = best_n // (2 * K) + 1
        hi = min(MAXG, int(lo * 2.2) + 4)
        if lo < 2 or lo > hi:
            continue
        for q in range(5, 40):
            if lib.is_prime_power(q) and lo <= q * (q - 1) <= hi:
                specs.append(("agl", K, q * (q - 1), q, 0, 0))
        for _ in range(60):
            k = rng.choice(KS)
            G = rng.randrange(lo, hi + 1)
            G -= G % k
            if G < lo or G < 2:
                continue
            m = G // k
            if m < 2:
                continue
            r = _find_r(m, k, rng)
            if r is None:
                continue
            specs.append(("sd", K, G, m, k, r))
    rng.shuffle(specs)

    chosen, budget, total = [], 1_600_000, 0
    for spec in specs:
        if len(chosen) >= 10:
            break
        G = spec[2]
        if total + G * G > budget:
            continue
        total += G * G
        chosen.append(spec)

    groups = []
    for spec in chosen:
        try:
            if spec[0] == "agl":
                tab = _agl_table(spec[3])
            else:
                tab = _semidirect_table(spec[3], spec[4], spec[5])
            groups.append((spec[1], spec[2], tab.tolist()))
        except Exception:
            continue
    return groups


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C lift search over group tables.
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

    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
        try:
            rng = random.Random(seed)
            groups = _group_pool(best_n, rng)
            if groups:
                data = [len(groups)]
                for K, G, tab in groups:
                    data.extend([K, G])
                    data.extend(tab)
                if len(data) % 2:
                    data.append(0)
                edges = [(data[i], data[i + 1]) for i in range(0, len(data), 2)]
                out = lib.run_c(C_SOURCE,
                                [d, D, seed % (1 << 32), f"{remaining:.2f}", best_n],
                                stdin_graph=(0, edges),
                                timeout=remaining + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
