import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over an arbitrary finite group given by its
# multiplication table. Base graph has K A-vertices and K B-vertices. Each of
# the DEG layers is a permutation pairing A_i with B_{p_l(i)} through a group
# element s, so every vertex has degree DEG. Vertices are A_{i,g} = i*G+g and
# B_{j,h} = (K+j)*G+h, with dart (i, j, s) joining A_{i,g} to B_{j,g*s}.
#
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
# depth D from each of the 2K block representatives (i*G+id) covers the graph.
#
# Groups arrive on stdin as a flat list of integers, passed through the
# standard graph channel: header "0 m", then m pairs. Layout of the flat data:
# ng, then per group: G, id, and the G*G table mul[x*G+y] in row-major order.
#
# Search: simulated annealing with breakout weights, plus an elite pool
# (iterated local search) keyed by group. The annealer minimises uncovered
# ordered pairs. The deadline uses wall-clock time from program start.
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
#define MAXGROUPS 96
#define WIN 60

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

typedef struct { int G, id; int *mul; } Group;
static Group grp[MAXGROUPS];
static int ngrp = 0;

static int DEG, DIAM;
static int K, G, ID, T, N;
static const int *MUL;
static int *dI, *dJ, *dS, *bestJ, *bestS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static long long *wt, *unc;
static long long wsum, last_w;
static int curstamp;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

typedef struct { int gi, K; long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = MUL[g * G + s];
}

static void build_all(void) {
    for (int t = 0; t < T; t++) build_perm(t);
}

static void setup_group(int gi, int k) {
    K = k;
    G = grp[gi].G;
    ID = grp[gi].id;
    MUL = grp[gi].mul;
    N = 2 * K * G;
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
    for (int t = 0; t < T; t++) { dI[t] = t % K; dJ[t] = 0; dS[t] = ID; }
    for (int r = 0; r < 2 * K; r++) { wt[r] = 1; unc[r] = 0; }
    wsum = 2 * K;
    last_w = 0;
    curstamp = 0;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
}

/* Returns the total number of uncovered ordered pairs over the 2K block
   representatives. Sets unc[r] per block and last_w to the weighted cost. */
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
            if (cnt[a] >= DEG || cnt[b] >= DEG) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0, w = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int src = r * G + ID;
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
    int p[4];
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
    build_all();
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

/* Annealing on the weighted cost with breakout weight bumps. Caller must have
   just called eval_cost(). Returns the best true cost; best state in bestJ/bestS. */
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
                    if (unc[r] > 0) { wt[r]++; wsum++; }
                wcur = 0;
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

/* A zero-cost run is a valid graph: reload it, re-verify, and emit if it beats the best. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    build_all();
    if (eval_cost() == 0 && N > best_n) emit();
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
    pool[slot].gi = gi;
    pool[slot].K = k;
    pool[slot].cost = cost;
    memcpy(pool[slot].J, J, sizeof(int) * (size_t)(DEG * k));
    memcpy(pool[slot].S, S, sizeof(int) * (size_t)(DEG * k));
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * grp[pool[i].gi].G;
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

static int pick_fresh(int k, int *gout) {
    int cand[MAXGROUPS], nc = 0;
    for (int gi = 0; gi < ngrp; gi++) {
        long long nn = 2LL * k * grp[gi].G;
        if (nn > best_n && nn <= (long long)best_n + WIN) cand[nc++] = gi;
    }
    if (nc == 0) {
        for (int gi = 0; gi < ngrp; gi++) {
            long long nn = 2LL * k * grp[gi].G;
            if (nn > best_n) cand[nc++] = gi;
        }
    }
    if (nc == 0) return 0;
    *gout = cand[rnd_int(nc)];
    return 1;
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) hm = 0;
    long long total = 2LL * hm;
    int *data = malloc(sizeof(int) * (size_t)(total + 2));
    long long got = 0;
    for (; got < total; got++) {
        if (scanf("%d", &data[got]) != 1) break;
    }
    total = got;

    long long p = 0;
    if (total > 0) {
        int ng = data[p++];
        for (int q = 0; q < ng && q < MAXGROUPS; q++) {
            if (p + 2 > total) break;
            int g = data[p++];
            int id = data[p++];
            if (g < 1 || id < 0 || id >= g) break;
            if (p + (long long)g * g > total) break;
            grp[ngrp].G = g;
            grp[ngrp].id = id;
            grp[ngrp].mul = malloc(sizeof(int) * (size_t)g * (size_t)g);
            memcpy(grp[ngrp].mul, data + p, sizeof(int) * (size_t)g * (size_t)g);
            p += (long long)g * g;
            ngrp++;
        }
    }

    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)(3 * DEG + 3));
        pool[i].S = malloc(sizeof(int) * (size_t)(3 * DEG + 3));
        pool[i].cost = BIGC;
        pool[i].gi = 0;
        pool[i].K = 1;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int ks[5] = {1, 1, 2, 2, 3};
    while (ngrp > 0 && elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            int gi = pool[pi].gi, kk = pool[pi].K;
            setup_group(gi, kk);
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)T);
            build_all();
            perturb(2 + rnd_int(4));
            build_all();
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(gi, kk, bc, bestJ, bestS);
            free_config();
            continue;
        }
        int kk = ks[rnd_int(5)];
        int gi = -1;
        if (!pick_fresh(kk, &gi)) {
            int found = 0;
            for (int a = 1; a <= 3 && !found; a++) {
                if (pick_fresh(a, &gi)) { kk = a; found = 1; }
            }
            if (!found) break;
        }
        setup_group(gi, kk);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(gi, kk, bc, bestJ, bestS);
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
# Group construction in Python. Every group is turned into a multiplication
# table (G, identity index, table as list of lists) and shipped to C.
# ----------------------------------------------------------------------------

def _closure(gens, mul, identity, limit=480):
    """Finite group generated by gens (right multiplication closure), or None if larger than limit."""
    elems = [identity]
    seen = {identity}
    frontier = [identity]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in seen:
                    if len(elems) >= limit:
                        return None
                    seen.add(y)
                    elems.append(y)
                    new.append(y)
        frontier = new
    return elems


def _table(elems, mul, identity):
    """Return (G, identity index, table) for a finite set closed under mul."""
    index = {e: i for i, e in enumerate(elems)}
    tab = [[index[mul(x, y)] for y in elems] for x in elems]
    return len(elems), index[identity], tab


def _perm_mul(p, q):
    return tuple(p[i] for i in q)


def _mat_mul(p):
    def mul(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d * g) % p, (c * f + d * h) % p)
    return mul


def _product_table(a, b):
    """Direct product of two tabled groups given as (order, identity, table)."""
    o1, i1, t1 = a
    o2, i2, t2 = b
    elems = [(x, y) for x in range(o1) for y in range(o2)]

    def mul(u, v):
        return (t1[u[0]][v[0]], t2[u[1]][v[1]])

    return _table(elems, mul, (i1, i2))


def _special_groups():
    """Named small and medium groups as (elements, mul, identity)."""
    out = []
    pm = _perm_mul
    perm_gens = [
        [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)],   # A5
        [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)],   # S5
        [(1, 0, 2, 3), (1, 2, 3, 0)],          # S4
        [(1, 2, 0, 3), (1, 0, 3, 2)],          # A4
        [(1, 0, 2), (1, 2, 0)],                # S3
    ]
    for gens in perm_gens:
        ident = tuple(range(len(gens[0])))
        el = _closure(gens, pm, ident)
        if el is not None:
            out.append((el, pm, ident))
    for p, g in ((5, 2), (7, 3)):
        t_ = tuple([(i + 1) % p for i in range(p)] + [p])
        m_ = tuple([(g * i) % p for i in range(p)] + [p])
        m2 = tuple([(g * g * i) % p for i in range(p)] + [p])
        j_ = tuple([p] + [(p - pow(i, p - 2, p)) % p for i in range(1, p)] + [0])
        ident = tuple(range(p + 1))
        for gens in ([t_, m_, j_], [t_, m2, j_]):
            el = _closure(gens, pm, ident)
            if el is not None:
                out.append((el, pm, ident))
    for p in (5, 7):
        mm = _mat_mul(p)
        el = _closure([(1, 1, 0, 1), (0, p - 1, 1, 0)], mm, (1, 0, 0, 1))
        if el is not None:
            out.append((el, mm, (1, 0, 0, 1)))
    return out


def _candidates(rng, lo, hi):
    """Return (special, semidirect) candidate lists of (order, builder)."""
    special = []
    semi = []

    # Components for direct products: small non-abelian groups times cyclic groups.
    nonab = []
    for gens in ([(1, 2, 0), (1, 0, 2)], [(1, 2, 0, 3), (1, 0, 3, 2)],
                 [(1, 0, 2, 3), (1, 2, 3, 0)], [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]):
        ident = tuple(range(len(gens[0])))
        el = _closure(gens, _perm_mul, ident)
        if el is not None:
            nonab.append(_table(el, _perm_mul, ident))
    cyc = []
    for n in range(2, 13):
        cyc.append(_table(list(range(n)), lambda x, y, n=n: (x + y) % n, 0))

    for elems, mul, ident in _special_groups():
        if lo <= len(elems) <= hi:
            special.append((len(elems),
                            lambda e=elems, m=mul, i=ident: _table(e, m, i)))
    for a in nonab:
        for b in cyc:
            if lo <= a[0] * b[0] <= hi:
                special.append((a[0] * b[0],
                                lambda x=a, y=b: _product_table(x, y)))

    for m in range(2, hi + 1):
        for k in range(1, hi // m + 1):
            order = m * k
            if order < lo:
                continue
            rs_ = [r for r in range(1, m)
                   if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not rs_:
                continue
            rng.shuffle(rs_)
            for r in rs_[:2]:
                mul = lib.semidirect_group(m, k, r)[1]
                semi.append((order,
                             lambda o=order, mu=mul: _table(range(o), mu, 0)))
    rng.shuffle(semi)
    return special, semi


def _select_groups(rng, lo, hi, budget_entries, stop_time):
    """Choose tabled groups in the order window, within a total table-size budget."""
    special, semi = _candidates(rng, lo, hi)
    groups = []
    used = 0
    for order, builder in special + semi:
        if len(groups) >= 60 or time.monotonic() > stop_time:
            break
        if order < lo or order > hi or used + order * order > budget_entries:
            continue
        try:
            groups.append(builder())
            used += order * order
        except Exception:
            continue
    return groups


def _flat_stdin(groups):
    """Pack groups into the flat integer stream read by the C engine."""
    flat = [len(groups)]
    for G, ident, tab in groups:
        flat.append(G)
        flat.append(ident)
        for row in tab:
            flat.extend(row)
    if len(flat) % 2:
        flat.append(0)
    return [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


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
# Driver: baselines, then the group-table annealer with a wide group choice.
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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Group orders that can beat best_n with K = 1, 2, 3 blocks, capped for speed.
    hi = 420
    lo = max(3, min(hi - 1, moore // 30))
    rng = random.Random(seed * 7919 + 13)
    try:
        groups = _select_groups(rng, lo, hi, 1_200_000,
                                start + 0.25 * time_limit)
        pairs = _flat_stdin(groups)
    except Exception:
        groups, pairs = [], []

    elapsed = time.monotonic() - start
    remaining = 0.9 * time_limit - elapsed - 1.5
    if groups and remaining >= 1.0:
        hard = min(remaining + 4.0, time_limit - elapsed - 2.0)
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
