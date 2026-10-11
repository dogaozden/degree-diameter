import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction family (bold change): voltage lifts of a bipartite base
# with UNBALANCED block counts. The base has KA A-blocks of degree a and KB
# B-blocks of degree b, with a*KA == b*KB, so an A-block may have a different
# degree from a B-block (e.g. degrees 6 and 5 on the two sides, with 5 A-blocks
# and 6 B-blocks). Blocks are copies of a group H = Z_m x| Z_k2 (order G):
#   A_i,g = i*G + g,   B_j,h = (KA + j)*G + h.
# Dart t = (i, j, s) joins A_i,g to B_j,g*s for all g. A-block i owns darts
# i*a .. i*a+a-1; the B-side multiset is fixed (each B_j receives b darts) and
# is changed only by swaps, so every degree stays exact.
#
# Left multiplication by h is an automorphism, so diameter <= D iff a BFS of
# depth D from each block representative covers the whole graph.
#
# Search: simulated annealing on the weighted count of uncovered pairs, with
# breakout weights, plus an elite pool used for iterated local search. Shapes
# (a, b, KA, KB) are drawn at random, favouring near-full degrees on both sides.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXNB 10
#define RMAX 16
#define POOLMAX 32
#define POOLP 0.5
#define BRK 120
#define ITERS 5000
#define ILS_ITERS 2500

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
static int A_, B_, KA, KB, NB, TA, M, K2, G, R;
static int Rpow[RMAX];
static int *dI, *dJ, *dS, *perm, *bJ, *bS, *adj, *cnt, *stamp, *fr, *nx;
static long long *wt, *unc;
static long long wsum, last_w;
static int curstamp;
static int best_n, best_m;
static int *best_e = NULL;

typedef struct {
    int a, b, ka, kb, m, k2, r;
    long long cost;
    int *J, *S;
} Cfg;

typedef struct { int a, b, ka, kb; } Shape;

static Cfg pool[POOLMAX];
static int npool = 0;
static Shape shapes[4096];
static int nshapes = 0;
static int fav[4096];
static int nfav = 0;

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

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void free_cfg(void) {
    free(dI); free(dJ); free(dS); free(bJ); free(bS); free(perm);
    free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    dI = dJ = dS = bJ = bS = perm = adj = cnt = stamp = fr = nx = NULL;
    wt = unc = NULL;
}

static void setup_cfg(int pa, int pb, int pka, int pkb, int pm, int pk2, int pr) {
    A_ = pa; B_ = pb; KA = pka; KB = pkb; NB = pka + pkb;
    M = pm; K2 = pk2; R = pr; G = pm * pk2;
    TA = A_ * KA;
    int N = NB * G;
    dI = malloc(sizeof(int) * (size_t)TA);
    dJ = malloc(sizeof(int) * (size_t)TA);
    dS = malloc(sizeof(int) * (size_t)TA);
    bJ = malloc(sizeof(int) * (size_t)TA);
    bS = malloc(sizeof(int) * (size_t)TA);
    perm = malloc(sizeof(int) * (size_t)TA * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)NB);
    unc = malloc(sizeof(long long) * (size_t)NB);
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int q = 1; q < K2; q++) Rpow[q] = (int)((long long)Rpow[q - 1] * R % M);
    for (int t = 0; t < TA; t++) dI[t] = t / A_;
    for (int r = 0; r < NB; r++) { wt[r] = 1; unc[r] = 0; }
    wsum = NB;
}

static void swapJ(int t1, int t2) {
    int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
}

/* Each B-block value appears exactly B_ times (TA = B_ * KB). */
static void random_J(void) {
    for (int t = 0; t < TA; t++) dJ[t] = t / B_;
    for (int i = TA - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        swapJ(i, j);
    }
}

static void random_init(void) {
    random_J();
    for (int t = 0; t < TA; t++) {
        dS[t] = rnd_int(G);
        build_perm(t);
    }
}

/* Returns the true cost (sum of uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    int N = NB * G;
    for (int t1 = 0; t1 < TA; t1++)
        for (int t2 = t1 + 1; t2 < TA; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < NB; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < TA; t++) {
        int ai = dI[t] * G, bj = (KA + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0, w = 0;
    for (int r = 0; r < NB; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = r * G;
        stamp[r * G] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                int u = f[q];
                const int *au = adj + (size_t)u * DEG;
                int dg = cnt[u];
                for (int e = 0; e < dg; e++) {
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

static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
        if (rnd_unit() < 0.4) {
            int t1 = rnd_int(TA), t2 = rnd_int(TA);
            if (dJ[t1] != dJ[t2]) swapJ(t1, t2);
        } else {
            int t = rnd_int(TA);
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < TA; t++) build_perm(t);
}

/* Annealing on the weighted cost with breakout weight bumps. The caller has
   just run eval_cost() so cost and last_w describe the start state. Returns the
   best true cost; the best state is kept in bJ/bS. */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost, wcur = last_w, prevc = cost;
    memcpy(bJ, dJ, sizeof(int) * (size_t)TA);
    memcpy(bS, dS, sizeof(int) * (size_t)TA);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < NB; r++)
                    if (unc[r] > 0) { wt[r]++; wsum++; }
                wcur = 0;
                for (int r = 0; r < NB; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum / NB;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (rnd_unit() < 0.25) {
            int t1 = rnd_int(TA), t2 = rnd_int(TA);
            if (dJ[t1] == dJ[t2]) continue;
            swapJ(t1, t2);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                swapJ(t1, t2);
            }
        } else {
            int t = rnd_int(TA);
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
            memcpy(bJ, dJ, sizeof(int) * (size_t)TA);
            memcpy(bS, dS, sizeof(int) * (size_t)TA);
        }
    }
    return bestc;
}

static void emit(void) {
    int m = TA * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < TA; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (KA + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = NB * G;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the record. */
static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bJ, sizeof(int) * (size_t)TA);
        memcpy(dS, bS, sizeof(int) * (size_t)TA);
        for (int t = 0; t < TA; t++) build_perm(t);
        if (NB * G > best_n) emit();
    }
}

static void pool_add(long long cost) {
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
    c->a = A_; c->b = B_; c->ka = KA; c->kb = KB;
    c->m = M; c->k2 = K2; c->r = R; c->cost = cost;
    memcpy(c->J, bJ, sizeof(int) * (size_t)TA);
    memcpy(c->S, bS, sizeof(int) * (size_t)TA);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = (long long)(pool[i].ka + pool[i].kb) * pool[i].m * pool[i].k2;
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
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    best_e = NULL;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)(DEG * MAXNB + 1));
        pool[i].S = malloc(sizeof(int) * (size_t)(DEG * MAXNB + 1));
        pool[i].cost = BIGC;
    }

    /* Enumerate shapes: a*KA == b*KB, both block counts >= 1, total blocks <= MAXNB. */
    for (int a = 1; a <= DEG; a++)
        for (int b = 1; b <= DEG; b++)
            for (int ka = 1; ka < MAXNB; ka++)
                for (int kb = 1; ka + kb <= MAXNB; kb++)
                    if (a * ka == b * kb && nshapes < 4096) {
                        shapes[nshapes].a = a;
                        shapes[nshapes].b = b;
                        shapes[nshapes].ka = ka;
                        shapes[nshapes].kb = kb;
                        if (a >= DEG - 1 && b >= DEG - 1) fav[nfav++] = nshapes;
                        nshapes++;
                    }

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        if (nshapes == 0) break;
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search from an elite configuration. */
            Cfg c = pool[pi];
            setup_cfg(c.a, c.b, c.ka, c.kb, c.m, c.k2, c.r);
            memcpy(dJ, c.J, sizeof(int) * (size_t)TA);
            memcpy(dS, c.S, sizeof(int) * (size_t)TA);
            for (int t = 0; t < TA; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc);
            free_cfg();
            continue;
        }

        /* Fresh random lift with a random shape and a group near the target order. */
        int si;
        if (nfav > 0 && rnd_unit() < 0.6) si = fav[rnd_int(nfav)];
        else si = rnd_int(nshapes);
        int pa = shapes[si].a, pb = shapes[si].b;
        int pka = shapes[si].ka, pkb = shapes[si].kb;
        int kk = pka + pkb;
        int gmin = best_n / kk + 1;
        int spread = gmin / 6 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[16], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
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
                m = g;
                r = 1;
            }
        }
        setup_cfg(pa, pb, pka, pkb, m, c2, r);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc);
        free_cfg();
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
    """W(q) for a small prime power q with q + 1 <= d (kept small for Python speed)."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C search over unbalanced voltage lifts.
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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Leave headroom for compile, parsing and validation.
    remaining = 0.88 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
