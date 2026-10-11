import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over an arbitrary finite group.
#
# The groups are supplied by Python as permutation generators (see the payload
# in build). C computes each group's multiplication table by closure.
#
# A graph with K base blocks per side and DEG layers has vertices
# A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h, and darts t = (i, j, s) join
# A_{i,g} to B_{j, g*s} for every g. Each layer is a permutation of the blocks,
# so every vertex has degree DEG. Left multiplication is an automorphism, so
# the diameter is at most D iff a BFS of depth D from each of the 2K block
# representatives covers the whole graph.
#
# Search: simulated annealing on the connection set with breakout weights.
# Elite configurations are kept in a pool and re-annealed (iterated local
# search). Groups and block counts are chosen among those whose order gives a
# graph larger than the current best.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXP 48
#define MAXG 800
#define MAXGROUPS 40
#define MAXDEG 16
#define MAXK 3
#define MAXT (MAXDEG * MAXK)
#define MAXN (2 * MAXK * MAXG)
#define HS 4096
#define BIGC 1000000000LL
#define BRK 120
#define ITERS 15000
#define ILS_ITERS 6000
#define POOLMAX 32
#define POOLP 0.5
#define PAYMAX 400000

typedef struct {
    int order;
    int P;
    uint16_t *mul;
} Group;

typedef struct {
    int gi, K;
    long long cost;
    int J[MAXT], S[MAXT];
} Cfg;

static Group grp[MAXGROUPS];
static int ngrp = 0;

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;
static long long MOORE;

static int K, G, T;
static const uint16_t *MT;
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int bestJ[MAXT], bestS[MAXT];
static int adj[MAXN * MAXDEG];
static int cnt[MAXN], stamp[MAXN], fr[MAXN], nx[MAXN];
static int curstamp = 0;
static long long unc[2 * MAXK], wt[2 * MAXK];
static long long wsum = 0, last_w = 0;

static int best_found = 0, best_N = 0, best_gi = 0, best_K = 0;
static int bdJ[MAXT], bdS[MAXT];

static Cfg pool[POOLMAX];
static int npool = 0;

static int pay_buf[PAYMAX];
static int npay = 0;

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

/* ---------------- group closure and multiplication tables ---------------- */

static unsigned hash_perm(const unsigned char *p, int P) {
    unsigned h = 2166136261u;
    for (int i = 0; i < P; i++) {
        h ^= p[i];
        h *= 16777619u;
    }
    return h & (HS - 1);
}

static int ht_lookup(unsigned char el[][MAXP], const int *ht, int P, const unsigned char *c) {
    unsigned h = hash_perm(c, P);
    while (ht[h]) {
        int idx = ht[h] - 1;
        if (memcmp(el[idx], c, (size_t)P) == 0) return idx;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void ht_put(unsigned char el[][MAXP], int *ht, int P, const unsigned char *c, int idx) {
    unsigned h = hash_perm(c, P);
    while (ht[h]) h = (h + 1) & (HS - 1);
    ht[h] = idx + 1;
    memcpy(el[idx], c, (size_t)P);
}

static int build_group(int P, int ng, const int *gens) {
    static unsigned char el[MAXG][MAXP];
    static int ht[HS];
    unsigned char c[MAXP];
    int n = 1;
    if (P < 1 || P > MAXP || ng < 1) return 0;
    for (int g = 0; g < ng; g++)
        for (int i = 0; i < P; i++)
            if (gens[g * P + i] < 0 || gens[g * P + i] >= P) return 0;
    memset(ht, 0, sizeof ht);
    for (int i = 0; i < P; i++) c[i] = (unsigned char)i;
    ht_put(el, ht, P, c, 0);
    for (int a = 0; a < n; a++) {
        for (int g = 0; g < ng; g++) {
            const int *gp = gens + g * P;
            for (int i = 0; i < P; i++) c[i] = (unsigned char)gp[el[a][i]];
            if (ht_lookup(el, ht, P, c) < 0) {
                if (n >= MAXG) return 0;
                ht_put(el, ht, P, c, n);
                n++;
            }
        }
    }
    if (ngrp >= MAXGROUPS) return 0;
    uint16_t *mt = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    if (!mt) return 0;
    for (int a = 0; a < n; a++)
        for (int b = 0; b < n; b++) {
            for (int i = 0; i < P; i++) c[i] = el[a][el[b][i]];
            int idx = ht_lookup(el, ht, P, c);
            if (idx < 0) {
                free(mt);
                return 0;
            }
            mt[a * n + b] = (uint16_t)idx;
        }
    grp[ngrp].order = n;
    grp[ngrp].P = P;
    grp[ngrp].mul = mt;
    ngrp++;
    return 1;
}

static void parse_payload(void) {
    if (npay < 1) return;
    int idx = 0;
    int NG = pay_buf[idx++];
    for (int gi = 0; gi < NG; gi++) {
        if (idx + 2 > npay) break;
        int P = pay_buf[idx], ng = pay_buf[idx + 1];
        idx += 2;
        if (P < 0 || ng < 0 || idx + P * ng > npay) break;
        build_group(P, ng, pay_buf + idx);
        idx += P * ng;
    }
}

static void read_input(void) {
    int n = 0, m = 0;
    npay = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    for (long i = 0; i < 2L * m && npay < PAYMAX; i++) {
        int x;
        if (scanf("%d", &x) != 1) break;
        pay_buf[npay++] = x;
    }
}

static long long moore_bound(int d, int D) {
    if (D == 0 || d == 0) return 1;
    if (d == 1) return D + 1 < 2 ? D + 1 : 2;
    if (d == 2) return 2LL * D;
    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        if (s > 100000000LL) return 200000000LL;
        p *= (d - 1);
    }
    return 2 * s;
}

/* ---------------- configuration and evaluation ---------------- */

static void set_group(int gi, int k) {
    K = k;
    G = grp[gi].order;
    MT = grp[gi].mul;
    T = DEG * K;
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum = 2 * K;
}

static long long bad_cost(int N) {
    for (int r = 0; r < 2 * K; r++) unc[r] = N;
    last_w = BIGC;
    return BIGC;
}

/* Returns the true cost (uncovered ordered pairs over block reps); sets unc[] and last_w. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return bad_cost(N);
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G, s = dS[t];
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + MT[g * G + s];
            if (cnt[a] >= DEG || cnt[b] >= DEG) return bad_cost(N);
            adj[a * DEG + cnt[a]++] = b;
            adj[b * DEG + cnt[b]++] = a;
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
            int *tmp = f;
            f = h;
            h = tmp;
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
            int tmp = p[i];
            p[i] = p[j];
            p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1];
            dJ[t1] = dJ[t2];
            dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
        }
    }
}

/* Annealing on the weighted cost with breakout weight bumps.
   The caller must have just called eval_cost() for the start state.
   Returns the best true cost; the best configuration goes to bestJ/bestS. */
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
                for (int r = 0; r < 2 * K; r++) {
                    if (unc[r] > 0) {
                        wt[r]++;
                        wsum++;
                    }
                }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1];
            dJ[t1] = dJ[t2];
            dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1];
                dJ[t1] = dJ[t2];
                dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
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

static int eligible(int gi, int k) {
    long long N = 2LL * k * grp[gi].order;
    return N > (long long)best_N && N <= MOORE;
}

static void consider_result(int gi, int k, const int *J, const int *S, long long bc) {
    if (bc != 0) return;
    int N = 2 * k * grp[gi].order;
    if (N <= best_N) return;
    best_found = 1;
    best_N = N;
    best_gi = gi;
    best_K = k;
    memcpy(bdJ, J, sizeof(int) * (size_t)(DEG * k));
    memcpy(bdS, S, sizeof(int) * (size_t)(DEG * k));
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
    c->K = k;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)(DEG * k));
    memcpy(c->S, S, sizeof(int) * (size_t)(DEG * k));
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (eligible(pool[i].gi, pool[i].K)) cand[nc++] = i;
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

static int pick_fresh(int *gio, int *ko) {
    static int cg[MAXGROUPS * MAXK], ck[MAXGROUPS * MAXK];
    int nc = 0;
    for (int gi = 0; gi < ngrp; gi++)
        for (int k = 1; k <= MAXK; k++)
            if (eligible(gi, k)) {
                cg[nc] = gi;
                ck[nc] = k;
                nc++;
            }
    if (nc == 0) return 0;
    int c = rnd_int(nc);
    *gio = cg[c];
    *ko = ck[c];
    return 1;
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
    best_N = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MOORE = moore_bound(DEG, DIAM);
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    read_input();
    parse_payload();

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            Cfg c = pool[pi];
            set_group(c.gi, c.K);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            perturb(2 + rnd_int(4));
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            consider_result(c.gi, c.K, bestJ, bestS, bc);
            pool_add(c.gi, c.K, bc, bestJ, bestS);
            continue;
        }
        int gi = 0, k = 1;
        if (!pick_fresh(&gi, &k)) break;
        set_group(gi, k);
        random_init();
        long long cst = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cst);
        consider_result(gi, k, bestJ, bestS, bc);
        pool_add(gi, k, bc, bestJ, bestS);
    }

    if (best_found) {
        int Kb = best_K, Tb = DEG * Kb, Gb = grp[best_gi].order;
        const uint16_t *mt = grp[best_gi].mul;
        printf("%d %d\n", 2 * Kb * Gb, Tb * Gb);
        for (int t = 0; t < Tb; t++) {
            int i = t % Kb, j = bdJ[t], s = bdS[t];
            for (int g = 0; g < Gb; g++)
                printf("%d %d\n", i * Gb + g, (Kb + j) * Gb + (int)mt[g * Gb + s]);
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Permutation groups given by generators (points 0..P-1). Passed to C as payload.
# ----------------------------------------------------------------------------

def _union(a, b):
    """Direct product of permutation groups (disjoint union of their actions)."""
    pa, ga = a
    pb, gb = b
    gens = ([list(g) + [pa + i for i in range(pb)] for g in ga]
            + [list(range(pa)) + [pa + x for x in h] for h in gb])
    return pa + pb, gens


def _cyc(m):
    return m, [[(i + 1) % m for i in range(m)]]


def _sym(n):
    t = list(range(n))
    t[0], t[1] = 1, 0
    return n, [t, [(i + 1) % n for i in range(n)]]


def _alt(n):
    """A_n for odd n, generated by a 3-cycle and an n-cycle."""
    c = list(range(n))
    c[0], c[1], c[2] = 1, 2, 0
    return n, [c, [(i + 1) % n for i in range(n)]]


def _psl2(q):
    """PSL(2,q) (= SL(2,q) for even q) acting on the projective line; INF = index q."""
    F = lib.GF(q)
    INF = q
    w = F.primitive_element()
    wi = F.inv(w)

    def mob(a, b, c, d):
        perm = []
        for x in range(q + 1):
            if x == INF:
                y = INF if c == 0 else F.mul(a, F.inv(c))
            else:
                den = F.add(F.mul(c, x), d)
                if den == 0:
                    y = INF
                else:
                    y = F.mul(F.add(F.mul(a, x), b), F.inv(den))
            perm.append(y)
        return perm

    gens = [mob(1, 1, 0, 1), mob(1, w, 0, 1), mob(1, 0, 1, 1), mob(w, 0, 0, wi)]
    return q + 1, gens


def _agl1(q):
    """Affine group AGL(1,q): x -> a x + b on GF(q)."""
    F = lib.GF(q)
    p, k = F.p, F.k
    gens = [[F.add(x, p ** i) for x in range(q)] for i in range(k)]
    w = F.primitive_element()
    gens.append([F.mul(w, x) for x in range(q)])
    return q, gens


def _agl23():
    """AGL(2,3), order 432, acting on GF(3)^2 with index x0 + 3*x1."""
    def pt(i):
        return (i % 3, i // 3)

    def idx(x0, x1):
        return (x0 % 3) + 3 * (x1 % 3)

    def perm(f):
        return [idx(*f(*pt(i))) for i in range(9)]

    gens = [
        perm(lambda x0, x1: (x0 + 1, x1)),
        perm(lambda x0, x1: (x0, x1 + 1)),
        perm(lambda x0, x1: (x0 + x1, x1)),
        perm(lambda x0, x1: (x0, x0 + x1)),
        perm(lambda x0, x1: (2 * x0, x1)),
    ]
    return 9, gens


def _group_families():
    fams = [_alt(5), _sym(5), _sym(6), _psl2(5), _psl2(7), _psl2(8), _psl2(9), _psl2(11),
            _agl23()]
    for q in (7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27):
        fams.append(_agl1(q))
    fams.append(_union(_alt(5), _cyc(6)))     # order 360
    fams.append(_union(_alt(5), _cyc(7)))     # order 420
    fams.append(_union(_sym(5), _cyc(3)))     # order 360
    fams.append(_union(_psl2(7), _cyc(3)))    # order 504
    fams.append(_union(_cyc(19), _cyc(19)))   # order 361 (abelian control)
    return fams


def _payload(fams):
    """Flat int list, sent as pairs in the stdin graph slot: [count, (P, ng, gens...)...]."""
    flat = [len(fams)]
    for P, gens in fams:
        flat += [P, len(gens)]
        for g in gens:
            flat.extend(int(x) for x in g)
    if len(flat) % 2:
        flat.append(0)
    pairs = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
    return (0, pairs)


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
# Driver: baselines, then the C search over bi-Cayley lifts of many groups.
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

    # Leave a margin for compile, process startup, parsing and validation.
    remaining = 0.88 * time_limit - (time.monotonic() - start) - 3.0
    if remaining >= 2.0 and 1 <= d <= 16:
        try:
            fams = _group_families()
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            stdin_graph=_payload(fams), timeout=remaining + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
