import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an ARBITRARY finite group, given as a full
# multiplication table from Python. Each group is a bi-lift template:
# A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart (i, j, s) joins A_i,g to
# B_j,(g*s). Each layer is a permutation, so every vertex has degree DEG.
# Left multiplication is an automorphism, so diameter <= D iff BFS of depth D
# from the 2K block representatives (the identity of each block) covers all.
#
# Input (via lib.graph_to_text): header "NG M", then 2M integers forming a
# flat payload: for each group, its order G followed by G*G table entries
# (row-major, entry x*G+y = x*y). Groups without a left identity are skipped.
#
# Search: simulated annealing with breakout weights, plus an elite pool with
# iterated local search. Each fresh run picks a random group and the smallest
# K that can beat the current best order (with a little slack).
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
#define KMAX 32
#define MAXNG 64

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

static int DEG, DIAM;
static int NG = 0;
static int gord[MAXNG];
static int gid[MAXNG];
static int *gtab[MAXNG];
static int cur_g = 0;
static int K, T, G;
static const int *MT;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;
static long long *wt = NULL;
static long long *unc = NULL;
static long long wsum_w = 0;
static long long last_w = 0;

typedef struct {
    int g, K;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

static inline int gmul(int x, int y) { return MT[x * G + y]; }

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static long long fail_cost(void) {
    for (int r = 0; r < 2 * K; r++) unc[r] = 0;
    last_w = BIGC;
    return BIGC;
}

/* Returns the true cost (sum of uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return fail_cost();
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            if (cnt[a] >= DEG || cnt[b] >= DEG) return fail_cost();
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    for (int v = 0; v < N; v++)
        if (cnt[v] != DEG) return fail_cost();

    long long total = 0;
    int ID = gid[cur_g];
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G + ID;
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
    cur_g = gi;
    G = gord[gi];
    MT = gtab[gi];
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
   Caller must have just called eval_cost(). Returns the best true cost;
   the best state goes to bestJ/bestS. */
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

/* A zero-cost run is a valid graph: load it and emit if it beats the best so far. */
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
    c->g = cur_g;
    c->K = K;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

/* Pick an elite entry whose order still beats the best; best of 3 samples. */
static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * gord[pool[i].g];
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2 || hm < 0) {
        printf("0 0\n");
        return 0;
    }
    long long total = 2LL * hm;
    int *flat = malloc(sizeof(int) * (size_t)(total + 2));
    for (long long i = 0; i < total; i++)
        if (scanf("%d", &flat[i]) != 1) flat[i] = 0;

    long long idx = 0;
    for (int gi = 0; gi < hn && NG < MAXNG; gi++) {
        if (idx >= total) break;
        long long go = flat[idx++];
        if (go < 1 || go > 1000) break;
        if (idx + go * go > total) break;
        int *tab = flat + idx;
        int ok = 1;
        for (long long q = 0; q < go * go && ok; q++)
            if (tab[q] < 0 || tab[q] >= go) ok = 0;
        int id = -1;
        if (ok) {
            for (int e = 0; e < go && id < 0; e++) {
                int good = 1;
                for (int y = 0; y < go && good; y++)
                    if (tab[(long long)e * go + y] != y) good = 0;
                if (good) id = e;
            }
        }
        if (ok && id >= 0) {
            gord[NG] = (int)go;
            gid[NG] = id;
            gtab[NG] = malloc(sizeof(int) * (size_t)(go * go));
            memcpy(gtab[NG], tab, sizeof(int) * (size_t)(go * go));
            NG++;
        }
        idx += go * go;
    }
    free(flat);
    if (NG == 0) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)(DEG * KMAX));
        pool[i].S = malloc(sizeof(int) * (size_t)(DEG * KMAX));
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg c = pool[pi];
            setup_group(c.g, c.K);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
            continue;
        }

        /* Fresh random lift over a random group, with the smallest K that can beat the best. */
        int gi = rnd_int(NG);
        int gg = gord[gi];
        int kmin = best_n / (2 * gg) + 1;
        int k = kmin + (rnd_unit() < 0.25 ? 1 : 0);
        if (k > KMAX) continue;
        setup_group(gi, k);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
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
# Group tables (Python side). A group is a list of rows: rows[x][y] = x*y.
# ----------------------------------------------------------------------------

def _cyclic_rows(m):
    return [[(x + y) % m for y in range(m)] for x in range(m)]


def _from_fn(n, mul):
    return [[mul(x, y) for y in range(n)] for x in range(n)]


def _semidirect_rows(m, k, r):
    order, mul, _ = lib.semidirect_group(m, k, r)
    return _from_fn(order, mul)


def _heisenberg_rows(p):
    """Heisenberg group mod p (order p^3): (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    n = p ** 3
    trip = [(x // (p * p), (x // p) % p, x % p) for x in range(n)]
    rows = []
    for a, b, c in trip:
        row = []
        for a2, b2, c2 in trip:
            row.append(((a + a2) % p) * p * p + ((b + b2) % p) * p + (c + c2 + a * b2) % p)
        rows.append(row)
    return rows


def _agl_cyc_rows(p, m):
    """AGL(1,p) x Z_m for prime p: affine maps x -> u x + v with u != 0, times a cyclic factor."""
    aff = [(u, v) for u in range(1, p) for v in range(p)]
    idx = {e: i for i, e in enumerate(aff)}
    atab = [[idx[((u * u2) % p, (u * v2 + v) % p)] for (u2, v2) in aff] for (u, v) in aff]
    n = len(aff) * m
    rows = []
    for x in range(n):
        xa, xz = divmod(x, m)
        row = []
        for y in range(n):
            ya, yz = divmod(y, m)
            row.append(atab[xa][ya] * m + (xz + yz) % m)
        rows.append(row)
    return rows


def _perm_rows(gens, n_pts, cap=400):
    """Permutation group generated by gens (tuples on n_pts points), as a multiplication table."""
    ident = tuple(range(n_pts))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(x[i] for i in g)
                if y not in index:
                    if len(elems) >= cap:
                        raise ValueError("group too large")
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return [[index[tuple(x[i] for i in y)] for y in elems] for x in elems]


def _direct(r1, r2):
    n1, n2 = len(r1), len(r2)
    rows = []
    for x in range(n1 * n2):
        x1, x2 = divmod(x, n2)
        row = []
        for y in range(n1 * n2):
            y1, y2 = divmod(y, n2)
            row.append(r1[x1][y1] * n2 + r2[x2][y2])
        rows.append(row)
    return rows


def _a5():
    return _perm_rows(((1, 2, 0, 3, 4), (1, 2, 3, 4, 0)), 5)


def _s5():
    return _perm_rows(((1, 0, 2, 3, 4), (1, 2, 3, 4, 0)), 5)


def _s4():
    return _perm_rows(((1, 0, 2, 3), (1, 2, 3, 0)), 4)


def _candidate_groups(start, time_limit):
    """Non-cyclic and non-metacyclic groups of orders that give useful lifts for d=6, D=5."""
    makers = [
        lambda: _heisenberg_rows(7),              # order 343: K=1 gives 686 vertices
        lambda: _direct(_a5(), _cyclic_rows(6)),  # order 360
        lambda: _direct(_s5(), _cyclic_rows(3)),  # order 360
        lambda: _direct(_s4(), _cyclic_rows(15)), # order 360
        lambda: _a5(),                            # order 60
        lambda: _s5(),                            # order 120
        lambda: _semidirect_rows(43, 2, 42),      # dihedral of order 86
        lambda: _semidirect_rows(45, 2, 44),      # dihedral of order 90
        lambda: _agl_cyc_rows(11, 1),             # order 110
        lambda: _agl_cyc_rows(7, 5),              # order 210
        lambda: _heisenberg_rows(5),              # order 125
    ]
    out = []
    for make in makers:
        if time.monotonic() - start > 0.2 * time_limit:
            break
        try:
            rows = make()
        except Exception:
            continue
        n = len(rows)
        if n < 2 or n > 400:
            continue
        if not all(len(set(r)) == n for r in rows):
            continue
        out.append(rows)
    return out


def _payload(groups):
    """Flat integer payload for the C engine, packed as graph-text edges."""
    flat = []
    for rows in groups:
        flat.append(len(rows))
        for row in rows:
            flat.extend(row)
    if len(flat) % 2:
        flat.append(0)
    edges = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
    return len(groups), edges


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
# Driver: baselines, then one C run over table-encoded groups.
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

    groups = _candidate_groups(start, time_limit)

    # Give the C search nearly all of the budget. The wall-clock deadline inside C
    # keeps the run on time; the margin covers compilation, parsing and validation.
    remaining = 0.93 * time_limit - (time.monotonic() - start) - 1.0
    if groups and remaining >= 3.0:
        try:
            payload = _payload(groups)
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            stdin_graph=payload, timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
