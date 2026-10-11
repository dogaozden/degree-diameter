import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley / voltage lifts over an arbitrary finite group given by
# its multiplication table (read from stdin). Each base vertex pair (A_i, B_j)
# is joined by darts (i, j, s): A_{i,g} ~ B_{j, g*s}. Left multiplication is an
# automorphism, so diameter <= D iff BFS of depth D from one vertex per block
# (2K blocks) reaches everything. Simulated annealing with breakout weights and
# an elite-pool iterated local search, as in the previous engine, but the group
# is no longer restricted to metacyclic semidirect products.
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

static int DEG, DIAM, K, G, T, N;
static int *MT;
static int *dI, *dJ, *dS, *bestJ, *bestS;
static int *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;

typedef struct { long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

/* right multiplication by dart s: g -> g*s */
static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = MT[g * G + s];
}

/* Returns the true cost: total uncovered vertices over the 2K block representatives.
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = N;
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
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) { wt[b] = 1; unc[b] = 0; }
    wsum_w = 2 * K;
    curstamp = 0;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)T);
        pool[i].S = malloc(sizeof(int) * (size_t)T);
        pool[i].cost = BIGC;
    }
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

static void random_init(void) {
    int *p = malloc(sizeof(int) * (size_t)K);
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
    free(p);
    for (int t = 0; t < T; t++) build_perm(t);
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

/* A zero-cost configuration is a valid graph of order N. Returns 1 when a
   valid graph was found (the search then stops; the group order is fixed). */
static int finish_run(long long bc) {
    if (bc != 0) return 0;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (N > best_n) emit();
    return 1;
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

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time K best_n < table\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    best_n = argc > 6 ? atoi(argv[6]) : 0;
    best_m = 0;
    if (DEG < 1 || DIAM < 1 || K < 1) {
        printf("0 0\n");
        return 0;
    }

    /* Group table: header "G G*G", then lines "x*G+y  x*y". */
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || (long long)m != (long long)n * n) {
        printf("0 0\n");
        return 0;
    }
    G = n;
    MT = malloc(sizeof(int) * (size_t)m);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= m || v < 0 || v >= G) {
            printf("0 0\n");
            return 0;
        }
        MT[u] = v;
    }

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    alloc_all();

    while (elapsed() < DEADLINE) {
        int found = 0;
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            found = finish_run(bc);
            pool_add(bc, bestJ, bestS);
        } else {
            random_init();
            long long cst = eval_cost();
            long long bc = run_sa(ITERS, 1.0, cst);
            found = finish_run(bc);
            pool_add(bc, bestJ, bestS);
        }
        if (found) break;
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
# Group constructions (multiplication tables, flat list: table[x*G + y] = x*y).
# ----------------------------------------------------------------------------

_A5_GENS = [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]
_S5_GENS = _A5_GENS + [(1, 0, 2, 3, 4)]
_A6_GENS = [(1, 2, 0, 3, 4, 5), (0, 2, 3, 4, 5, 1)]


def _perm_table(gens):
    """Multiplication table of the permutation group generated by gens (x*y)[i] = y[x[i]]."""
    n = len(gens[0])
    ident = tuple(range(n))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[i] for i in x)
                if y not in index:
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    G = len(elems)
    table = [0] * (G * G)
    for xi, x in enumerate(elems):
        base = xi * G
        for yi, y in enumerate(elems):
            table[base + yi] = index[tuple(y[i] for i in x)]
    return G, table


def _cyclic_product(G, table, k):
    """Direct product of a group table with Z_k; element (g, c) has index g*k + c."""
    NG = G * k
    t = [0] * (NG * NG)
    for g in range(G):
        for c in range(k):
            row = (g * k + c) * NG
            for h in range(G):
                gh = table[g * G + h]
                for e in range(k):
                    t[row + h * k + e] = gh * k + (c + e) % k
    return NG, t


def _heisenberg(p):
    """Heisenberg group of exponent p over Z_p (p odd): (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    G = p ** 3
    p2 = p * p

    def dec(x):
        a, rem = divmod(x, p2)
        b, c = divmod(rem, p)
        return a, b, c

    els = [dec(x) for x in range(G)]
    table = [0] * (G * G)
    for x in range(G):
        a, b, c = els[x]
        base = x * G
        for y in range(G):
            a2, b2, c2 = els[y]
            table[base + y] = ((a + a2) % p) * p2 + ((b + b2) % p) * p + (c + c2 + a * b2) % p
    return G, table


def _group_table(name):
    """Return (order, table) for a named group, or (0, []) if unknown."""
    if name == "H7":
        return _heisenberg(7)
    if name == "A6":
        return _perm_table(_A6_GENS)
    if name == "A5":
        return _perm_table(_A5_GENS)
    if name == "S5":
        return _perm_table(_S5_GENS)
    if name == "A5xZ3":
        return _cyclic_product(*_perm_table(_A5_GENS), 3)
    if name == "A5xZ2":
        return _cyclic_product(*_perm_table(_A5_GENS), 2)
    return 0, []


# (name, base vertices per side K, group order, scheduling weight)
_SPECS = [
    ("H7", 1, 343, 0.30),
    ("A6", 1, 360, 0.25),
    ("A5xZ3", 2, 180, 0.15),
    ("S5", 3, 120, 0.12),
    ("A5xZ2", 3, 120, 0.08),
    ("A5", 6, 60, 0.10),
]


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines, then group-lift searches in C (one group per run).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
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

    bound = lib.moore_bound(d, D)
    if best_n >= bound:
        return best

    avail = 0.88 * time_limit - (time.monotonic() - start) - 2.5
    specs = []
    for name, K, order, w in _SPECS:
        size = 2 * K * order
        if best_n < size <= bound:
            specs.append((name, K, order, w))

    remaining_w = sum(s[3] for s in specs)
    for name, K, order, w in specs:
        if remaining_w <= 0:
            break
        left = avail - (time.monotonic() - start)
        if left < 1.5:
            break
        budget = left * w / remaining_w
        remaining_w -= w
        if budget < 1.0:
            continue
        try:
            G, table = _group_table(name)
            if G != order or len(table) != G * G:
                continue
            pairs = [(idx, table[idx]) for idx in range(G * G)]
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", K, best_n],
                            stdin_graph=(G, pairs), timeout=budget + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
