import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bipartite voltage lifts of the semidirect products
# Z_M x|_r Z_K2 over a base of K A-vertices and K B-vertices, with K in 1..4.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for every g. Each layer is a permutation of the K base
# pairs, so every vertex has degree DEG. Left multiplication is an
# automorphism, so diameter <= D iff a BFS of depth D from each of the 2K block
# representatives reaches every vertex.
#
# Search: tabu search over single-voltage and within-layer target-swap moves,
# with aspiration and random restarts from the best state. About 30% of runs
# use simulated annealing on the same move set. The C engine keeps the best
# zero-cost configuration with the largest group order.
#
# Safety: Python takes the best of K_{d,d}, the projective-plane incidence graph
# and (for D >= 4) the generalized quadrangle W(q). The C output replaces it
# only if lib.is_valid accepts it.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 4
#define BIGC 1000000000LL
#define CAND 16
#define TABU_ITERS 2500
#define ANNEAL_ITERS 6000
#define STALL 400
#define TABU_TENURE_BASE 4
#define TABU_TENURE_RAND 8

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

static int DEG, DIAM, K, K2, M, G, T, R, NN;
static int *Rp;
static int *dI, *dJ, *dS, *bJ, *bS, *tabu;
static int *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

typedef struct {
    int type, t1, t2, oldv, newv;
} Move;

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
    long long ra = ((long long)a + (long long)Rp[b] * c) % M;
    int rb = (b + e) % K2;
    return (int)ra * K2 + rb;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void alloc_config(void) {
    NN = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bJ = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
    tabu = calloc((size_t)T, sizeof(int));
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)NN * DEG);
    cnt = malloc(sizeof(int) * (size_t)NN);
    stamp = calloc((size_t)NN, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NN);
    nx = malloc(sizeof(int) * (size_t)NN);
    Rp = malloc(sizeof(int) * (size_t)K2);
    curstamp = 0;
    Rp[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rp[b] = (int)((long long)Rp[b - 1] * R % M);
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bJ); free(bS); free(tabu);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rp);
    dI = dJ = dS = bJ = bS = perm = adj = cnt = stamp = fr = nx = Rp = NULL;
    tabu = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

/* True cost: uncovered ordered pairs summed over the 2K block representatives.
   Zero means every block is within distance DIAM of everything. */
static long long eval_cost(void) {
    for (int a = 0; a < T; a++)
        for (int b = a + 1; b < T; b++)
            if (dI[a] == dI[b] && dJ[a] == dJ[b] && dS[a] == dS[b])
                return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)NN);
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
            memset(stamp, 0, sizeof(int) * (size_t)NN);
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
        total += NN - count;
    }
    return total;
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

/* Type 0: change the voltage of dart t1. Type 1: swap the targets of two darts in one layer. */
static int gen_move(Move *m) {
    if (K > 1 && rnd_unit() < 0.25) {
        int l = rnd_int(DEG);
        int i1 = rnd_int(K), i2 = rnd_int(K);
        if (i1 == i2) return 0;
        m->type = 1;
        m->t1 = l * K + i1;
        m->t2 = l * K + i2;
        return 1;
    }
    int t = rnd_int(T);
    int nv = rnd_int(G);
    if (nv == dS[t]) return 0;
    m->type = 0;
    m->t1 = t;
    m->t2 = -1;
    m->oldv = dS[t];
    m->newv = nv;
    return 1;
}

static void apply_move(const Move *mv, int fwd) {
    if (mv->type == 0) {
        dS[mv->t1] = fwd ? mv->newv : mv->oldv;
        build_perm(mv->t1);
    } else {
        int tmp = dJ[mv->t1];
        dJ[mv->t1] = dJ[mv->t2];
        dJ[mv->t2] = tmp;
    }
}

static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
        Move m;
        if (gen_move(&m)) apply_move(&m, 1);
    }
}

/* Tabu search (use_tabu) or simulated annealing on the same moves.
   The best state is kept in bJ/bS. Returns its cost. */
static long long run_search(int use_tabu, int iters) {
    long long cur = eval_cost();
    long long best = cur;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    memset(tabu, 0, sizeof(int) * (size_t)T);
    int stall = 0;
    for (int it = 1; it <= iters && best > 0; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        if (use_tabu) {
            Move bm;
            long long bc = 0;
            int have = 0;
            for (int c = 0; c < CAND; c++) {
                Move m;
                if (!gen_move(&m)) continue;
                apply_move(&m, 1);
                long long v = eval_cost();
                apply_move(&m, 0);
                int isTabu = tabu[m.t1] > it || (m.type == 1 && tabu[m.t2] > it);
                if (isTabu && v >= best) continue;
                if (!have || v < bc || (v == bc && rnd_unit() < 0.5)) {
                    bm = m; bc = v; have = 1;
                }
            }
            if (!have) continue;
            apply_move(&bm, 1);
            cur = bc;
            int ten = TABU_TENURE_BASE + rnd_int(TABU_TENURE_RAND);
            tabu[bm.t1] = it + ten;
            if (bm.type == 1) tabu[bm.t2] = it + ten;
        } else {
            Move m;
            if (!gen_move(&m)) continue;
            apply_move(&m, 1);
            long long v = eval_cost();
            double temp = 1.5 * (1.0 - (double)it / iters) + 0.05;
            if (v <= cur || rnd_unit() < exp(-(double)(v - cur) / temp)) cur = v;
            else apply_move(&m, 0);
        }
        if (cur < best) {
            best = cur;
            memcpy(bJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bS, dS, sizeof(int) * (size_t)T);
            stall = 0;
        } else if (use_tabu && ++stall > STALL) {
            memcpy(dJ, bJ, sizeof(int) * (size_t)T);
            memcpy(dS, bS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(3);
            cur = eval_cost();
            stall = 0;
            memset(tabu, 0, sizeof(int) * (size_t)T);
        }
    }
    return best;
}

/* Store a zero-cost configuration as the output graph. */
static void store_best(const int *J, const int *S) {
    int m = T * G;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            e[idx++] = dI[t] * G + g;
            e[idx++] = (K + J[t]) * G + gmul(g, S[t]);
        }
    }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = 2 * K * G;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [min_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = min_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[6] = {1, 2, 2, 3, 3, 4};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(6)];
        int gmin = best_n / (2 * k) + 1;
        int g = gmin + rnd_int(gmin / 8 + 2);
        if (g < 2) g = 2;
        int opts[16], no = 0;
        for (int c = 1; c <= 12 && c <= g; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = no ? opts[rnd_int(no)] : 1;
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
        setup_group(k, c2, m, r);
        random_init();
        int use_tabu = rnd_unit() < 0.7;
        long long bc = run_search(use_tabu, use_tabu ? TABU_ITERS : ANNEAL_ITERS);
        if (bc == 0 && 2 * k * g > best_n) store_best(bJ, bS);
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
# Driver: baselines in Python, then the C tabu/annealing lift search.
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

    # Most of the budget goes to the C search; leave room for compile, parsing and validation.
    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
