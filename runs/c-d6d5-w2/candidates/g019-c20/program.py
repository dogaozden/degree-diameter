import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: a different search over the same lift space as the parent.
#
# Groups: semidirect products Z_m x| Z_k2 with k2 | 12 and r^k2 = 1 mod m.
# Base: K A-vertices and K B-vertices (K in 1..4). Dart t = l*K + i (layer l,
# source i) joins A_{i,g} to B_{J_t, g*s_t} for all g. Each layer's J is a
# permutation, so every vertex has degree DEG. Left multiplication is an
# automorphism, so diameter <= DIAM iff BFS of depth DIAM from the 2K block
# representatives covers every vertex.
#
# Search (new operators, in place of the parent's breakout/ILS driver):
#   1. Layer crossover (genetic step): two elite configurations of the SAME
#      group are mixed layer by layer. Copying whole layers keeps every
#      layer a permutation, so children stay DEG-regular.
#   2. Short annealing polish on the true cost (uncovered ordered pairs).
#   3. Elites are kept by eligibility first: a pool entry whose group order no
#      longer beats the best order found is replaced before any other entry.
#   4. Fresh random lifts over groups near the target order, as a fallback.
#
# Output: the best valid graph strictly larger than the start order, or "0 0".
# The Python driver always keeps and validates a fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXK 4
#define POOLMAX 40
#define SA_FRESH 5000
#define SA_ILS 2500
#define POOLP 0.7
#define CROSS_P 0.6

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

static int DEG, DIAM, MAXT;
static int K, K2, M, R, G, T;
static int *Rpow = NULL, *perm = NULL, *adj = NULL, *cnt = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int *dJ = NULL, *dS = NULL, *bestJ = NULL, *bestS = NULL;
static int curstamp = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

typedef struct {
    int K, K2, M, R;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

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

static void build_all(void) {
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Sum over the 2K block representatives of vertices not reached within DIAM.
   Returns 0 iff the lift has diameter <= DIAM. Duplicate darts give BIGC. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (t1 % K == t2 % K && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = (t % K) * G, bj = (K + dJ[t]) * G;
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
        total += N - count;
    }
    return total;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2; T = DEG * K;
    int N = 2 * K * G;
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_config(void) {
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    perm = adj = cnt = stamp = fr = nx = NULL;
    Rpow = NULL;
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = (t % K) * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = 2 * K * G;
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
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    build_all();
}

/* Kicks that keep each layer a permutation. */
static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
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

/* Simulated annealing on the true cost. The caller has evaluated the start state.
   The best state goes to bestJ/bestS. Returns the best cost. */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05);
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
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
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
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

static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        build_all();
        if (2 * K * G > best_n) emit();
    }
}

static int elig_entry(int i) {
    return 2 * pool[i].K * pool[i].K2 * pool[i].M > best_n;
}

/* Only positive-cost entries whose group order still beats best_n are stored.
   Ineligible entries are replaced first. */
static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    if (2 * K * G <= best_n) return;
    int slot = -1;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        long long worst = -1;
        for (int i = 0; i < POOLMAX; i++) {
            long long key = elig_entry(i) ? pool[i].cost : BIGC;
            if (key > worst) { worst = key; slot = i; }
        }
        if (worst <= cost) return;
    }
    Cfg *c = &pool[slot];
    c->K = K; c->K2 = K2; c->M = M; c->R = R; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_eligible(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (elig_entry(i)) cand[nc++] = i;
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

static int find_partner(int a) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        if (i != a && pool[i].K == pool[a].K && pool[i].K2 == pool[a].K2 &&
            pool[i].M == pool[a].M && pool[i].R == pool[a].R)
            cand[nc++] = i;
    }
    return nc ? cand[rnd_int(nc)] : -1;
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
    if (DEG < 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MAXT = MAXK * DEG;
    dJ = malloc(sizeof(int) * (size_t)MAXT);
    dS = malloc(sizeof(int) * (size_t)MAXT);
    bestJ = malloc(sizeof(int) * (size_t)MAXT);
    bestS = malloc(sizeof(int) * (size_t)MAXT);
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
        pool[i].K = pool[i].K2 = pool[i].M = pool[i].R = 1;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 2, 2, 3, 4};
    while (elapsed() < DEADLINE) {
        int pa = -1;
        if (npool > 0 && rnd_unit() < POOLP) pa = pick_eligible();
        if (pa >= 0) {
            /* Layer crossover of two elites from the same group, then polish. */
            Cfg *A = &pool[pa];
            setup_group(A->K, A->K2, A->M, A->R);
            int pb = find_partner(pa);
            memcpy(dJ, A->J, sizeof(int) * (size_t)T);
            memcpy(dS, A->S, sizeof(int) * (size_t)T);
            if (pb >= 0 && rnd_unit() < CROSS_P) {
                Cfg *B = &pool[pb];
                for (int l = 0; l < DEG; l++) {
                    if (rnd_unit() < 0.5) {
                        for (int i = 0; i < K; i++) {
                            int t = l * K + i;
                            dJ[t] = B->J[t];
                            dS[t] = B->S[t];
                        }
                    }
                }
            }
            build_all();
            perturb(2 + rnd_int(4));
            long long cst = eval_cost();
            long long bc = run_sa(SA_ILS, 0.5, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
        } else {
            /* Fresh random lift over a group of order near the best so far. */
            int k = kc[rnd_int(5)];
            int gmin = best_n / (2 * k) + 1;
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
            setup_group(k, c2, m, r);
            random_init();
            long long cost = eval_cost();
            long long bc = run_sa(SA_FRESH, 1.0, cost);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
        }
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
# Driver: baselines in Python, then the C search with layer crossover.
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

    # Give the C search nearly all of the budget. The reserve covers the
    # one-off C compile (outside the C deadline), parsing and validation.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
