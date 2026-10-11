import time

import lib


# ----------------------------------------------------------------------------
# Search family: voltage lifts over Cayley-type groups Z_m x|_r Z_k2 (k2 | |G|).
#
# Changes from the previous engine:
#  * Fresh starts sample base sizes K in {1..4} with more weight on K = 2, 3.
#  * Most moves are focused: pick a block (A_i or B_j) that is still not covered
#    by its BFS ball, then change a dart incident to that block. Random moves
#    still happen, so the search is not confined to the focus region.
#  * Breakout weights bump the uncovered blocks when the true cost stalls.
#  * The elite pool restarts from low-cost configurations whose group order is
#    still above the current best.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s), with
# t = l*K + i and dart i in layer l, joins A_i,g to B_j,g*s for all g. Each
# layer is a permutation of the K blocks, so every vertex has degree DEG.
# Left multiplication is an automorphism, so the diameter is at most D iff BFS
# of depth D from each of the 2K block representatives reaches all vertices.
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
#define MAXDEG 12
#define MAXT (MAXK * MAXDEG)
#define MAXC2 12
#define POOLMAX 32
#define ITERS 5000
#define ILS_ITERS 2500
#define BRK 120
#define POOLP 0.55

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

static int DEG, DIAM, K, K2, M, G, T, R;
static int *Rpow = NULL;
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int bestJ[MAXT], bestS[MAXT];
static int *perm = NULL, *adj = NULL, *cnt = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int curstamp = 0;
static long long *wt = NULL, *unc = NULL, *ucur = NULL;
static long long wsum = 0;
static long long lastw = 0;
static double DEADLINE;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

typedef struct {
    int K, K2, M, R;
    long long cost;
    int J[MAXT], S[MAXT];
} Cfg;

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

/* True cost: uncovered ordered pairs summed over the 2K block representatives.
   Sets unc[r] per block and lastw to the breakout-weighted cost. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 1;
                lastw = BIGC;
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
    long long total = 0, w = 0;
    for (int r = 0; r < 2 * K; r++) {
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
    lastw = w;
    return total;
}

/* Evaluate the current state and remember its uncovered blocks. */
static long long eval_state(void) {
    long long c = eval_cost();
    memcpy(ucur, unc, sizeof(long long) * (size_t)(2 * K));
    return c;
}

static void alloc_group(void) {
    int N = 2 * K * G;
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    ucur = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_group(void) {
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    free(wt); free(unc); free(ucur);
    perm = adj = NULL;
    cnt = stamp = fr = nx = NULL;
    Rpow = NULL;
    wt = unc = ucur = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    T = DEG * K;
    alloc_group();
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum = 2 * K;
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
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Random kicks used by the iterated local search. */
static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int tmp = dJ[l * K + i1]; dJ[l * K + i1] = dJ[l * K + i2]; dJ[l * K + i2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

static int pick_uncovered(void) {
    int cand[2 * MAXK], nc = 0;
    for (int r = 0; r < 2 * K; r++)
        if (ucur[r] > 0) cand[nc++] = r;
    if (nc == 0) return -1;
    return cand[rnd_int(nc)];
}

/* Propose one move on the current state. Returns 0 if nothing changed.
   Focused moves act on a dart incident to a block that is still uncovered. */
static int propose(int focus) {
    int r = focus ? pick_uncovered() : -1;
    if (r < 0) {
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) return 0;
            int tmp = dJ[l * K + i1]; dJ[l * K + i1] = dJ[l * K + i2]; dJ[l * K + i2] = tmp;
            return 1;
        }
        int t = rnd_int(T);
        int news = rnd_int(G);
        if (news == dS[t]) return 0;
        dS[t] = news;
        build_perm(t);
        return 1;
    }
    int l = rnd_int(DEG);
    int t = -1;
    if (r < K) {
        t = l * K + r;
    } else {
        int j = r - K;
        for (int i = 0; i < K; i++)
            if (dJ[l * K + i] == j) { t = l * K + i; break; }
    }
    if (t < 0) return 0;
    if (K > 1 && rnd_unit() < 0.4) {
        int i_self = t % K;
        int i2 = rnd_int(K);
        if (i2 == i_self) return 0;
        int t2 = l * K + i2;
        int tmp = dJ[t]; dJ[t] = dJ[t2]; dJ[t2] = tmp;
        return 1;
    }
    int news = rnd_int(G);
    if (news == dS[t]) return 0;
    dS[t] = news;
    build_perm(t);
    return 1;
}

/* Annealing on the breakout-weighted cost. The caller must have called
   eval_state() so that lastw and ucur describe the start state.
   Returns the best true cost; the best configuration goes to bestJ/bestS. */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost, prevc = cost;
    long long wcur = lastw;
    int saveS[MAXT], saveJ[MAXT];
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                for (int r = 0; r < 2 * K; r++)
                    if (ucur[r] > 0) { wt[r]++; wsum++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * ucur[r];
            }
            prevc = cost;
        }
        double avgw = (double)wsum / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * avgw;
        memcpy(saveS, dS, sizeof(int) * (size_t)T);
        memcpy(saveJ, dJ, sizeof(int) * (size_t)T);
        int focus = rnd_unit() < 0.6;
        if (!propose(focus)) continue;
        long long c2 = eval_cost();
        long long w2 = lastw;
        if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
            cost = c2;
            wcur = w2;
            memcpy(ucur, unc, sizeof(long long) * (size_t)(2 * K));
            if (cost < bestc) {
                bestc = cost;
                memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
                memcpy(bestS, dS, sizeof(int) * (size_t)T);
            }
        } else {
            for (int t = 0; t < T; t++) {
                if (dS[t] != saveS[t]) {
                    dS[t] = saveS[t];
                    build_perm(t);
                }
            }
            memcpy(dJ, saveJ, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the best so far. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (2 * K * G > best_n) emit();
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
    c->K = K; c->K2 = K2; c->M = M; c->R = R; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].K2 * pool[i].M;
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
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < POOLMAX; i++) pool[i].cost = BIGC;
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[8] = {1, 2, 2, 3, 3, 4, 1, 2};
    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            Cfg c = pool[pi];
            setup_group(c.K, c.K2, c.M, c.R);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            long long cst = eval_state();
            long long bc = run_sa(ILS_ITERS, 0.3, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_group();
            continue;
        }

        int k = kc[rnd_int(8)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 5 + 3;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[MAXC2], no = 0;
        for (int c = 1; c <= MAXC2; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 300 && !found; tr++) {
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
        long long cost = eval_state();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
        free_group();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    free(best_e);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (always valid, used as fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Leave room for the cached compile, process start, parsing and validation.
    time_limit = float(time_limit)
    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
