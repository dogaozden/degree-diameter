import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts of semidirect products Z_m x| Z_k2 over a base of
# K A-vertices and K B-vertices. This version replaces the annealer with a
# tabu search. Each step samples a batch of random moves (a layer swap of two
# targets, or a voltage change), applies the best non-tabu move even if it is
# worse, and keeps a short tabu list on the darts it touched. Aspiration allows
# a tabu move if it beats the run's best. Runs restart after STAG steps without
# improvement. Half of the runs start from an elite configuration (lowest
# positive cost so far, same group-order floor) with a small random kick.
#
# Cost: sum over the 2K block representatives of uncovered vertices after
# BFS of depth DIAM, plus a penalty for duplicate darts. Cost 0 means a valid
# simple bipartite graph of max degree DEG and diameter <= DIAM.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex has
# degree DEG. Left multiplication is an automorphism, so BFS from the block
# representatives suffices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DUPPEN 1000LL
#define SAMPLE 24
#define TABU_TEN 6
#define STAG 300
#define RUN_IT 5000
#define ELITE_P 0.5

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

static int DEG, DIAM, K, K2, M, G, T, R, MAXT;
static int *Rpow;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *tabu_until, *bJ, *bS;
static int curstamp;
static double DEADLINE;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

/* Elite configuration: lowest positive cost seen for a group above the record. */
static int have_elite = 0;
static long long elite_cost = 1000000000LL;
static int eK, eK2, eM, eR;
static int *eJ = NULL, *eS = NULL;

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

static void set_volt(int t, int v) {
    dS[t] = v;
    build_perm(t);
}

static void do_swap(int t1, int t2) {
    int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
}

/* Cost = uncovered ordered pairs over block representatives + duplicate penalty. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    long long dup = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) dup++;
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
        total += N - count;
    }
    return total + DUPPEN * dup;
}

static void alloc_config(void) {
    int N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bJ = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
    tabu_until = calloc((size_t)T, sizeof(int));
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bJ); free(bS); free(tabu_until);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    dI = dJ = dS = bJ = bS = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
    tabu_until = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
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
    /* Elites from older records are no longer eligible. */
    have_elite = 0;
    elite_cost = 1000000000LL;
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

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 != i2) do_swap(l * K + i1, l * K + i2);
        } else {
            set_volt(rnd_int(T), rnd_int(G));
        }
    }
}

/* Tabu search over batches of sampled moves. Caller has set dJ/dS and perms
   and passes the true cost of that state. Best state goes to bJ/bS. */
static long long run_tabu(long long cost, int maxit) {
    long long bestc = cost;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) tabu_until[t] = 0;
    int last_imp = 0;
    for (int it = 1; it <= maxit && bestc > 0; it++) {
        if (elapsed() > DEADLINE) break;
        long long mc = 4000000000LL;
        int mtype = -1, ma = 0, mb = 0;
        for (int s = 0; s < SAMPLE; s++) {
            if (K > 1 && rnd_unit() < 0.3) {
                int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                do_swap(t1, t2);
                long long c2 = eval_cost();
                do_swap(t1, t2);
                int tb = tabu_until[t1] > it || tabu_until[t2] > it;
                if (tb && c2 >= bestc) continue;
                if (c2 < mc || (c2 == mc && rnd_int(2))) {
                    mc = c2; mtype = 0; ma = t1; mb = t2;
                }
            } else {
                int t = rnd_int(T);
                int nv = rnd_int(G);
                if (nv == dS[t]) continue;
                int old = dS[t];
                set_volt(t, nv);
                long long c2 = eval_cost();
                set_volt(t, old);
                int tb = tabu_until[t] > it;
                if (tb && c2 >= bestc) continue;
                if (c2 < mc || (c2 == mc && rnd_int(2))) {
                    mc = c2; mtype = 1; ma = t; mb = nv;
                }
            }
        }
        if (mtype < 0) continue;
        if (mtype == 0) {
            do_swap(ma, mb);
            tabu_until[ma] = it + TABU_TEN + rnd_int(4);
            tabu_until[mb] = it + TABU_TEN + rnd_int(4);
        } else {
            set_volt(ma, mb);
            tabu_until[ma] = it + TABU_TEN + rnd_int(4);
        }
        cost = eval_cost();
        if (cost < bestc) {
            bestc = cost;
            memcpy(bJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bS, dS, sizeof(int) * (size_t)T);
            last_imp = it;
        }
        if (it - last_imp > STAG) break;
    }
    return bestc;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the record. */
static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bJ, sizeof(int) * (size_t)T);
        memcpy(dS, bS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * G > best_n) emit();
    }
}

static void store_elite(long long bc) {
    if (bc <= 0 || bc >= elite_cost) return;
    if (2 * K * G <= best_n) return;
    if (eJ == NULL) {
        eJ = malloc(sizeof(int) * (size_t)MAXT);
        eS = malloc(sizeof(int) * (size_t)MAXT);
    }
    eK = K; eK2 = K2; eM = M; eR = R;
    memcpy(eJ, bJ, sizeof(int) * (size_t)T);
    memcpy(eS, bS, sizeof(int) * (size_t)T);
    elite_cost = bc;
    have_elite = 1;
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
    MAXT = 3 * DEG + 3;
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        long long bc;
        if (have_elite && 2 * eK * eK2 * eM > best_n && rnd_unit() < ELITE_P) {
            setup_group(eK, eK2, eM, eR);
            memcpy(dJ, eJ, sizeof(int) * (size_t)T);
            memcpy(dS, eS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            long long cst = eval_cost();
            bc = run_tabu(cst, RUN_IT);
        } else {
            int k = kc[rnd_int(5)];
            int gmin = best_n / (2 * k) + 1;
            int spread = gmin / 6 + 2;
            int g = gmin + rnd_int(spread);
            if (g < 2) g = 2;
            int opts[12], no = 0;
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
            long long cst = eval_cost();
            bc = run_tabu(cst, RUN_IT);
        }
        finish_run(bc);
        store_elite(bc);
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
# Driver: baselines in Python, then the C tabu search over voltage lifts.
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

    # Give the C search nearly all of the budget. The wall-clock deadline inside C
    # keeps the run on time; the margin covers compilation, parsing and validation.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
