import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts of groups Z_m x|_r Z_k2 over a base of K A-vertices
# and K B-vertices (K <= 5), searched by tabu search with sampled neighbourhoods.
#
# Changes from the previous annealer:
#  * Tabu search instead of simulated annealing. Each step samples NS random
#    moves (layer swaps of B-targets, or voltage changes), applies the best
#    non-tabu move (aspiration allowed if it beats the run's best), and makes
#    the touched darts tabu for a short random tenure.
#  * Broader base: K in {1..5}, so larger base multigraphs are explored.
#  * Iterated local search over an elite pool of configurations. Elite entries
#    store their group parameters, so a perturbed elite is re-searched in its
#    own group. Restarts from random lifts keep exploration alive.
#  * Groups with r = 1 (abelian Z_m x Z_k2) and r != 1 (semidirect) both occur.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex has
# degree DEG. Left multiplication is an automorphism, so diameter <= D iff BFS
# of depth D from each of the 2K block representatives covers all vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define NS 32
#define NOIMP 1500
#define RUNIT 40000
#define ELITE 8
#define KMAX 5

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

static int DEG, DIAM, K, K2, M, R, G, T, N;
static int *Rpow, *dI, *dJ, *dS, *tabu, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bJ, *bS;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;

typedef struct {
    int K, K2, M, R;
    long long cost;
    int *J, *S;
} Elite;

static Elite elite[ELITE];
static int nelite = 0;

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

/* Sum over the 2K block representatives of uncovered vertices after depth DIAM.
   Returns 0 iff the lift has diameter <= DIAM. Duplicate darts give BIGC. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
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
    return total;
}

static void alloc_group(void) {
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    tabu = calloc((size_t)T, sizeof(int));
    bJ = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
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
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void free_group(void) {
    free(dI); free(dJ); free(dS); free(tabu); free(bJ); free(bS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    dI = dJ = dS = bJ = bS = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
    tabu = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    alloc_group();
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

/* Random kicks that keep every layer a permutation. */
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

/* Tabu search from the current state. Best state goes to bJ/bS. Returns its cost. */
static long long tabu_run(void) {
    long long cost = eval_cost();
    long long bestc = cost;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    memset(tabu, 0, sizeof(int) * (size_t)T);
    int noimp = 0;
    for (int it = 1; it <= RUNIT && bestc > 0; it++) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) break;
        if (noimp > NOIMP) break;
        long long cb = 4 * BIGC;
        int ctype = -1, ca = 0, cx = 0, cnew = 0;
        for (int s = 0; s < NS; s++) {
            if (K > 1 && rnd_unit() < 0.25) {
                int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                long long c = eval_cost();
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                int tb = (tabu[t1] > it) || (tabu[t2] > it);
                if (tb && c >= bestc) continue;
                if (c < cb || (c == cb && rnd_unit() < 0.5)) {
                    cb = c; ctype = 0; ca = t1; cx = t2;
                }
            } else {
                int t = rnd_int(T);
                int olds = dS[t], news = rnd_int(G);
                if (news == olds) continue;
                int tb = tabu[t] > it;
                dS[t] = news; build_perm(t);
                long long c = eval_cost();
                dS[t] = olds; build_perm(t);
                if (tb && c >= bestc) continue;
                if (c < cb || (c == cb && rnd_unit() < 0.5)) {
                    cb = c; ctype = 1; ca = t; cnew = news;
                }
            }
        }
        if (ctype < 0) { noimp++; continue; }
        if (ctype == 0) {
            int tmp = dJ[ca]; dJ[ca] = dJ[cx]; dJ[cx] = tmp;
            int ten = it + 4 + rnd_int(8);
            tabu[ca] = ten; tabu[cx] = ten;
        } else {
            dS[ca] = cnew; build_perm(ca);
            tabu[ca] = it + 4 + rnd_int(8);
        }
        if (cb < bestc) {
            bestc = cb;
            memcpy(bJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bS, dS, sizeof(int) * (size_t)T);
            noimp = 0;
        } else {
            noimp++;
        }
    }
    return bestc;
}

static void add_elite(long long cost) {
    int slot;
    if (nelite < ELITE) {
        slot = nelite++;
    } else {
        slot = 0;
        for (int i = 1; i < ELITE; i++)
            if (elite[i].cost > elite[slot].cost) slot = i;
        if (elite[slot].cost <= cost) return;
    }
    Elite *e = &elite[slot];
    e->K = K; e->K2 = K2; e->M = M; e->R = R; e->cost = cost;
    memcpy(e->J, bJ, sizeof(int) * (size_t)T);
    memcpy(e->S, bS, sizeof(int) * (size_t)T);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    int DEGarg = atoi(argv[1]);
    DEG = DEGarg;
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
    for (int i = 0; i < ELITE; i++) {
        elite[i].J = malloc(sizeof(int) * (size_t)(DEG * KMAX));
        elite[i].S = malloc(sizeof(int) * (size_t)(DEG * KMAX));
        elite[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[8] = {1, 1, 2, 2, 3, 3, 4, 5};
    while (elapsed() < DEADLINE) {
        int use_elite = -1;
        if (nelite > 0 && rnd_unit() < 0.5) {
            int cand[ELITE], nc = 0;
            for (int i = 0; i < nelite; i++) {
                long long nn = 2LL * elite[i].K * elite[i].K2 * elite[i].M;
                if (nn > best_n) cand[nc++] = i;
            }
            if (nc > 0) use_elite = cand[rnd_int(nc)];
        }
        if (use_elite >= 0) {
            Elite *e = &elite[use_elite];
            setup_group(e->K, e->K2, e->M, e->R);
            memcpy(dJ, e->J, sizeof(int) * (size_t)T);
            memcpy(dS, e->S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(6));
        } else {
            int k = kc[rnd_int(8)];
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
        }

        long long bc = tabu_run();
        if (bc == 0) {
            memcpy(dJ, bJ, sizeof(int) * (size_t)T);
            memcpy(dS, bS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            if (N > best_n) emit();
        } else if (bc < BIGC) {
            add_elite(bc);
        }
        free_group();
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
# Driver: baselines in Python, then the C tabu search with elite ILS.
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

    # Use about 90% of the budget for the C search. The C deadline is measured
    # from program start, so compile time is excluded; the 1.5 s reserve covers
    # a cold compile, parsing and validation.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
