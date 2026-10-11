import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley / voltage-lift search by tabu search.
#
# This replaces the earlier annealer with a different search. Each step samples
# a batch of single-dart moves (retarget one dart's group element, or swap two
# targets inside one layer), applies the best admissible move, and keeps it on
# a tabu list. Stagnation triggers a perturbation of the best configuration.
#
# Model: K A-blocks and K B-blocks, each a copy of a group H of order G
# (H = Z_M x| Z_K2, element a*K2+b). Layer l is a permutation p_l of the K
# blocks, and dart (l, i) joins A_{i,g} to B_{p_l(i), g*s} for all g. Every
# vertex then has degree DEG. Left multiplication is an automorphism, so
# diameter <= D iff BFS of depth D from each of the 2K block representatives
# covers all vertices.
#
# Groups are drawn at random near the current best order, so each success
# raises the bar. Any cost-0 configuration is emitted if it is larger than the
# best so far. The Python side validates every output and keeps a fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXDEG 16
#define MAXK 6
#define MAXT (MAXDEG * MAXK)
#define NSAMP 24
#define STEPS 2500
#define NOIMP 250
#define TTBASE 6
#define TTRAND 8
#define PERTURB_MIN 3
#define PERTURB_RANGE 5

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

static int DEG, DIAM, K, K2, M, G, T, R, N;
static int dJ[MAXT], dS[MAXT];
static int bestJ[MAXT], bestS[MAXT];
static int *perm, *Rpow, *adjv, *cntv, *stamp, *fq, *nq;
static int curstamp;

static int best_n, best_m;
static int *best_e = NULL;

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
static int gmul(int x, int y) {
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

/* Sum over the 2K block representatives of the number of vertices NOT within
   distance DIAM. Returns BIGC for configurations with a repeated dart. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (t1 % K == t2 % K && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
    memset(cntv, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = (t % K) * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            if (cntv[a] >= DEG || cntv[b] >= DEG) return BIGC;
            adjv[(size_t)a * DEG + cntv[a]++] = b;
            adjv[(size_t)b * DEG + cntv[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fq, *h = nq;
        int fsz = 1, count = 1;
        f[0] = r * G;
        stamp[r * G] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adjv + (size_t)f[q] * DEG;
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
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    N = 2 * K * G;
    T = DEG * K;
    perm = malloc(sizeof(int) * (size_t)T * G);
    adjv = malloc(sizeof(int) * (size_t)N * DEG);
    cntv = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fq = malloc(sizeof(int) * (size_t)N);
    nq = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    curstamp = 0;
}

static void free_group(void) {
    free(perm); free(adjv); free(cntv); free(stamp); free(fq); free(nq); free(Rpow);
    perm = adjv = cntv = stamp = fq = nq = Rpow = NULL;
}

static void build_all(void) {
    for (int t = 0; t < T; t++) build_perm(t);
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

static void swap_layer_targets(int t1, int t2) {
    int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
}

static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            swap_layer_targets(l * K + i1, l * K + i2);
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

/* Tabu search from the current state. Returns the best true cost found and
   stores that configuration in bestJ/bestS. */
static long long tabu_run(long long cost0) {
    int tabu[MAXT];
    memset(tabu, 0, sizeof(tabu));
    long long cur = cost0;
    long long bestc = cur;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    int last_imp = 0;
    for (int step = 1; step <= STEPS && bestc > 0; step++) {
        if ((step & 15) == 0 && elapsed() > DEADLINE) break;
        long long cb = 4 * BIGC;
        int kind = -1, ct = -1, cs = -1, ci1 = -1, ci2 = -1;
        for (int smp = 0; smp < NSAMP; smp++) {
            if (rnd_unit() < 0.75) {
                int t = rnd_int(T);
                int olds = dS[t];
                int news = rnd_int(G);
                if (news == olds) continue;
                dS[t] = news; build_perm(t);
                long long c2 = eval_cost();
                dS[t] = olds; build_perm(t);
                if (tabu[t] > step && !(c2 < bestc)) continue;
                if (c2 < cb || (c2 == cb && rnd_unit() < 0.5)) {
                    cb = c2; kind = 0; ct = t; cs = news;
                }
            } else {
                if (K < 2) continue;
                int l = rnd_int(DEG);
                int i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                swap_layer_targets(t1, t2);
                long long c2 = eval_cost();
                swap_layer_targets(t1, t2);
                if ((tabu[t1] > step || tabu[t2] > step) && !(c2 < bestc)) continue;
                if (c2 < cb || (c2 == cb && rnd_unit() < 0.5)) {
                    cb = c2; kind = 1; ci1 = t1; ci2 = t2;
                }
            }
        }
        if (kind < 0) continue;
        if (kind == 0) {
            dS[ct] = cs; build_perm(ct);
            tabu[ct] = step + TTBASE + rnd_int(TTRAND);
        } else {
            swap_layer_targets(ci1, ci2);
            tabu[ci1] = step + TTBASE + rnd_int(TTRAND);
            tabu[ci2] = step + TTBASE + rnd_int(TTRAND);
        }
        cur = cb;
        if (cur < bestc) {
            bestc = cur;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
            last_imp = step;
        }
        if (step - last_imp > NOIMP) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(dS, bestS, sizeof(int) * (size_t)T);
            build_all();
            perturb(PERTURB_MIN + rnd_int(PERTURB_RANGE));
            build_all();
            memset(tabu, 0, sizeof(tabu));
            cur = eval_cost();
            last_imp = step;
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
            best_e[idx++] = (t % K) * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = N;
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
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[6] = {1, 1, 2, 2, 3, 4};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(6)];
        if (k > MAXK) k = 1;
        long long gmin = (long long)best_n / (2 * k) + 1;
        if (gmin < 2) gmin = 2;
        int spread = (int)(gmin / 10) + 3;
        long long gl = gmin + rnd_int(spread);
        int g = (int)gl;
        int opts[16], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        if (no == 0) continue;
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
        long long c0 = eval_cost();
        long long bc = tabu_run(c0);
        if (bc == 0) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(dS, bestS, sizeof(int) * (size_t)T);
            build_all();
            if (N > best_n) emit();
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
# Driver: baselines in Python, then the C tabu search over bi-Cayley lifts.
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

    if best_n >= lib.moore_bound(d, D):
        return best

    # Most of the budget goes to the C tabu search. The reserve covers compile,
    # parsing and validation.
    remaining = 0.94 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
