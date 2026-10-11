import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over semidirect products Z_m x| Z_k2 with a base of
# K A-vertices and K B-vertices (K = 1, 2, 3). Two searches share one group
# sampler and one exact cost function:
#   * tabu search over single-dart moves (main new strategy, ~60% of runs),
#   * simulated annealing (parent strategy, kept as a hedge, ~40% of runs).
#
# Cost = number of ordered (block representative, vertex) pairs at distance
# more than DIAM, computed exactly by BFS from the 2K block representatives.
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex has
# degree DEG. Left multiplication is an automorphism, so BFS from the block
# representatives decides the diameter.
#
# argv: d D seed time_limit [start_n] [floor_n]
#   start_n: emit only graphs with more vertices than this.
#   floor_n: 70% of runs target group orders giving at least this many vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXK 3
#define RUN_ITERS 5000
#define STALL 1200
#define NSAMPLE 16
#define SA_ITERS 8000

static uint64_t rs[2];

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
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int DEG, DIAM, K, K2, M, G, T, R;
static int *Rpow;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS, *tab;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;
static int floor_n;

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

/* Exact cost: ordered pairs (block representative, vertex) at distance > DIAM. */
static long long eval_cost(void) {
    int N = 2 * K * G;
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

static void alloc_config(void) {
    int N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    tab = calloc((size_t)T * G, sizeof(int));
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
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(tab); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
    tab = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

/* Random semidirect group Z_m x| Z_c2 of order g (c2 = 1 gives cyclic). */
static void pick_group(int k, int gmin, int spread) {
    int g = gmin + rnd_int(spread);
    if (g < 2) g = 2;
    int opts[16], no = 0;
    for (int c = 1; c <= 12; c++)
        if (g % c == 0 && g / c >= 2) opts[no++] = c;
    int c2 = opts[rnd_int(no)];
    int m = g / c2, r = 1;
    if (c2 > 1) {
        int found = 0;
        for (int tr = 0; tr < 400 && !found; tr++) {
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

/* Tabu search: best admissible move among NSAMPLE random candidates. Returns best cost. */
static long long run_tabu(void) {
    long long cur = eval_cost();
    long long bestc = cur;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    memset(tab, 0, sizeof(int) * (size_t)T * G);
    int since = 0;
    for (int it = 1; it <= RUN_ITERS && bestc > 0 && since < STALL; it++) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) break;
        long long bc = 4LL * BIGC;
        int kind = -1, ba = 0, bb = 0, bv = 0, ties = 0;
        for (int c = 0; c < NSAMPLE; c++) {
            int k2 = 0, a = 0, b = 0, v = 0;
            long long cc = 0;
            if (K > 1 && rnd_unit() < 0.25) {
                int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                k2 = 1; a = l * K + i1; b = l * K + i2;
                int tmp = dJ[a]; dJ[a] = dJ[b]; dJ[b] = tmp;
                cc = eval_cost();
                tmp = dJ[a]; dJ[a] = dJ[b]; dJ[b] = tmp;
            } else {
                k2 = 0; a = rnd_int(T); v = rnd_int(G);
                if (v == dS[a]) continue;
                int old = dS[a];
                dS[a] = v; build_perm(a);
                cc = eval_cost();
                dS[a] = old; build_perm(a);
                if (tab[a * G + v] > it && cc >= bestc) continue;   /* tabu, no aspiration */
            }
            if (cc < bc) {
                bc = cc; kind = k2; ba = a; bb = b; bv = v; ties = 1;
            } else if (cc == bc) {
                ties++;
                if (rnd_int(ties) == 0) { kind = k2; ba = a; bb = b; bv = v; }
            }
        }
        if (kind < 0) { since++; continue; }
        if (kind == 0) {
            int old = dS[ba];
            tab[ba * G + old] = it + 5 + rnd_int(6);
            dS[ba] = bv;
            build_perm(ba);
        } else {
            int tmp = dJ[ba]; dJ[ba] = dJ[bb]; dJ[bb] = tmp;
        }
        cur = eval_cost();
        if (cur < bestc) {
            bestc = cur;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
            since = 0;
        } else {
            since++;
        }
    }
    return bestc;
}

/* Simulated annealing from the current configuration. Returns best cost. */
static long long run_sa(void) {
    long long cost = eval_cost();
    long long bestc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < SA_ITERS && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double temp = 3.0 * (1.0 - (double)it / SA_ITERS) + 0.05;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int a = l * K + i1, b = l * K + i2;
            int tmp = dJ[a]; dJ[a] = dJ[b]; dJ[b] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = dJ[a]; dJ[a] = dJ[b]; dJ[b] = tmp;
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

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n] [floor_n]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    floor_n = argc > 6 ? atoi(argv[6]) : 0;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[6] = {1, 1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(6)];
        int base = best_n;
        if (rnd_unit() < 0.7 && floor_n > base) base = floor_n;
        int gmin = base / (2 * k) + 1;
        if (gmin < 2) gmin = 2;
        int spread = gmin / 8 + 3;
        pick_group(k, gmin, spread);
        random_init();
        long long bc = (rnd_unit() < 0.6) ? run_tabu() : run_sa();
        if (bc == 0 && 2 * K * G > best_n) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(dS, bestS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            emit();
        }
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
# Driver: baselines in Python, then the C search (tabu + annealing hedge).
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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
        # Search floor: aim the group orders at roughly 40% of the Moore bound.
        floor_n = max(best_n, int(0.4 * moore))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n, floor_n],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
