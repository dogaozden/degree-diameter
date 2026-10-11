import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: tabu search over bi-Cayley lifts instead of annealing.
#
# Construction: vertices A_i,g = i*G + g and B_j,h = (K+j)*G + h, with G the
# order of a group Z_m x|_r Z_k2. Dart t = (i, j, s) joins A_i,g to B_j,g*s for
# all g. Each layer is a permutation of the K blocks, so every vertex has degree
# DEG. Left multiplication is an automorphism, so the diameter is at most DIAM
# iff BFS of depth DIAM from each of the 2K block representatives covers all.
#
# Search: tabu search over the full neighbourhood (every voltage change and
# every within-layer target swap), with a tenure list and aspiration. Each run
# restarts at a random group order slightly above the current record. This
# replaces the parent's annealing and breakout weights.
#
# Safety: the Python driver keeps PG(2,q), W(q) and K_{d,d} fallbacks, and
# every returned graph passes lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define STALL 250
#define TENURE_BASE 4
#define TENURE_RAND 8

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

static int DEG, DIAM, K, K2, M, R, G, T, N;
static int *Rpow, *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *tabu_s, *tabu_j;
static int curstamp;
static int best_n, best_m;
static int *best_e = NULL;

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void alloc_all(void) {
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    tabu_s = calloc((size_t)T * G, sizeof(int));
    tabu_j = calloc((size_t)T * K, sizeof(int));
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void free_all(void) {
    free(dI); free(dJ); free(dS); free(perm); free(adj); free(cnt);
    free(stamp); free(fr); free(nx); free(Rpow); free(tabu_s); free(tabu_j);
    dI = dJ = dS = perm = adj = cnt = stamp = fr = nx = NULL;
    Rpow = tabu_s = tabu_j = NULL;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

/* Sum over the 2K block representatives of the number of vertices at distance
   more than DIAM. Zero iff the graph is valid. Duplicate darts give BIGC. */
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
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int src = r * G;
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

static void random_init(void) {
    int p[16];
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

/* Tabu search over the full neighbourhood: change one voltage, or swap two
   targets inside one layer. Returns 1 when a valid lift is reached. The
   current state is left as the valid graph. */
static int search_group(void) {
    memset(tabu_s, 0, sizeof(int) * (size_t)T * G);
    memset(tabu_j, 0, sizeof(int) * (size_t)T * K);
    long long cost = eval_cost();
    long long best = cost;
    int stall = 0;
    for (int it = 1; ; it++) {
        if (cost == 0) return 1;
        if (stall >= STALL) return 0;
        if (elapsed() > DEADLINE) return 0;
        int tenure = TENURE_BASE + rnd_int(TENURE_RAND);

        long long bc = 4 * BIGC;
        int kind = -1, bt = -1, bs = 0, bt2 = -1, bnt = 0;

        for (int t = 0; t < T; t++) {
            int old = dS[t];
            for (int s = 0; s < G; s++) {
                if (s == old) continue;
                dS[t] = s;
                build_perm(t);
                long long c = eval_cost();
                int tb = tabu_s[(size_t)t * G + s] > it;
                if (!tb || c < best) {
                    if (c < bc) {
                        bc = c; kind = 0; bt = t; bs = s; bnt = 1;
                    } else if (c == bc) {
                        bnt++;
                        if (rnd_int(bnt) == 0) { kind = 0; bt = t; bs = s; }
                    }
                }
            }
            dS[t] = old;
            build_perm(t);
        }

        if (K > 1) {
            for (int l = 0; l < DEG; l++)
                for (int i1 = 0; i1 < K; i1++)
                    for (int i2 = i1 + 1; i2 < K; i2++) {
                        int t1 = l * K + i1, t2 = l * K + i2;
                        int a = dJ[t1], b = dJ[t2];
                        dJ[t1] = b; dJ[t2] = a;
                        long long c = eval_cost();
                        int tb = tabu_j[(size_t)t1 * K + b] > it ||
                                 tabu_j[(size_t)t2 * K + a] > it;
                        dJ[t1] = a; dJ[t2] = b;
                        if (!tb || c < best) {
                            if (c < bc) {
                                bc = c; kind = 1; bt = t1; bt2 = t2; bnt = 1;
                            } else if (c == bc) {
                                bnt++;
                                if (rnd_int(bnt) == 0) { kind = 1; bt = t1; bt2 = t2; }
                            }
                        }
                    }
        }

        if (kind < 0) {
            int t = rnd_int(T), s = rnd_int(G);
            dS[t] = s;
            build_perm(t);
            cost = eval_cost();
        } else if (kind == 0) {
            int old = dS[bt];
            dS[bt] = bs;
            build_perm(bt);
            tabu_s[(size_t)bt * G + old] = it + tenure;
            cost = bc;
        } else {
            int a = dJ[bt], b = dJ[bt2];
            dJ[bt] = b;
            dJ[bt2] = a;
            tabu_j[(size_t)bt * K + a] = it + tenure;
            tabu_j[(size_t)bt2 * K + b] = it + tenure;
            cost = bc;
        }

        if (cost < best) {
            best = cost;
            stall = 0;
        } else {
            stall++;
        }
    }
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kch[6] = {1, 1, 2, 2, 3, 4};
    while (elapsed() < DEADLINE) {
        int k = kch[rnd_int(6)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 8 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;

        int opts[16], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            for (int tr = 0; tr < 200; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    break;
                }
            }
        }

        K = k; K2 = c2; M = m; R = r; G = g;
        alloc_all();
        random_init();
        if (search_group()) emit();
        free_all();
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

    if D >= 4 and time.monotonic() - start < 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Leave a margin for compilation, parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
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
