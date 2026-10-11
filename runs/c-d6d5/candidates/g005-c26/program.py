import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over a base of K A-vertices and K B-vertices, with
# the voltage group chosen from TWO families:
#   fam 0: metacyclic Z_m x|_r Z_k2 (the parent family)
#   fam 1: Heisenberg group H(n) = upper unitriangular 3x3 matrices over Z_n,
#          order n^3. These are non-metacyclic for most n, so they reach group
#          orders and lift structures the parent never searched.
# Groups are stored as full multiplication tables, so the search code is
# identical for every family. Vertices: A_i,g = i*G+g, B_j,h = (K+j)*G+h.
# Dart t = (i, j, s) with layer l = t / K joins A_i,g to B_j,g*s for all g.
# Each layer is a permutation of the B-blocks, so every vertex has degree DEG.
# Left multiplication is an automorphism, so BFS of depth DIAM from the 2K
# block representatives decides the diameter.
# Search: simulated annealing from random starts, plus iterated local search
# from an elite pool keyed by group. Stop at the wall-clock deadline.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define GMAX 1500
#define KMAX 4
#define MAXDEG 32
#define TMAX (MAXDEG * KMAX)
#define NMAX (2 * KMAX * GMAX)
#define AMAX (NMAX * MAXDEG)
#define POOLMAX 32
#define POOLP 0.6
#define ITERS 6000
#define ILS_ITERS 3000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static int DEG, DIAM;
static int fam, P1, P2, P3;
static int K, G, N, T;
static int *tab;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static int curstamp;
static int best_n, best_m;
static int *best_e;

typedef struct {
    int fam, p1, p2, p3, k, g;
    long long cost;
    int J[TMAX], S[TMAX];
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

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

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

/* Install group (family, params) with K blocks: fills tab, G, N, T, dI.
   Returns 0 if the parameters do not describe a valid group of allowed size. */
static int set_group(int f, int p1, int p2, int p3, int k) {
    int g;
    if (k < 1 || k > KMAX) return 0;
    if (f == 0) {
        static int rp[GMAX];
        int m = p1, k2 = p2, r = p3;
        if (m < 1 || k2 < 1) return 0;
        long long gg = (long long)m * k2;
        if (gg < 2 || gg > GMAX) return 0;
        if (k2 > 1) {
            if (m < 2 || gcd_i(r, m) != 1 || powmod_ll(r, k2, m) != 1 % m) return 0;
        }
        g = (int)gg;
        rp[0] = 1 % m;
        for (int b = 1; b < k2; b++) rp[b] = (int)((long long)rp[b - 1] * r % m);
        for (int x = 0; x < g; x++) {
            int a = x / k2, b = x % k2;
            for (int y = 0; y < g; y++) {
                int c = y / k2, e = y % k2;
                int ra = (int)(((long long)a + (long long)rp[b] * c) % m);
                int rb = (b + e) % k2;
                tab[x * g + y] = ra * k2 + rb;
            }
        }
    } else {
        int n = p1;
        if (n < 2) return 0;
        long long gg = (long long)n * n * n;
        if (gg > GMAX) return 0;
        g = (int)gg;
        int nn = n * n;
        for (int x = 0; x < g; x++) {
            int a = x / nn, b = (x / n) % n, c = x % n;
            for (int y = 0; y < g; y++) {
                int a2 = y / nn, b2 = (y / n) % n, c2 = y % n;
                int A = (a + a2) % n;
                int B = (b + b2) % n;
                int C = (c + c2 + a * b2) % n;
                tab[x * g + y] = (A * n + B) * n + C;
            }
        }
    }
    fam = f; P1 = p1; P2 = p2; P3 = p3;
    K = k; G = g; N = 2 * K * G; T = DEG * K;
    for (int t = 0; t < T; t++) dI[t] = t % K;
    return 1;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = tab[g * G + s];
}

/* Number of (source, target) pairs at distance > DIAM, counted over block representatives.
   Zero iff the lift is valid. Duplicate darts and overfull vertices get BIGC. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            if (cnt[a] >= DEG || cnt[b] >= DEG) return BIGC;
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)NMAX);
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
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Random kicks: swap two targets inside one layer, or change one voltage. Both keep layers permutations. */
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

/* Simulated annealing from the current state. Best state goes to bestJ/bestS. */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05);
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
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

/* A zero-cost run is a valid graph: load it and emit if it beats the best so far. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (2LL * K * G > best_n) emit();
}

/* Elite pool: keep positive-cost configurations together with their group. */
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
    c->fam = fam; c->p1 = P1; c->p2 = P2; c->p3 = P3;
    c->k = K; c->g = G; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

/* Pick an elite entry whose group order still exceeds the current best; best of 3 samples. */
static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].k * pool[i].g;
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
        fprintf(stderr, "usage: prog d D seed time_limit [base_n target]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int base_n = argc > 5 ? atoi(argv[5]) : 0;
    int target = argc > 6 ? atoi(argv[6]) : 0;
    best_n = base_n;
    best_m = 0;
    best_e = NULL;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    tab = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    dI = malloc(sizeof(int) * TMAX);
    dJ = malloc(sizeof(int) * TMAX);
    dS = malloc(sizeof(int) * TMAX);
    bestJ = malloc(sizeof(int) * TMAX);
    bestS = malloc(sizeof(int) * TMAX);
    perm = malloc(sizeof(int) * (size_t)TMAX * GMAX);
    adj = malloc(sizeof(int) * (size_t)AMAX);
    cnt = malloc(sizeof(int) * NMAX);
    stamp = calloc(NMAX, sizeof(int));
    fr = malloc(sizeof(int) * NMAX);
    nx = malloc(sizeof(int) * NMAX);
    curstamp = 0;

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg *c = &pool[pi];
            if (!set_group(c->fam, c->p1, c->p2, c->p3, c->k)) continue;
            memcpy(dJ, c->J, sizeof(int) * (size_t)T);
            memcpy(dS, c->S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            continue;
        }

        /* Fresh random lift. Group order aims just above the larger of the
           current best and the target, divided by 2K. */
        int k = kc[rnd_int(5)];
        long long goal = target > best_n ? target : best_n;
        int gmin = (int)(goal / (2 * k)) + 1;
        int spread = gmin / 8 + 3;
        int ok = 0;
        if (rnd_unit() < 0.5) {
            int cand[16], nc = 0;
            for (int n = 2; n <= 12; n++) {
                int c = n * n * n;
                if (c >= gmin && c <= gmin + spread && c <= GMAX) cand[nc++] = n;
            }
            if (nc > 0) ok = set_group(1, cand[rnd_int(nc)], 0, 0, k);
        }
        for (int tr = 0; tr < 20 && !ok; tr++) {
            int g = gmin + rnd_int(spread);
            if (g < 2) g = 2;
            if (g > GMAX) g = GMAX;
            int opts[12], no = 0;
            for (int c = 1; c <= 12; c++)
                if (g % c == 0 && g / c >= 2) opts[no++] = c;
            int c2 = opts[rnd_int(no)];
            int m = g / c2, r = 1;
            if (c2 > 1) {
                int found = 0;
                for (int t2 = 0; t2 < 200 && !found; t2++) {
                    int cand = 1 + rnd_int(m - 1);
                    if (gcd_i(cand, m) == 1 && powmod_ll(cand, c2, m) == 1 % m) {
                        r = cand;
                        found = 1;
                    }
                }
                if (!found) { c2 = 1; m = g; r = 1; }
            }
            ok = set_group(0, m, c2, r, k);
        }
        if (!ok) continue;

        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
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
# Safe baseline families (always computed first, so a valid graph is in hand).
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


# Known record orders the search should aim to beat. The C engine uses the
# target only to choose group orders; it emits only graphs larger than the
# baseline it was given.
RECORD_TARGET = {(6, 5): 684}


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C search over two group families.
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

    target = RECORD_TARGET.get((d, D), 0)
    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n, target],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
