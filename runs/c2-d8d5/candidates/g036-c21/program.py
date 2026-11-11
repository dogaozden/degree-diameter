import math
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift search over semidirect products Z_m x| Z_k2.
#
# A candidate is k blocks per side, a group G of order m*k2 and d "layers".
# Layer l joins A-block i to B-block P[l][i] with voltage S[l][i]: the edges
# are (i,g)-(j, g*s). Left multiplication by G is an automorphism that fixes
# each block, so the diameter test only needs BFS from one representative per
# block (2k BFS runs), not from every vertex. The cost is the number of
# unreached (representative, vertex) pairs plus a large penalty for repeated
# darts (which would create multi-edges). Simulated annealing moves voltages
# and layer permutations. Each success saves the graph and the group size grows.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 64
#define MAXK 8
#define MAXPW 64

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int ri(int n) { return (int)(rnd() % (u64)n); }
static double rd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ---- group Z_m x|_r Z_k2, element a*k2+b, (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1+b2) ---- */
static int gm = 1, gk2 = 1, gr = 1, gG = 1;
static int pw[MAXPW];

static int gmul(int x, int y) {
    int a1 = x / gk2, b1 = x % gk2;
    int a2 = y / gk2, b2 = y % gk2;
    int a = (a1 + pw[b1] * a2) % gm;
    int b = (b1 + b2) % gk2;
    return a * gk2 + b;
}

static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    int t = (pw[nb] * a) % gm;
    int na = (gm - t) % gm;
    return na * gk2 + nb;
}

static void set_group(int m, int k2, int r) {
    gm = m; gk2 = k2; gr = r; gG = m * k2;
    pw[0] = 1 % gm;
    for (int b = 1; b < gk2; b++) pw[b] = (int)((long long)pw[b - 1] * gr % gm);
}

/* ---- candidate groups ---- */
typedef struct { int m, k2, r, G; } Cand;
static Cand *cand = NULL;
static int ncand = 0, capcand = 0;

static void push_cand(int m, int k2, int r) {
    if (ncand >= capcand) {
        int nc = capcand ? capcand * 2 : 4096;
        Cand *t = realloc(cand, sizeof(Cand) * (size_t)nc);
        if (!t) return;
        cand = t;
        capcand = nc;
    }
    cand[ncand].m = m;
    cand[ncand].k2 = k2;
    cand[ncand].r = r;
    cand[ncand].G = m * k2;
    ncand++;
}

static int powmod(int b, int e, int m) {
    long long res = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) res = res * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)res;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int cmp_cand(const void *a, const void *b) {
    int ga = ((const Cand *)a)->G, gb = ((const Cand *)b)->G;
    return (ga > gb) - (ga < gb);
}

static void enumerate(int GMAX) {
    for (int k2 = 1; k2 <= 40 && k2 <= GMAX; k2++) {
        for (int m = 2; m * k2 <= GMAX; m++) {
            if (k2 == 1) { push_cand(m, 1, 1); continue; }
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k2, m) != 1 % m) continue;
                push_cand(m, k2, r);
            }
        }
    }
}

/* ---- lift state ---- */
static int K = 1, dd = 1, DD = 1, NV = 0;
static int P[MAXD][MAXK], Pinv[MAXD][MAXK], S[MAXD][MAXK];
static int *nbt = NULL, *vis = NULL, *qu = NULL;
static int stampv = 0;
static int badBlock = -1;

static int best_n = 0, best_m = 0, found = 0;
static int *beU = NULL, *beV = NULL;

static void swap_layer(int l, int a, int b) {
    int t = P[l][a]; P[l][a] = P[l][b]; P[l][b] = t;
    Pinv[l][P[l][a]] = a;
    Pinv[l][P[l][b]] = b;
}

static void random_state(void) {
    for (int l = 0; l < dd; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = ri(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            P[l][i] = perm[i];
            Pinv[l][perm[i]] = i;
        }
        for (int i = 0; i < K; i++) S[l][i] = ri(gG);
    }
}

static void build_table(void) {
    int G = gG;
    for (int v = 0; v < NV; v++) {
        int b = v / G, x = v % G;
        int *row = nbt + (size_t)v * dd;
        if (b < K) {
            for (int l = 0; l < dd; l++) {
                int j = P[l][b];
                row[l] = (K + j) * G + gmul(x, S[l][b]);
            }
        } else {
            int j = b - K;
            for (int l = 0; l < dd; l++) {
                int i = Pinv[l][j];
                row[l] = i * G + gmul(x, ginv(S[l][i]));
            }
        }
    }
}

static int dup_count(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < dd; l1++)
            for (int l2 = l1 + 1; l2 < dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return dup;
}

/* Cost 0 iff the lift is simple and has diameter <= DD. Left translation is an
   automorphism, so BFS from one representative per block suffices. */
static long long evaluate(void) {
    int G = gG;
    build_table();
    int dup = dup_count();
    long long unre = 0;
    badBlock = -1;
    for (int b = 0; b < 2 * K; b++) {
        int stamp = ++stampv;
        int src = b * G;
        int qh = 0, qt = 0;
        qu[qt++] = src;
        vis[src] = stamp;
        for (int lev = 0; lev < DD && qh < qt; lev++) {
            int end = qt;
            while (qh < end) {
                int v = qu[qh++];
                const int *row = nbt + (size_t)v * dd;
                for (int l = 0; l < dd; l++) {
                    int u = row[l];
                    if (vis[u] != stamp) {
                        vis[u] = stamp;
                        qu[qt++] = u;
                    }
                }
            }
        }
        if (qt < NV) {
            unre += NV - qt;
            if (badBlock < 0) {
                for (int v = 0; v < NV; v++) {
                    if (vis[v] != stamp) { badBlock = v / G; break; }
                }
            }
        }
    }
    return unre + (long long)NV * dup;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < K * gG; v++) {
        for (int l = 0; l < dd; l++) {
            beU[m] = v;
            beV[m] = nbt[(size_t)v * dd + l];
            m++;
        }
    }
    best_m = m;
    best_n = NV;
    found = 1;
}

static void consider_save(void) {
    if (NV > best_n) save_best();
}

static double elapsed(clock_t c0) {
    return (double)(clock() - c0) / CLOCKS_PER_SEC;
}

static void anneal(int iters, double tlimit, clock_t c0) {
    random_state();
    long long cost = evaluate();
    if (cost == 0) { consider_save(); return; }
    double T0 = 2.0 + 0.02 * (double)cost, T1 = 0.2;
    long long bestc = cost;
    int lastImp = 0;
    for (int it = 0; it < iters; it++) {
        if ((it & 255) == 0 && elapsed(c0) >= tlimit) break;
        if (it - lastImp > 2500) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int oldBad = badBlock;
        int kind = (K >= 2 && rd() < 0.25);
        int useBad = (oldBad >= 0 && rd() < 0.5);
        int l = ri(dd), i;
        if (useBad) i = (oldBad < K) ? oldBad : Pinv[l][oldBad - K];
        else i = ri(K);
        int i2 = -1, old = 0;
        if (kind) {
            i2 = ri(K - 1);
            if (i2 >= i) i2++;
            swap_layer(l, i, i2);
        } else {
            old = S[l][i];
            int nw = ri(gG);
            if (nw == old) continue;
            S[l][i] = nw;
        }
        long long nc = evaluate();
        if (nc <= cost || rd() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            if (cost < bestc) { bestc = cost; lastImp = it; }
            if (cost == 0) { consider_save(); return; }
        } else {
            if (kind) swap_layer(l, i, i2);
            else S[l][i] = old;
            badBlock = oldBad;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    best_n = atoi(argv[5]);
    int GMAX = argc > 6 ? atoi(argv[6]) : 1000;
    if (dd < 1 || dd > MAXD || DD < 1 || GMAX < 2 || best_n < 0) {
        printf("0 0\n");
        return 0;
    }

    int NVmax = 2 * MAXK * GMAX;
    nbt = malloc(sizeof(int) * (size_t)NVmax * dd);
    vis = calloc((size_t)NVmax, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)NVmax);
    beU = malloc(sizeof(int) * ((size_t)MAXK * GMAX * dd + 16));
    beV = malloc(sizeof(int) * ((size_t)MAXK * GMAX * dd + 16));
    if (!nbt || !vis || !qu || !beU || !beV) { printf("0 0\n"); return 0; }

    enumerate(GMAX);
    if (ncand == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)ncand, sizeof(Cand), cmp_cand);

    clock_t c0 = clock();
    int nocand = 0;
    while (elapsed(c0) < limit) {
        int k = 1 + ri(4);
        long long lo = best_n / (2 * k) + 1;   /* need 2*k*G > best_n */
        int a = 0, b = ncand;
        while (a < b) {
            int mid = (a + b) / 2;
            if ((long long)cand[mid].G < lo) a = mid + 1;
            else b = mid;
        }
        if (a >= ncand) {
            if (++nocand > 200) break;
            continue;
        }
        int span = (int)(lo / 6) + 8;
        if (span > ncand - a) span = ncand - a;
        int pick = a + ri(span);
        set_group(cand[pick].m, cand[pick].k2, cand[pick].r);
        K = k;
        NV = 2 * K * gG;
        int before = best_n;
        anneal(6000, limit, c0);
        if (best_n > before) nocand = 0;
    }

    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", beU[i], beV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact record construction (calibration case)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main search: C bi-Cayley lift annealer seeded with the current best order.
    budget = time_limit * 0.85 - (time.monotonic() - t0) - 3.0
    if budget >= 2.0:
        gmax = max(64, min(lib.moore_bound(d, D) // 2 + 8, 3000))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed % (1 << 30), f"{budget:.2f}", best[0], gmax],
                            timeout=budget + 20.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
