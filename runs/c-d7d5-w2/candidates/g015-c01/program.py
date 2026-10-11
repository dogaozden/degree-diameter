import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine: tabu-guided search over bi-Cayley lifts with Z_m x|_r Z_k2 voltages.
#
# Base graph: K A-vertices and K B-vertices, each joined to every other base
# vertex by DEG darts. Layer l is a permutation dJ (so degrees stay regular),
# and each dart carries a group element dS. Vertex (i, x) on side A is joined
# to (j, x*g) on side B for each dart (i, j, g). Left translation is an
# automorphism, so it is enough to measure distance from the 2K base vertices.
#
# Moves: change one dart's group element, or swap two targets within a layer.
# Each step samples NCAND moves and takes the best non-tabu one. Stagnation
# triggers a kick from the best state.
#
# Usage: prog d D K m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

TABU_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define TT 12
#define NCAND 24
#define STAG 3000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx, *pbuf;
static int *bestS, *bestJ, *tabuS, *tabuJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static double slice;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

static void set_all_perm(void) {
    for (int e = 0; e < NE; e++) set_perm(e);
}

static void random_init(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) pbuf[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pbuf[i]; pbuf[i] = pbuf[j]; pbuf[j] = t;
        }
        for (int i = 0; i < K; i++) {
            dI[l * K + i] = i;
            dJ[l * K + i] = pbuf[i];
        }
    }
    for (int e = 0; e < NE; e++) dS[e] = rndint(G);
    set_all_perm();
}

/* Total penalty: distance excess and unreached vertices from the 2K base
   vertices, plus a penalty for duplicate darts (identical i, j, g). */
static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
    }
    return total + PEN * dup;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) { printf("0 0\n"); return 0; }
    if ((long long)MM * K2 > 20000LL) { printf("0 0\n"); return 0; }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;
    if (G < DEG || N > 40000) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    pbuf = malloc(sizeof(int) * K);
    tabuS = calloc((size_t)NE * G, sizeof(int));
    tabuJ = calloc((size_t)NE * K, sizeof(int));
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt ||
        !fr || !nx || !vis || !pbuf || !tabuS || !tabuJ) {
        printf("0 0\n");
        return 0;
    }

    t0 = clock();
    random_init();
    int cur = cost_fn();
    int bestCost = cur;
    save_best();
    int found = (cur == 0);
    long it = 0;
    long since = 0;

    while (!found && elapsed() < slice) {
        it++;
        int bType = -1, bE1 = 0, bE2 = 0, bVal = 0, bCost = BIGCOST;

        for (int c = 0; c < NCAND; c++) {
            if (K > 1 && rnd01() < 0.35) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                if (dJ[e1] == dJ[e2]) continue;
                int v = dJ[e2];
                int tabu = tabuJ[e1 * K + v] > it;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                if (tabu && !(nc < bestCost)) continue;
                if (nc < bCost) { bCost = nc; bType = 1; bE1 = e1; bE2 = e2; }
            } else {
                int e = rndint(NE);
                int ns = rndint(G);
                if (ns == dS[e]) continue;
                int old = dS[e];
                int tabu = tabuS[e * G + ns] > it;
                dS[e] = ns; set_perm(e);
                int nc = cost_fn();
                dS[e] = old; set_perm(e);
                if (tabu && !(nc < bestCost)) continue;
                if (nc < bCost) { bCost = nc; bType = 0; bE1 = e; bVal = ns; }
            }
        }

        if (bType < 0) continue;

        if (bType == 0) {
            int e = bE1;
            tabuS[e * G + dS[e]] = (int)(it + TT);
            dS[e] = bVal;
            set_perm(e);
        } else {
            int e1 = bE1, e2 = bE2;
            tabuJ[e1 * K + dJ[e1]] = (int)(it + TT);
            tabuJ[e2 * K + dJ[e2]] = (int)(it + TT);
            int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
        }
        cur = bCost;

        if (cur < bestCost) { bestCost = cur; save_best(); since = 0; }
        else since++;
        if (cur == 0) { found = 1; break; }

        if (since > STAG) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 4 + 2;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            set_all_perm();
            cur = cost_fn();
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur == 0) { found = 1; break; }
            since = 0;
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
    memcpy(dS, bestS, sizeof(int) * (size_t)NE);
    set_all_perm();
    printf("%d %d\n", N, NE * G);
    for (int e = 0; e < NE; e++) {
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
        }
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions and fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group sampling and the search driver.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m = max(2, -(-target // k2))
        r = 1
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m)
                     if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        if m * k2 >= target:
            return m, k2, r
    return None


def _search(d, D, rng, state, until):
    """Repeatedly run the tabu engine on random bi-Cayley lifts that beat the current best."""
    fails = 0
    while fails < 30:
        remaining = until - time.monotonic()
        if remaining < 1.5:
            break
        slice_s = min(remaining, 15.0)
        best_n = state[0][0]
        k = rng.choice([1, 1, 2, 2, 3, 4, 6])
        g_need = best_n // (2 * k) + 1
        target = g_need + rng.randrange(0, 4)
        grp = _sample_group(target, rng)
        if grp is None:
            fails += 1
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                TABU_C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            fails += 1
            continue
        if n > best_n and lib.is_valid(n, e, d, D):
            state[0] = (n, e)
            fails = 0
        else:
            fails += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    state = [fallback]

    def consider(cand):
        n, e = cand
        if n > state[0][0] and lib.is_valid(n, e, d, D):
            state[0] = (n, e)

    if D == 2:
        return state[0]

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return state[0]

    try:
        _search(d, D, rng, state, deadline)
    except Exception:
        pass

    best = state[0]
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
