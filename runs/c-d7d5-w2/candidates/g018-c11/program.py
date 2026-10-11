import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley lift
# over the group Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1. Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e]:
# A_{i,g} ~ B_{j,g*s} for all g.
#
# NEW: base-vertex insertion warm start. The engine may read a warm state
# from stdin (encoded as a graph "NE NE" followed by NE lines "dJ dS"). The
# Python driver grows a valid lift from K to K+1 base vertices by appending,
# in every layer, a fixed-point dart K -> K with a random voltage. The result
# is a valid permutation per layer, so degrees stay DEG, and the group order
# stays fixed, so the order grows by exactly 2*G. Annealing then repairs the
# diameter starting from that state.
#
# Cost: excess distance summed over BFS from the 2K representatives. Zero
# iff the lift has diameter <= DIAM, plus a duplicate-dart penalty.
#
# Output: graph text, then a line "LIFT K m k2 r" and NE lines "dJ dS".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 8000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

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

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;

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
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    for (int e = 0; e < NE; e++) dI[e] = e % K;

    /* Optional warm start: "NE NE" then NE lines "dJ dS". */
    int warm_pending = 0;
    int wn = 0, wm = 0;
    if (scanf("%d %d", &wn, &wm) == 2 && wm == NE) {
        warm_pending = 1;
        for (int e = 0; e < NE; e++) {
            int j = -1, s = -1;
            if (scanf("%d %d", &j, &s) != 2 || j < 0 || j >= K || s < 0 || s >= G) {
                warm_pending = 0;
                break;
            }
            dJ[e] = j;
            dS[e] = s;
        }
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (warm_pending) {
            warm_pending = 0;
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.5;
        } else if (bestCost >= BIGCOST || rnd01() < 0.25) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) {
                dS[e] = rndint(G);
                set_perm(e);
            }
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
        printf("LIFT %d %d %d %d\n", K, MM, K2, r);
        for (int e = 0; e < NE; e++) printf("%d %d\n", dJ[e], dS[e]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (kept for smaller D, used as fallbacks).
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
# Group sampling and lift-output helpers.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m = max(2, -(-target // k2))
        r = 1  # r = 1 is the direct product, always valid
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def _split_output(out):
    """Split C output into (graph_text, lift) where lift = (K, m, k2, r, dJ, dS). (None, None) if no graph."""
    if "LIFT" not in out:
        return None, None
    gtext, _, ltext = out.partition("LIFT")
    t = ltext.split()
    if len(t) < 4:
        return None, None
    K, m, k2, r = (int(x) for x in t[:4])
    nums = [int(x) for x in t[4:]]
    if len(nums) % 2:
        return None, None
    return gtext, (K, m, k2, r, nums[0::2], nums[1::2])


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    search_deadline = start + 0.92 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
        if D == 3 and pg is not None and lib.is_prime_power(d - 1):
            return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Lift search with base-vertex growth. `lift` is the largest valid lift so far.
    lift = None
    lift_n = 0
    grow_fail = 0
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        seed_c = rng.randrange(1, 10 ** 9)
        grow = lift is not None and grow_fail < 3 and rng.random() < 0.7
        if grow:
            # Insert one base vertex per side, keeping the group and old voltages.
            K, m, k2, r, dJ, dS = lift
            Kn = K + 1
            nJ, nS = [], []
            for l in range(d):
                nJ.extend(dJ[l * K:(l + 1) * K])
                nS.extend(dS[l * K:(l + 1) * K])
                nJ.append(K)
                nS.append(rng.randrange(m * k2))
            args = [d, D, Kn, m, k2, r, seed_c, f"{slice_s:.2f}"]
            stdin_graph = (len(nJ), list(zip(nJ, nS)))
        else:
            k = rng.choice([1, 1, 2, 2, 3])
            want = max(best[0], lift_n) * (1.0 + rng.uniform(0.0, 0.1))
            target = max(2, math.ceil(want / (2 * k)))
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
            args = [d, D, k, m, k2, r, seed_c, f"{slice_s:.2f}"]
            stdin_graph = None
            grow_fail = 0
        try:
            out = lib.run_c(C_SOURCE, args, stdin_graph=stdin_graph, timeout=slice_s + 10.0)
        except RuntimeError:
            break

        gtext, L = _split_output(out)
        improved_lift = False
        if gtext is not None and L is not None:
            try:
                n, e = lib.parse_graph_text(gtext)
            except ValueError:
                n = 0
            if n > lift_n and len(L[4]) == d * L[0] and lib.is_valid(n, e, d, D):
                lift = L
                lift_n = n
                improved_lift = True
                if n > best[0]:
                    best = (n, e)
        if improved_lift:
            grow_fail = 0
        elif grow:
            grow_fail += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
