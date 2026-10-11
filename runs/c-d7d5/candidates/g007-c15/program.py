import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: voltage search on bi-Cayley lifts over Z_m x|_r Z_k2
# (element (a, b) coded as a*k2 + b).
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1. Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e]:
# A_{i,g} ~ B_{j,g*s} for all g. Left multiplication is an automorphism,
# so BFS from the 2K representatives decides the diameter exactly.
#
# Two search modes (argv[9]):
#   0 = simulated annealing with reheating from the best state (as before)
#   1 = TABU search: each step samples CAND random moves, evaluates each,
#       and applies the best non-tabu one (aspiration if it beats the best).
#       Moving a voltage forbids returning to the old voltage for a while;
#       moving a target forbids returning to the old target. A phase ends
#       after STALL steps without improving its own best; the next phase
#       restarts from a kicked copy of the global best.
#
# Cost = unreached (rep, vertex) pairs + duplicate penalty.
#
# Usage: prog d D K m k2 r seed slice_seconds [mode]
# Prints a valid graph ("n m" + edges) or "0 0".
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
#define CAND 40
#define TEN_J 7
#define TEN_S 9
#define STALL 1500
#define RL 60000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[64];
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static int *tabuS, *tabuJ;
static int *pbuf;
static int bestCost = BIGCOST;
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
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
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
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

static void random_start(void) {
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
    for (int e = 0; e < NE; e++) {
        dS[e] = rndint(G);
        set_perm(e);
    }
}

static void kick_best(int kick) {
    memcpy(dS, bestS, sizeof(int) * (size_t)NE);
    memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
    for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
    for (int e = 0; e < NE; e++) set_perm(e);
}

/* Simulated annealing phase. Returns 1 if a zero-cost state is current. */
static int anneal_phase(clock_t t0, double slice, double T0) {
    int cur = cost_fn();
    if (cur < bestCost) { bestCost = cur; save_best(); }
    if (cur == 0) return 1;
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
        if (cur == 0) return 1;
    }
    return 0;
}

/* Tabu phase: best sampled non-tabu move per step. Returns 1 if solved. */
static int tabu_phase(clock_t t0, double slice) {
    int cur = cost_fn();
    if (cur < bestCost) { bestCost = cur; save_best(); }
    if (cur == 0) return 1;
    memset(tabuS, 0, sizeof(int) * (size_t)NE * G);
    memset(tabuJ, 0, sizeof(int) * (size_t)NE * K);
    int phaseBest = cur;
    int stall = 0;
    for (int it = 1; ; it++) {
        if ((it & 31) == 0 && elapsed(t0) >= slice) break;
        if (stall > STALL) break;

        int bc = BIGCOST, btype = -1, be1 = 0, be2 = 0, bns = 0;
        for (int c = 0; c < CAND; c++) {
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int n1 = dJ[e2], n2 = dJ[e1];
                int tb = (tabuJ[e1 * K + n1] > it) || (tabuJ[e2 * K + n2] > it);
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                if (tb && nc >= bestCost) continue;
                if (nc < bc || (nc == bc && rndint(2))) {
                    bc = nc; btype = 1; be1 = e1; be2 = e2;
                }
            } else {
                int e = rndint(NE);
                int ns = rndint(G);
                int old = dS[e];
                if (ns == old) continue;
                int tb = tabuS[e * G + ns] > it;
                dS[e] = ns; set_perm(e);
                int nc = cost_fn();
                dS[e] = old; set_perm(e);
                if (tb && nc >= bestCost) continue;
                if (nc < bc || (nc == bc && rndint(2))) {
                    bc = nc; btype = 0; be1 = e; bns = ns;
                }
            }
        }
        if (btype < 0) { stall++; continue; }

        if (btype == 1) {
            int e1 = be1, e2 = be2;
            tabuJ[e1 * K + dJ[e1]] = it + TEN_J;
            tabuJ[e2 * K + dJ[e2]] = it + TEN_J;
            int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
        } else {
            int e = be1;
            tabuS[e * G + dS[e]] = it + TEN_S;
            dS[e] = bns;
            set_perm(e);
        }
        cur = bc;
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur < phaseBest) { phaseBest = cur; stall = 0; } else stall++;
        if (cur == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice [mode]\n");
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
    int mode = (argc > 9) ? atoi(argv[9]) : 0;

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 60) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
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
    tabuS = malloc(sizeof(int) * (size_t)NE * G);
    tabuJ = malloc(sizeof(int) * (size_t)NE * K);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    pbuf = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !tabuS || !tabuJ || !perm ||
        !adj || !cnt || !fr || !nx || !vis || !pbuf) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    while (!found && elapsed(t0) < slice) {
        int fresh = (bestCost >= BIGCOST) || (rnd01() < 0.2);
        if (fresh) random_start();
        else kick_best(NE / 8 + 1);
        if (mode == 1) found = tabu_phase(t0, slice);
        else found = anneal_phase(t0, slice, fresh ? 2.0 : 0.8);
    }

    if (found) {
        /* The current state is the zero-cost state at the moment of return. */
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions.
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
# Group menu: every valid (m, k2, r) with m*k2 about target (new helper).
# Enumerating all valid r for each small k2 lets the search choose uniformly
# over the menu instead of over a single random r per draw.
# ----------------------------------------------------------------------------

def _group_options(target):
    """Return (m, k2, r) triples describing Z_m x|_r Z_k2 with m*k2 >= target, m minimal."""
    opts = []
    for k2 in range(1, 25):
        m = max(2, -(-target // k2))
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for c in range(1, m):
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                opts.append((m, k2, c))
    return opts


# ----------------------------------------------------------------------------
# Search driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        # Araujo-Pardo & Lopez record for D = 3, d = q + 2 with q a prime power.
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except (ValueError, RuntimeError):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: the C engine searches voltages of bi-Cayley lifts. Each call
    # targets a group order just above best / (2k), so every success is a strict
    # improvement. About 60% of slices use tabu mode, the rest annealing.
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 12.0)
        k = rng.choice([1, 1, 2, 2, 3])
        base = best[0] // (2 * k)
        target = base + 1 + rng.randrange(0, max(2, base // 10 + 1))
        opts = _group_options(target)
        if not opts:
            continue
        m, k2, r = rng.choice(opts)
        mode = 1 if rng.random() < 0.6 else 0
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}", mode],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
