import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: breakout local search (clause weighting) over the voltages of a
# bi-Cayley lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base graph: K vertices per side, DEG layers. Layer l is a permutation p_l of
# 0..K-1, so every vertex has degree DEG. Dart e = l*K + i joins A_{i,g} to
# B_{dJ[e], g*s} with s = dS[e]. Left multiplication is an automorphism, so a
# BFS from the 2K identity vertices decides the diameter exactly.
#
# Cost = sum over unreached (representative, vertex) pairs of their weights,
# plus PEN per duplicate dart. Weights start at 1. When the search stalls, the
# weights of currently unreached pairs grow, which reshapes the landscape.
# Moves: change one voltage, or swap two targets inside one layer (keeps degrees).
# Each random restart ends with a unit-weight coordinate polish when close.
#
# Usage: prog DEG DIAM K m k2 r seed slice_seconds
# Prints a graph ("n m" + edges) on success, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define PEN 1000
#define STUCK 40
#define BREAK_ITERS 20000
#define POLISH_T 60

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[64];
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx, *bestJ, *bestS, *pbuf;
static uint32_t *vis;
static uint32_t stamp = 0;
static long long *wt;
static uint64_t rs = 88172645463325252ULL;
static double deadline;
static long long g_raw = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * (long long)c) % MM;
    return (int)(t * K2 + (b + d) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

/* Returns weighted cost (weights of unreached pairs + PEN * duplicates).
   Sets g_raw to the unweighted cost. If bump != 0, unreached pairs get +1 weight. */
static long long eval(int bump) {
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

    long long wsum = 0, raw = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1;
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
            int *tmp = cur;
            cur = nxt;
            nxt = tmp;
            fn = nn;
        }
        long long *w = wt + (size_t)ri * (size_t)N;
        for (int v = 0; v < N; v++) {
            if (vis[v] != stamp) {
                raw++;
                wsum += w[v];
                if (bump) w[v]++;
            }
        }
    }
    g_raw = raw + (long long)PEN * dup;
    return wsum + (long long)PEN * dup;
}

static void reset_weights(void) {
    long long total = (long long)2 * K * N;
    for (long long j = 0; j < total; j++) wt[j] = 1;
}

static void save_best(void) {
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
}

static void load_state(const int *J, const int *S) {
    memcpy(dJ, J, sizeof(int) * (size_t)NE);
    memcpy(dS, S, sizeof(int) * (size_t)NE);
    for (int e = 0; e < NE; e++) set_perm(e);
}

/* Breakout local search from the current state. Leaves the state at the best
   raw cost found and returns that raw cost. Weights must be set beforehand. */
static long long breakout(void) {
    long long wc = eval(0);
    long long rc = g_raw;
    long long bestRaw = rc;
    save_best();
    int stuck = 0;
    for (long t = 0; t < BREAK_ITERS && rc > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        if (K > 1 && rndint(4) == 0) {
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tmp = dJ[e1];
            dJ[e1] = dJ[e2];
            dJ[e2] = tmp;
            long long wc2 = eval(0);
            if (wc2 <= wc) {
                stuck = (wc2 < wc) ? 0 : stuck + 1;
                wc = wc2;
                rc = g_raw;
            } else {
                tmp = dJ[e1];
                dJ[e1] = dJ[e2];
                dJ[e2] = tmp;
                stuck++;
            }
        } else {
            int e = rndint(NE);
            int old = dS[e];
            int ns = rndint(G);
            if (ns == old) continue;
            dS[e] = ns;
            set_perm(e);
            long long wc2 = eval(0);
            if (wc2 <= wc) {
                stuck = (wc2 < wc) ? 0 : stuck + 1;
                wc = wc2;
                rc = g_raw;
            } else {
                dS[e] = old;
                set_perm(e);
                stuck++;
            }
        }
        if (rc < bestRaw) {
            bestRaw = rc;
            save_best();
        }
        if (stuck >= STUCK) {
            eval(1);            /* raise weights of unreached pairs */
            wc = eval(0);
            rc = g_raw;
            stuck = 0;
        }
    }
    load_state(bestJ, bestS);
    return bestRaw;
}

/* Best-improvement coordinate sweeps over every dart value with unit weights. */
static void polish(void) {
    reset_weights();
    long long cost = eval(0);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < DEG && cost != 0; l++) {
            for (int i = 0; i < K; i++) {
                if (now_s() > deadline) {
                    eval(0);
                    return;
                }
                int e = l * K + i;
                int old = dS[e];
                int bestv = old;
                long long bestc = cost;
                for (int s = 0; s < G; s++) {
                    if (s == old) continue;
                    dS[e] = s;
                    set_perm(e);
                    long long c2 = eval(0);
                    if (c2 < bestc) {
                        bestc = c2;
                        bestv = s;
                    }
                }
                dS[e] = bestv;
                set_perm(e);
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                }
                if (cost == 0) break;
            }
        }
    }
    eval(0);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 60 || r < 1) {
        printf("0 0\n");
        return 0;
    }
    int rr = r % MM;
    if (gcd_int(rr == 0 ? 1 : rr, MM) != 1) {
        printf("0 0\n");
        return 0;
    }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * rr % MM);
    if ((((long long)POWR[K2 - 1] * rr) % MM) != 1 % MM) {
        printf("0 0\n");
        return 0;
    }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;
    if (G > 100000 || N > 400000) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd64();

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(uint32_t));
    wt = malloc(sizeof(long long) * (size_t)2 * K * N);
    pbuf = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestJ || !bestS || !perm || !adj || !cnt || !fr ||
        !nx || !vis || !wt || !pbuf) {
        printf("0 0\n");
        return 0;
    }

    deadline = now_s() + slice;
    int found = 0;
    while (!found && now_s() < deadline) {
        /* Fresh random lift. */
        for (int l = 0; l < DEG; l++) {
            for (int i = 0; i < K; i++) pbuf[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = pbuf[i];
                pbuf[i] = pbuf[j];
                pbuf[j] = t;
            }
            for (int i = 0; i < K; i++) {
                dI[l * K + i] = i;
                dJ[l * K + i] = pbuf[i];
            }
        }
        for (int e = 0; e < NE; e++) dS[e] = rndint(G);
        for (int e = 0; e < NE; e++) set_perm(e);

        reset_weights();
        long long best = breakout();
        if (best > 0 && best <= POLISH_T && now_s() < deadline) polish();
        eval(0);
        if (g_raw == 0) found = 1;
    }

    if (found) {
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
# Group sampling and the search driver.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        r = 1  # r = 1 is the direct product, always valid
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 5.0))
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Breakout search over bi-Cayley lifts. Each call targets a group order whose
    # lift is strictly larger than the current best, so every success improves it.
    if d >= 3 and D >= 3:
        failures = 0
        while failures < 3:
            elapsed = time.monotonic() - start
            remaining = deadline - time.monotonic()
            if remaining < 2.0:
                break
            slice_s = min(remaining - 1.0, 14.0)
            K = rng.choice([1, 1, 1, 2])
            base = best[0] // (2 * K)
            target = base + 1 + rng.randrange(0, max(2, base // 20 + 1))
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
            timeout = min(slice_s + 5.0, time_limit - elapsed - 1.0)
            if timeout < 1.0:
                break
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, K, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    timeout=timeout,
                )
            except RuntimeError:
                failures += 1
                continue
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
