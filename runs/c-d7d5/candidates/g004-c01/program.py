import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A (lift search): simulated annealing over the voltages of a bi-Cayley
# lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Unchanged from the
# parent; it supplies the starting graph.
#
# Usage: prog d D K m k2 r seed slice_seconds
# ----------------------------------------------------------------------------

LIFT_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[64];
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

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
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
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine B (NEW, bold change): direct edge-level annealing on a bipartite
# d-regular graph with H vertices per side. No group structure at all.
#
# Start: a Haar graph (A_a ~ B_{a+s} for d distinct shifts s), which is simple
# and d-regular. Moves: 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep
# every degree and simplicity. Cost = number of ordered vertex pairs at distance
# greater than D, computed with bitset ball expansion. Cost 0 means valid.
#
# Usage: prog d D H seed slice_seconds
# Prints "2H dH" plus edges (A ids 0..H-1, B ids H..2H-1), or "0 0".
# ----------------------------------------------------------------------------

EDGE_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, H, NV, W, NE;
static int *ea, *eb, *adj, *cntv, *bestEb, *pbuf;
static unsigned char *M;
static uint64_t *R0, *R1;
static unsigned char pc16[65536];
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static inline int popc64(uint64_t x) {
    return pc16[x & 0xFFFF] + pc16[(x >> 16) & 0xFFFF] + pc16[(x >> 32) & 0xFFFF] + pc16[x >> 48];
}

/* 2-switch on darts i, j: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Applying it twice
   restores the original state, so it doubles as its own undo. Returns 1 if applied. */
static int sw(int i, int j) {
    int a1 = ea[i], a2 = ea[j];
    if (a1 == a2) return 0;
    int b1 = eb[i], b2 = eb[j];
    if (b1 == b2) return 0;
    if (M[a1 * H + b2] || M[a2 * H + b1]) return 0;
    M[a1 * H + b1] = 0; M[a2 * H + b2] = 0;
    M[a1 * H + b2] = 1; M[a2 * H + b1] = 1;
    eb[i] = b2; eb[j] = b1;
    return 1;
}

static long long cost_fn(void) {
    memset(cntv, 0, sizeof(int) * (size_t)NV);
    for (int i = 0; i < NE; i++) {
        int a = ea[i], b = H + eb[i];
        adj[a * DEG + cntv[a]++] = b;
        adj[b * DEG + cntv[b]++] = a;
    }
    memset(R0, 0, sizeof(uint64_t) * (size_t)NV * W);
    for (int v = 0; v < NV; v++) R0[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    uint64_t *cur = R0, *nxt = R1;
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int t = 0; t < DEG; t++) {
                const uint64_t *u = cur + (size_t)adj[v * DEG + t] * W;
                for (int w = 0; w < W; w++) o[w] |= u[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long total = 0;
    for (int v = 0; v < NV; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(c[w]);
        total += NV - pc;
    }
    return total;
}

static void save_best(void) {
    memcpy(bestEb, eb, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D H seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    H = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    if (DEG < 1 || DIAM < 1 || H < DEG || H > 4000) {
        printf("0 0\n");
        return 0;
    }
    NV = 2 * H;
    W = (NV + 63) / 64;
    NE = H * DEG;

    for (int i = 0; i < 65536; i++) pc16[i] = (unsigned char)((i >> 1) ? pc16[i >> 1] + (i & 1) : (i & 1));

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEF12345ULL;
    if (rs == 0) rs = 1;

    ea = malloc(sizeof(int) * NE);
    eb = malloc(sizeof(int) * NE);
    bestEb = malloc(sizeof(int) * NE);
    adj = malloc(sizeof(int) * (size_t)NV * DEG);
    cntv = malloc(sizeof(int) * NV);
    pbuf = malloc(sizeof(int) * H);
    M = calloc((size_t)H * H, 1);
    R0 = malloc(sizeof(uint64_t) * (size_t)NV * W);
    R1 = malloc(sizeof(uint64_t) * (size_t)NV * W);
    if (!ea || !eb || !bestEb || !adj || !cntv || !pbuf || !M || !R0 || !R1) {
        printf("0 0\n");
        return 0;
    }
    for (int a = 0; a < H; a++)
        for (int t = 0; t < DEG; t++) ea[a * DEG + t] = a;

    clock_t t0 = clock();
    int found = 0;
    long long bestCost = -1;
    const int RL = 20000;

    while (!found && elapsed(t0) < slice) {
        int fresh = (bestCost < 0 || rnd01() < 0.2);
        double T0;
        if (fresh) {
            for (int i = 0; i < H; i++) pbuf[i] = i;
            for (int k = 0; k < DEG; k++) {
                int j = k + rndint(H - k);
                int tmp = pbuf[k]; pbuf[k] = pbuf[j]; pbuf[j] = tmp;
            }
            for (int a = 0; a < H; a++)
                for (int t = 0; t < DEG; t++)
                    eb[a * DEG + t] = (a + pbuf[t]) % H;
            T0 = 2.0;
        } else {
            memcpy(eb, bestEb, sizeof(int) * (size_t)NE);
            T0 = 0.8;
        }
        memset(M, 0, (size_t)H * H);
        for (int i = 0; i < NE; i++) M[ea[i] * H + eb[i]] = 1;
        if (!fresh) {
            int kick = NE / 20 + 2, done = 0, tries = 0;
            while (done < kick && tries < kick * 50) {
                tries++;
                if (sw(rndint(NE), rndint(NE))) done++;
            }
        }
        long long cur = cost_fn();
        if (bestCost < 0 || cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 63) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.03;
            int i = rndint(NE), j = rndint(NE);
            if (!sw(i, j)) continue;
            long long nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                sw(i, j);
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", NV, NE);
        for (int i = 0; i < NE; i++) printf("%d %d\n", ea[i], H + eb[i]);
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
# Group sampling for the lift engine.
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


# ----------------------------------------------------------------------------
# Driver: exact constructions, then lift search (safe improvement), then the
# direct edge-annealing engine (the bold new construction) for the rest of
# the budget. Every accepted graph is checked with lib.is_valid.
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

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

    # Phase 1: lift search (parent engine) for a share of the budget.
    lift_deadline = start + 0.4 * budget
    while True:
        remaining = lift_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 12.0)
        k = rng.choice([1, 1, 2, 2, 3])
        base = best[0] // (2 * k)
        target = base + 1 + rng.randrange(0, max(2, base // 10 + 1))
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                LIFT_C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    # Phase 2 (bold change): direct edge-level annealing of a d-regular bipartite
    # graph with H = best_order/2 + 1 vertices per side. Each success is a strict
    # improvement, so the target climbs one step at a time.
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        h = max(d, best[0] // 2 + 1)
        slice_s = min(remaining - 1.0, 15.0)
        try:
            out = lib.run_c(
                EDGE_C_SOURCE,
                [d, D, h, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
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
