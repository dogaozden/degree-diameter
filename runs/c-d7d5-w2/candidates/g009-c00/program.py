import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: tabu search over the voltages of a bi-Cayley lift over the
# group Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1, so every vertex has degree DEG. Dart e = l*K + i joins A_i to
# B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j, g*s} for all g.
# Right multiplication by s is a bijection on G, so the lift is valid and
# left multiplication is an automorphism. A BFS from the 2K representatives
# decides the diameter exactly.
#
# Search: each step samples MOVES random moves (voltage change, or swap of
# two targets inside one layer), evaluates each exactly, and takes the best
# non-tabu one even when it is worse than the current state. Aspiration lets
# a tabu move through when it beats the best cost. After STAG steps without
# improvement, the search restarts from the best state with a kick, or from
# a fresh random lift.
#
# Cost = unreached (representative, vertex) pairs + duplicate penalty.
#
# Usage: prog d D K m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define MOVES 24
#define STAG 3000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR, *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ, *tabu, *pbuf;
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

static void random_lift(void) {
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
    for (int e = 0; e < NE; e++) set_perm(e);
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
    {
        int a = r < 0 ? -r : r, b = MM, t;
        while (b) { t = a % b; a = b; b = t; }
        if (a != 1) { printf("0 0\n"); return 0; }
    }
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
    tabu = calloc(NE, sizeof(int));
    pbuf = malloc(sizeof(int) * K);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    if (!dI || !dJ || !dS || !bestS || !bestJ || !tabu || !pbuf || !perm ||
        !adj || !cnt || !fr || !nx || !vis) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    random_lift();
    int cur = cost_fn();
    int best = cur;
    save_best();
    long it = 0;
    int since = 0;

    while (best > 0 && elapsed(t0) < slice) {
        it++;
        int bestMc = BIGCOST, ctype = -1, ce1 = 0, ce2 = 0, cns = 0, nties = 0;

        for (int mv = 0; mv < MOVES; mv++) {
            int type, e1, e2 = 0, ns = 0, old = 0, nc;
            if (K > 1 && rnd01() < 0.25) {
                type = 1;
                int l = rndint(DEG), i1 = rndint(K), i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                e1 = l * K + i1;
                e2 = l * K + i2;
                if (dJ[e1] == dJ[e2]) continue;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                nc = cost_fn();
                t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
            } else {
                type = 0;
                e1 = rndint(NE);
                ns = rndint(G);
                old = dS[e1];
                if (ns == old) continue;
                dS[e1] = ns; set_perm(e1);
                nc = cost_fn();
                dS[e1] = old; set_perm(e1);
                e2 = e1;
            }
            int tb = (tabu[e1] > it) || (type == 1 && tabu[e2] > it);
            if (tb && nc >= best) continue;
            if (nc < bestMc) {
                bestMc = nc; ctype = type; ce1 = e1; ce2 = e2; cns = ns; nties = 1;
            } else if (nc == bestMc) {
                nties++;
                if (rndint(nties) == 0) {
                    ctype = type; ce1 = e1; ce2 = e2; cns = ns;
                }
            }
        }

        if (ctype < 0) {
            /* No admissible move was sampled: take a random voltage change. */
            ce1 = rndint(NE);
            cns = rndint(G);
            dS[ce1] = cns; set_perm(ce1);
            cur = cost_fn();
        } else {
            if (ctype == 0) {
                dS[ce1] = cns; set_perm(ce1);
            } else {
                int t = dJ[ce1]; dJ[ce1] = dJ[ce2]; dJ[ce2] = t;
            }
            cur = bestMc;
            int ten = 1 + rndint(NE / 2 + 1);
            tabu[ce1] = (int)it + ten;
            if (ctype == 1) tabu[ce2] = (int)it + ten;
        }

        if (cur < best) {
            best = cur;
            save_best();
            since = 0;
        } else if (++since > STAG) {
            since = 0;
            if (rnd01() < 0.5) {
                random_lift();
            } else {
                memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
                memcpy(dS, bestS, sizeof(int) * (size_t)NE);
                int kick = NE / 3 + 1;
                for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
                for (int e = 0; e < NE; e++) set_perm(e);
            }
            memset(tabu, 0, sizeof(int) * (size_t)NE);
            cur = cost_fn();
            if (cur < best) {
                best = cur;
                save_best();
            }
        }
    }

    if (best == 0) {
        memcpy(dS, bestS, sizeof(int) * (size_t)NE);
        memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
        for (int e = 0; e < NE; e++) set_perm(e);
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

# Known record orders used as search targets for specific (d, D) cases.
ANCHOR = {(7, 5): 1134}


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
# Group enumeration and candidate pools.
# ----------------------------------------------------------------------------

def _groups(G):
    """All (m, k2, r) with m * k2 = G, m >= 2, describing Z_m x|_r Z_k2."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _pools(lo_n, rng):
    """Candidate (K, m, k2, r) lists giving 2*K*G >= lo_n, smallest orders first."""
    spread = {1: 40, 2: 10, 3: 4}
    pools = {}
    for K in (1, 2, 3):
        g_lo = -(-lo_n // (2 * K))
        items = []
        for G in range(max(2, g_lo), min(3000, g_lo + spread[K])):
            grp = _groups(G)
            rng.shuffle(grp)
            items += [(K, m, k2, r) for (m, k2, r) in grp]
        pools[K] = items
    return pools


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    search_deadline = t0 + 0.92 * budget
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
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: tabu search over voltages of bi-Cayley lifts. Each run uses
    # one exact group from the candidate pools, aiming above the anchor order.
    ref = max(best[0], ANCHOR.get((d, D), 0))
    pools = _pools(ref + 2, rng)
    ptr = {1: 0, 2: 0, 3: 0}
    weights = {1: 0.6, 2: 0.3, 3: 0.1}
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0:
            break
        avail = [K for K in (1, 2, 3) if pools[K]]
        if not avail:
            break
        K = rng.choices(avail, [weights[k] for k in avail])[0]
        pool = pools[K]
        _, m, k2, r = pool[ptr[K] % len(pool)]
        ptr[K] += 1
        slice_s = min(remaining, 10.0)
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
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
