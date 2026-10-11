import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New idea: degree-completed projective-plane bases.
#
# A bipartite base multigraph B (K vertices per side) is lifted over a
# semidirect group Z_m x|_r Z_k2 with voltages on its darts. The C engine
# anneals only the voltages; the base is fixed and given on stdin. Bases are
# either
#   (a) the point-line incidence graph of PG(2, q), q + 1 <= d, completed to
#       degree d by random perfect matchings avoiding existing edges (found by
#       Kuhn's augmenting paths), or
#   (b) a random simple d-regular bipartite graph on K per side.
# Left multiplication by the group is an automorphism of every lift and acts
# transitively on each fibre, so BFS from the 2K fibre representatives decides
# the diameter exactly. A lift of a simple base is simple, so no duplicate
# penalty is needed.
#
# C usage: prog d D K m k2 r seed slice_seconds, base on stdin in
# "n m" + edge format with n = 2K (side A = 0..K-1, side B = K..2K-1).
# Prints a zero-cost lift ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGCOST (1 << 30)
#define RL 20000
#define STAG 5000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR, *dI, *dJ, *dS, *bestS, *perm, *adj, *cnt, *fr, *nx;
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
                int du = cnt[u];
                for (int t = 0; t < du; t++) {
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
    return total;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 1;
    }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (d < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    int nb, mb;
    if (scanf("%d %d", &nb, &mb) != 2 || nb != 2 * K || mb < 1) {
        printf("0 0\n");
        return 0;
    }
    NE = mb;
    G = MM * K2;
    N = 2 * K * G;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    int *degb = calloc((size_t)nb, sizeof(int));
    if (!dI || !dJ || !dS || !bestS || !degb) { printf("0 0\n"); return 0; }
    for (int e = 0; e < NE; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u >= K) { int t = u; u = v; v = t; }
        if (u < 0 || u >= K || v < K || v >= 2 * K) { printf("0 0\n"); return 0; }
        dI[e] = u;
        dJ[e] = v - K;
        degb[u]++;
        degb[v]++;
    }
    DEG = 0;
    for (int i = 0; i < nb; i++) if (degb[i] > DEG) DEG = degb[i];
    free(degb);
    if (DEG < 1 || DEG > d) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(uint32_t));
    if (!perm || !adj || !cnt || !fr || !nx || !vis) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.4) {
            for (int e = 0; e < NE; e++) dS[e] = rndint(G);
            T0 = 1.5;
        } else {
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 6 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            T0 = 0.7;
        }
        for (int e = 0; e < NE; e++) set_perm(e);
        int cur = cost_fn();
        if (cur < bestCost) {
            bestCost = cur;
            memcpy(bestS, dS, sizeof(int) * (size_t)NE);
        }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.03;
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
            if (cur < bestCost) {
                bestCost = cur;
                memcpy(bestS, dS, sizeof(int) * (size_t)NE);
            }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        memcpy(dS, bestS, sizeof(int) * (size_t)NE);
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
# Exact constructions (kept from the parent as safe starting points).
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
# New helpers: random perfect matchings avoiding a forbidden set, degree-
# completed projective-plane bases, and group enumeration.
# ----------------------------------------------------------------------------

def _prime_power_below(d):
    """Largest prime power q with q + 1 <= d (q >= 2), or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _kuhn_matching(K, forbid, rng):
    """Random perfect matching on K x K avoiding pairs (i, j) in forbid.

    Returns perm with A-vertex i matched to B-vertex perm[i], or None.
    """
    match_b = [-1] * K

    def augment(i, seen):
        cols = list(range(K))
        rng.shuffle(cols)
        for j in cols:
            if seen[j] or (i, j) in forbid:
                continue
            seen[j] = True
            if match_b[j] == -1 or augment(match_b[j], seen):
                match_b[j] = i
                return True
        return False

    order = list(range(K))
    rng.shuffle(order)
    for i in order:
        if not augment(i, [False] * K):
            return None
    perm = [0] * K
    for j in range(K):
        perm[match_b[j]] = j
    return perm


def _pg_base(d, rng):
    """PG(2,q) incidence with q + 1 <= d, completed to d-regular by random matchings.

    Returns (K, pairs) with pairs a set of (i, j), i and j in 0..K-1, or None.
    """
    q = _prime_power_below(d)
    if q is None:
        return None
    n, inc = lib.projective_plane_incidence(q)
    K = n // 2
    pairs = {(u, v - K) for u, v in inc}
    for _ in range(d - (q + 1)):
        p = _kuhn_matching(K, pairs, rng)
        if p is None:
            return None
        pairs.update((i, p[i]) for i in range(K))
    return K, pairs


def _regular_base(K, d, rng):
    """Random simple d-regular bipartite base on K per side (needs K >= d), or None."""
    pairs = set()
    for _ in range(d):
        p = _kuhn_matching(K, pairs, rng)
        if p is None:
            return None
        pairs.update((i, p[i]) for i in range(K))
    return pairs


def _group_options(G):
    """All (m, k2, r) with Z_m x|_r Z_k2 of order G = m * k2 (r = 1 is the direct product)."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        rs_ = [1]
        if k2 > 1 and m > 2:
            rs_ += [c for c in range(2, m)
                    if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        opts += [(m, k2, r) for r in rs_]
    return opts


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.92 * budget
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    pg_ok = _prime_power_below(d) is not None

    # Main search: anneal voltages of lifts of a fixed base over semidirect groups.
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)

        if pg_ok and rng.random() < 0.4:
            base = _pg_base(d, rng)
        else:
            K0 = rng.randint(d, 4 * d)
            pairs0 = _regular_base(K0, d, rng)
            base = None if pairs0 is None else (K0, pairs0)
        if base is None:
            continue
        K0, pairs = base

        n_min = best[0] + 1
        G_min = -(-n_min // (2 * K0))
        opts = _group_options(G_min + rng.randrange(0, 3))
        if not opts:
            continue
        m, k2, r = rng.choice(opts)

        stdin_edges = [(i, K0 + j) for i, j in sorted(pairs)]
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K0, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(2 * K0, stdin_edges),
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
