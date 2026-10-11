"""Tabu search over bi-Cayley lifts with arbitrary (table-given) groups.

Changes from the previous annealing engine:
  * The group is supplied as a full multiplication table, so the lift can use
    any finite group built from semidirect and direct products of cyclic groups.
  * The search is a tabu search. Each step samples SAMPLE random moves (voltage
    change or swap of two dart targets in one layer), applies the best non-tabu
    move even when it is worse, and tabu-marks the darts it touched. A restart
    kicks the best state found so far when no improvement is seen for RESTART steps.
  * Left multiplication by any group element is an automorphism of the lift, so
    the BFS from the 2K block representatives decides the diameter exactly.

Safe fallbacks (K_{d,d}, PG(2,q), W(q), validated with lib.is_valid) are kept, so
every case returns a valid graph.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define PEN 1000
#define BIGC (1 << 29)
#define SAMPLE 24
#define TEN0 5
#define RESTART 3000

static int DEG, DIAM, K, G, N, NE, LMAX, UNREACH_W;
static int *MT, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx, *bestJ, *bestS, *tabuU, *pbuf;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

typedef struct { int type, a, b, val, old; } Move;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

/* perm[e][g] = g * s_e (right multiplication), so the edge set is
   A_{i,g} ~ B_{j, g*s} for all g. */
static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = MT[g * G + s];
}

/* Excess-distance cost: zero iff the lift is valid, plus a duplicate penalty. */
static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (e1 % K == e2 % K && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = (e % K) * G, bb = (K + dJ[e]) * G;
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

static void random_start(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) pbuf[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pbuf[i]; pbuf[i] = pbuf[j]; pbuf[j] = t;
        }
        for (int i = 0; i < K; i++) dJ[l * K + i] = pbuf[i];
    }
    for (int e = 0; e < NE; e++) dS[e] = rndint(G);
    for (int e = 0; e < NE; e++) set_perm(e);
}

static void kick_best(int k) {
    memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
    memcpy(dS, bestS, sizeof(int) * (size_t)NE);
    for (int q = 0; q < k; q++) dS[rndint(NE)] = rndint(G);
    for (int e = 0; e < NE; e++) set_perm(e);
}

static void apply_mv(Move *mv) {
    if (mv->type == 0) {
        mv->old = dS[mv->a];
        dS[mv->a] = mv->val;
        set_perm(mv->a);
    } else {
        int t = dJ[mv->a]; dJ[mv->a] = dJ[mv->b]; dJ[mv->b] = t;
    }
}

static void revert_mv(Move *mv) {
    if (mv->type == 0) {
        dS[mv->a] = mv->old;
        set_perm(mv->a);
    } else {
        int t = dJ[mv->a]; dJ[mv->a] = dJ[mv->b]; dJ[mv->b] = t;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    if (DEG < 1 || DIAM < 1 || K < 1) { printf("0 0\n"); return 0; }

    /* Input: "n m" then m lines "x y" giving MT[x] = y, with n = m = G*G. */
    long long nn = 0, mm = 0;
    if (scanf("%lld %lld", &nn, &mm) != 2 || nn < 1 || mm != nn) { printf("0 0\n"); return 0; }
    int g = 1;
    while ((long long)g * g < nn) g++;
    if ((long long)g * g != nn) { printf("0 0\n"); return 0; }
    G = g;
    MT = malloc(sizeof(int) * (size_t)nn);
    if (!MT) { printf("0 0\n"); return 0; }
    for (long long q = 0; q < mm; q++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        MT[u] = v;
    }

    N = 2 * K * G;
    NE = DEG * K;
    LMAX = DIAM + 3;
    UNREACH_W = LMAX - DIAM + 2;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    tabuU = calloc(NE, sizeof(int));
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    pbuf = malloc(sizeof(int) * K);
    if (!dJ || !dS || !bestJ || !bestS || !tabuU || !perm || !adj || !cnt || !fr || !nx || !vis || !pbuf) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    random_start();
    int cur = cost_fn();
    int bestCost = cur;
    save_best();
    if (cur == 0) found = 1;

    int since = 0;
    long long it = 0;
    while (!found) {
        it++;
        if ((it & 63) == 0 && elapsed(t0) >= slice) break;

        Move bm;
        int bc = BIGC, have = 0;
        for (int s = 0; s < SAMPLE; s++) {
            Move mv;
            if (K > 1 && rnd01() < 0.35) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                mv.type = 1; mv.a = l * K + i1; mv.b = l * K + i2; mv.val = 0; mv.old = 0;
            } else {
                mv.type = 0; mv.a = rndint(NE); mv.b = 0; mv.val = rndint(G); mv.old = 0;
                if (mv.val == dS[mv.a]) continue;
            }
            int isTabu = (tabuU[mv.a] > it) || (mv.type == 1 && tabuU[mv.b] > it);
            apply_mv(&mv);
            int c = cost_fn();
            revert_mv(&mv);
            if (isTabu && c >= bestCost) continue;
            if (!have || c < bc || (c == bc && (rnd64() & 1))) {
                bc = c; bm = mv; have = 1;
            }
        }
        if (!have) continue;

        apply_mv(&bm);
        cur = bc;
        int ten = TEN0 + rndint(TEN0 + 1);
        tabuU[bm.a] = (int)it + ten;
        if (bm.type == 1) tabuU[bm.b] = (int)it + ten;

        if (cur < bestCost) { bestCost = cur; save_best(); since = 0; }
        else since++;
        if (cur == 0) { found = 1; break; }

        if (since > RESTART) {
            kick_best(NE / 6 + 1);
            cur = cost_fn();
            since = 0;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            int ba = (e % K) * G, bb = (K + dJ[e]) * G;
            const int *pm = perm + (size_t)e * G;
            for (int q = 0; q < G; q++) printf("%d %d\n", ba + q, bb + pm[q]);
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (safe fallbacks).
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
# Group sampling. A group is a list of cyclic-by-cyclic factors (m, k2, r),
# and the search group is their direct product. The product is passed to C
# as a multiplication table.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 48, 49, 54, 56, 63, 72, 81]
MAX_ORDER = 700


def _sample_cyclic(target, rng):
    """Return (m, k2, r) with Z_m x|_r Z_k2 of order >= target, or None."""
    for _ in range(100):
        k2 = rng.choice(K2_CHOICES)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return (m, 1, 1)
        nontrivial = [c for c in range(2, m)
                      if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if nontrivial and rng.random() < 0.7:
            return (m, k2, rng.choice(nontrivial))
        return (m, k2, 1)
    return None


def _sample_group(target, rng):
    """Return a list of factors whose direct product has order >= target, or None."""
    if rng.random() < 0.25:
        c = rng.choice([2, 3, 4, 5, 6])
        base = _sample_cyclic(-(-target // c), rng)
        if base is not None:
            return [base, (c, 1, 1)]
    base = _sample_cyclic(target, rng)
    return [base] if base is not None else None


def _prod(o1, mu1, o2, mu2):
    """Direct product of two groups given as (order, mul); element x = a*o2 + b."""
    def mul(x, y):
        a1, b1 = divmod(x, o2)
        a2, b2 = divmod(y, o2)
        return mu1(a1, a2) * o2 + mu2(b1, b2)
    return o1 * o2, mul


def _group(factors):
    """Return (order, mul) for the direct product of the factors. Identity is 0."""
    order, mul, _ = lib.semidirect_group(*factors[0])
    for f in factors[1:]:
        o2, mu2, _ = lib.semidirect_group(*f)
        order, mul = _prod(order, mul, o2, mu2)
    return order, mul


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    search_deadline = t_start + 0.9 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_2 is valid for any d >= 1, D >= 1.
    best = (2, [(0, 1)])
    hb = lib.haar_graph(d, range(d))
    if hb[0] > best[0] and lib.is_valid(hb[0], hb[1], d, D):
        best = hb

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D < 3 or d < 2:
        return best

    step = 0.08
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining - 1.0, 12.0)
        K = rng.choice([1, 2, 2, 3])
        want = best[0] * (1.0 + step)
        target = max(2, math.ceil(want / (2 * K)))
        factors = _sample_group(target, rng)
        if factors is None:
            step = max(0.005, step * 0.7)
            continue
        try:
            order, mul = _group(factors)
        except ValueError:
            step = max(0.005, step * 0.7)
            continue
        if order > MAX_ORDER:
            step = max(0.005, step * 0.7)
            continue

        # Group table in the stdin "graph" format: n = m = order^2, pairs (x*order+y, x*y).
        table = [(x * order + y, mul(x, y)) for x in range(order) for y in range(order)]
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(order * order, table),
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            n, e = 0, []

        if consider(n, e):
            step = min(0.4, step * 1.25)
        else:
            step = max(0.005, step * 0.7)

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    return best
