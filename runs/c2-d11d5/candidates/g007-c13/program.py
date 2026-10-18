"""Bi-Cayley lift search: a C simulated annealer over semidirect groups Z_m x| Z_k2 with
base size k, plus exact constructions as fallbacks. Every returned graph is checked with
lib.is_valid, and K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage:  prog d D seed time_limit < input
 * stdin:  "thr np" then np pairs of ints; configurations are read two pairs at a time:
 *         (k, m), (k2, r) meaning base size k, group Z_m x| Z_k2 with r^k2 = 1 mod m.
 *         thr is the order the result must beat.
 * stdout: "n m" + edges of the best lift found, or "0 0".
 *
 * Vertices: A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h. Layer l matches A_i to
 * B_{perm[l][i]} with voltage volt[l][i]: A_{i,g} ~ B_{j, g*s}. Each layer is a perfect
 * matching of blocks, so every vertex has degree exactly d. Cost = unreached (vertex, block)
 * pairs at distance > D, plus a penalty for duplicate darts.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 12
#define MAXG 4096
#define MAXN 98304
#define MAXE 786432
#define SLICE 2.0
#define PATIENCE 1500
#define PEN 200

static int d, D;
static int K, GM, GK2, G, N;
static uint32_t FULL;
static int pw[MAXG];
static int invg[MAXG];
static int perm[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t wa[MAXN], wb[MAXN], cand[MAXN], ra[MAXN];
static int bestU[MAXE], bestV[MAXE];
static int bestE = 0, bestNv = 0, bestN = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Semidirect product: element a*GK2 + b, (a,b)*(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2;
    int c = y / GK2, e = y % GK2;
    int na = (int)(((long)a + (long)pw[b] * c) % GM);
    int nb = (b + e) % GK2;
    return na * GK2 + nb;
}

static int ginv(int x) {
    int a = x / GK2, b = x % GK2;
    int nb = (GK2 - b) % GK2;
    long t = ((long)pw[nb] * a) % GM;
    int na = (int)((GM - t) % GM);
    return na * GK2 + nb;
}

static int setup_group(int k, int m, int k2, int r) {
    K = k;
    GM = m;
    GK2 = k2;
    G = m * k2;
    N = 2 * K * G;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    if ((long)pw[k2 - 1] * r % m != 1 % m) return 0;
    if (gcd_i(r, m) != 1) return 0;
    for (int x = 0; x < G; x++) invg[x] = ginv(x);
    FULL = (1u << (2 * K)) - 1u;
    return 1;
}

static void build_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = perm[l][i], s = volt[l][i], si = invg[s];
        int A0 = i * G, B0 = (K + j) * G;
        for (int g = 0; g < G; g++) {
            nbr[l][A0 + g] = B0 + gmul(g, s);
            nbr[l][B0 + g] = A0 + gmul(g, si);
        }
    }
}

static void randomize_all(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) volt[l][i] = rndint(G);
        build_layer(l);
    }
}

/* Cost of the current configuration; the reach bitsets go to cand[]. */
static long eval_cost(void) {
    uint32_t *cur = wa, *nxt = wb;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * G] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = cur[v];
            for (int l = 0; l < d; l++) r |= cur[nbr[l][v]];
            nxt[v] = r;
            if (r != cur[v]) changed = 1;
        }
        uint32_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    memcpy(cand, cur, sizeof(uint32_t) * (size_t)N);
    long cost = 0;
    for (int v = 0; v < N; v++) cost += __builtin_popcount(FULL & ~cur[v]);
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && volt[l1][i] == volt[l2][i]) dup++;
    return cost + PEN * dup;
}

static void store_solution(void) {
    int E = 0;
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) {
            bestU[E] = v;
            bestV[E] = nbr[l][v];
            E++;
        }
    bestE = E;
    bestNv = N;
    bestN = N;
}

static int run_config(double until) {
    randomize_all();
    long cost = eval_cost();
    memcpy(ra, cand, sizeof(uint32_t) * (size_t)N);
    long c0 = cost > 1 ? cost : 1;
    long best = cost;
    long last = 0;
    for (long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 31) == 0 && now() > until) return 0;
        if (it - last > PATIENCE) {
            randomize_all();
            cost = eval_cost();
            memcpy(ra, cand, sizeof(uint32_t) * (size_t)N);
            c0 = cost > 1 ? cost : 1;
            best = cost;
            last = it;
            continue;
        }
        double T = 0.3 + 0.05 * (double)c0 * pow(0.997, (double)(it - last));
        int l = rndint(d);
        if (K >= 2 && rnd01() < 0.2) {
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = t;
            build_layer(l);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                memcpy(ra, cand, sizeof(uint32_t) * (size_t)N);
            } else {
                t = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = t;
                build_layer(l);
            }
        } else {
            int i = -1;
            if (rnd01() < 0.4) {
                int v = rndint(N);
                int tries = 0;
                while (tries++ < 30 && ra[v] == FULL) v = rndint(N);
                if (ra[v] != FULL) {
                    int blk = v / G;
                    if (blk < K) {
                        i = blk;
                    } else {
                        int j = blk - K;
                        for (int ii = 0; ii < K; ii++)
                            if (perm[l][ii] == j) {
                                i = ii;
                                break;
                            }
                    }
                }
            }
            if (i < 0) i = rndint(K);
            int old = volt[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            volt[l][i] = nv;
            build_layer(l);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                memcpy(ra, cand, sizeof(uint32_t) * (size_t)N);
            } else {
                volt[l][i] = old;
                build_layer(l);
            }
        }
        if (cost < best) {
            best = cost;
            last = it;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < input\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int thr = 0, m = 0;
    if (scanf("%d %d", &thr, &m) != 2) { thr = 0; m = 0; }
    bestN = thr;
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    int nconf = m / 2;
    for (int c = 0; c < nconf; c++) {
        int k, mg, k2, r;
        if (scanf("%d %d %d %d", &k, &mg, &k2, &r) != 4) break;
        if (now() > t_end) break;
        if (k < 1 || k > MAXK || mg < 2 || k2 < 1 || r < 1 || r >= mg) continue;
        long Gl = (long)mg * k2;
        if (Gl > MAXG) continue;
        long Nl = 2L * k * Gl;
        if (Nl > MAXN || Nl <= bestN) continue;
        if (!setup_group(k, mg, k2, r)) continue;
        double until = now() + SLICE;
        if (until > t_end) until = t_end;
        if (run_config(until)) store_solution();
    }
    if (bestE == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestNv, bestE);
    for (int e = 0; e < bestE; e++) printf("%d %d\n", bestU[e], bestV[e]);
    return 0;
}
'''


_MAX_G = 4096
_MAX_N = 98304
_K_OPTS = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12)
_K2_OPTS = (1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 20, 24)


# ----------------------------------------------------------------------------
# Exact constructions (used as stronger starting points for small cases).
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


# ----------------------------------------------------------------------------
# Group and base-size sampling for the C annealer.
# ----------------------------------------------------------------------------

def _group_params(G_t, k2, rng):
    """Return (m, k2, r) with m*k2 >= G_t, or None if no suitable r was found."""
    m = max(2, -(-G_t // k2))
    if k2 == 1:
        return m, 1, 1
    cands = [1, m - 1] + [rng.randrange(1, m) for _ in range(40)] if m > 2 else [1]
    for r in cands:
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return m, k2, r
    return None


def _make_configs(rng, lo, hi, moore, count):
    """Sample up to `count` distinct (k, m, k2, r) configurations with lo <= 2kG <= hi, sorted by order."""
    if hi < lo:
        return []
    seen = set()
    scored = []
    attempts = 0
    while len(scored) < count and attempts < count * 30:
        attempts += 1
        k = rng.choice(_K_OPTS)
        k2 = rng.choice(_K2_OPTS)
        T = rng.randint(lo, hi)
        G_t = max(2, -(-T // (2 * k)))
        g = _group_params(G_t, k2, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        N = 2 * k * G
        if G > _MAX_G or N > min(_MAX_N, moore) or N < lo:
            continue
        key = (k, m, k2, r)
        if key in seen:
            continue
        seen.add(key)
        scored.append((N, key))
    scored.sort()
    return [key for _, key in scored]


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Bold change: one C annealer over bi-Cayley lifts. Configurations are sorted by order
    # and the C side keeps only those that beat the current best, so the search ratchets
    # upward through the window [0.2, 0.32] of the Moore bound.
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = t0 + total
    moore = lib.moore_bound(d, D)
    lo = max(best_n + 1, int(0.2 * moore))
    hi = min(moore, max(lo + 1, int(0.32 * moore)))
    if hi >= lo and deadline - time.monotonic() > 3.0:
        rng = random.Random(seed)
        configs = _make_configs(rng, lo, hi, moore, 300)
        if configs:
            pairs = []
            for k, m, k2, r in configs:
                pairs.append((k, m))
                pairs.append((k2, r))
            budget = deadline - time.monotonic() - 1.0
            if budget > 2.0:
                try:
                    # The header n carries the threshold to beat; pairs carry the configurations.
                    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                     stdin_graph=(best_n, pairs), timeout=budget + 10.0)
                    consider(*lib.parse_graph_text(text))
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
