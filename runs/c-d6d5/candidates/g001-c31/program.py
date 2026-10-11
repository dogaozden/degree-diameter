import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/*
 * Annealing search for bipartite voltage lifts over semidirect products
 * Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b + e)).
 *
 * Base: k A-vertices and k B-vertices. Layer l has a perfect matching
 * A_i -> B_{pj[l*k+i]}, and dart e = l*k+i carries voltage sv[e] in G.
 * Edges: A(i,g) -- B(j, g*s) for all g. Each A and each B vertex has degree d.
 * Left multiplication is an automorphism, so only the 2k vertices g=0 need BFS.
 *
 * Cost = (unreached (rep, vertex) pairs within distance D) + 3 * (duplicate pairs).
 * Moves: change one voltage, or swap two targets inside one layer.
 * Temperature cycles with reheating from the best state seen.
 * Prints the graph on success, or "0 0" when time runs out.
 */

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d, D, k, m, k2, G, N, ND;
static long long pw[64];
static int *mulT, *pj, *sv, *perm, *adj, *deg, *stamp, *queue_;
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long a2 = ((long long)a + pw[b] * (long long)c) % m;
    int b2 = (b + e) % k2;
    return (int)a2 * k2 + b2;
}

static void build_row(int e) {
    int s = sv[e];
    int *row = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) row[g] = mulT[g * G + s];
}

static long long evaluate(void) {
    memset(deg, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int e = l * k + i;
            int j = pj[e];
            int *row = perm + (size_t)e * G;
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (k + j) * G + row[g];
                adj[(size_t)a * d + deg[a]++] = b;
                adj[(size_t)b * d + deg[b]++] = a;
            }
        }
    }
    long long pen = 0;
    for (int v = 0; v < N; v++) {
        int *nb = adj + (size_t)v * d;
        for (int x = 0; x < d; x++)
            for (int y = x + 1; y < d; y++)
                if (nb[x] == nb[y]) pen++;
    }
    long long unreached = 0;
    for (int r = 0; r < 2 * k; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int head = 0, tail = 0;
        queue_[tail++] = src;
        stamp[src] = curstamp;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = queue_[head++];
                int *nb = adj + (size_t)u * d;
                for (int t = 0; t < d; t++) {
                    int v = nb[t];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        queue_[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached + 3 * pen;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: d D seed time k m k2 r\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d < 1 || D < 1 || k < 1 || m < 2 || k2 < 1 || k2 > 63) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 5; w++) rnd64();

    G = m * k2;
    N = 2 * k * G;
    ND = d * k;

    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        pw[b] = p;
        p = (p * (long long)r) % m;
    }

    mulT = malloc(sizeof(int) * (size_t)G * G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[x * G + y] = gmul(x, y);

    pj = malloc(sizeof(int) * ND);
    sv = malloc(sizeof(int) * ND);
    perm = malloc(sizeof(int) * (size_t)ND * G);
    adj = malloc(sizeof(int) * (size_t)N * d);
    deg = malloc(sizeof(int) * N);
    stamp = calloc(N, sizeof(int));
    queue_ = malloc(sizeof(int) * N);
    int *bpj = malloc(sizeof(int) * ND);
    int *bsv = malloc(sizeof(int) * ND);

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) pj[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pj[l * k + i];
            pj[l * k + i] = pj[l * k + j];
            pj[l * k + j] = t;
        }
    }
    for (int e = 0; e < ND; e++) {
        sv[e] = rndint(G);
        build_row(e);
    }

    clock_t t0 = clock();
    long long cur = evaluate();
    long long best = cur;
    memcpy(bpj, pj, sizeof(int) * ND);
    memcpy(bsv, sv, sizeof(int) * ND);

    const long long CYC = 200000;
    long long it = 0;
    while (best > 0) {
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        if (it % CYC == 0) {
            memcpy(pj, bpj, sizeof(int) * ND);
            memcpy(sv, bsv, sizeof(int) * ND);
            for (int e = 0; e < ND; e++) build_row(e);
            cur = best;
        }
        double ph = (double)(it % CYC) / (double)CYC;
        double T = 0.25 + 12.0 * (1.0 - ph) * (1.0 - ph);

        if (k >= 2 && rndint(4) == 0) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int e1 = l * k + i1, e2 = l * k + i2;
            int t = pj[e1]; pj[e1] = pj[e2]; pj[e2] = t;
            long long c2 = evaluate();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                t = pj[e1]; pj[e1] = pj[e2]; pj[e2] = t;
            }
        } else {
            int e = rndint(ND);
            int old = sv[e];
            sv[e] = rndint(G);
            build_row(e);
            long long c2 = evaluate();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                sv[e] = old;
                build_row(e);
            }
        }
        if (cur < best) {
            best = cur;
            memcpy(bpj, pj, sizeof(int) * ND);
            memcpy(bsv, sv, sizeof(int) * ND);
        }
    }

    if (best == 0) {
        memcpy(pj, bpj, sizeof(int) * ND);
        memcpy(sv, bsv, sizeof(int) * ND);
        for (int e = 0; e < ND; e++) build_row(e);
        printf("%d %d\n", N, ND * G);
        for (int e = 0; e < ND; e++) {
            int i = e % k;
            int j = pj[e];
            int *row = perm + (size_t)e * G;
            for (int g = 0; g < G; g++)
                printf("%d %d\n", i * G + g, (k + j) * G + row[g]);
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: constructions, group choice, C runs, bookkeeping.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pick_config(G, rng):
    """Random (k2, m, r) with G = m*k2 and r^k2 = 1 mod m, preferring non-cyclic groups."""
    opts = []
    for k2 in (2, 3, 4, 5, 6, 8, 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((1, m, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        opts.extend((k2, m, r) for r in rs)
    if not opts:
        return None
    nontriv = [o for o in opts if o[0] > 1]
    pool = nontriv if nontriv and rng.random() < 0.8 else opts
    return rng.choice(pool)


def _run_search(d, D, k, m, k2, r, seed, budget):
    """Run the C annealer for one group. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", k, m, k2, r],
                        timeout=budget + 5.0)
        n, edges = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n <= 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = (n, [(i, (i + 1) % n) for i in range(n)])
        if lib.is_valid(cyc[0], cyc[1], d, D):
            return cyc

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(res):
        nonlocal best
        if res is None:
            return
        n, e = res
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if D >= 3:
        consider(_best_pg(d))

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Bisection over the group order G for each base size k.
    # lo[k]: largest G found valid. hi[k]: smallest G judged infeasible.
    ks = (1, 2, 3)
    lo = {k: 0 for k in ks}
    hi = {k: None for k in ks}
    fails = {k: 0 for k in ks}
    budget_cap = max(4.0, 0.2 * time_limit)

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        active = [k for k in ks if hi[k] is None or hi[k] - lo[k] > 1]
        if not active:
            break
        k = rng.choice(active)

        if hi[k] is None:
            if lo[k] == 0:
                G = max(2, best[0] // (2 * k) + 1)
            else:
                G = lo[k] + max(1, lo[k] // 30)
        else:
            G = (lo[k] + hi[k]) // 2
            if G < 2 or G >= hi[k]:
                hi[k] = lo[k] + 1
                continue

        cfg = _pick_config(G, rng)
        if cfg is None:
            hi[k] = G
            continue
        k2, m, r = cfg

        budget = min(remaining - 1.5, budget_cap)
        if budget < 1.0:
            break
        res = _run_search(d, D, k, m, k2, r, rng.randrange(1 << 30), budget)
        if res is not None:
            consider(res)
            lo[k] = max(lo[k], G)
            fails[k] = 0
        else:
            fails[k] += 1
            if fails[k] >= 2:
                hi[k] = G
                fails[k] = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
