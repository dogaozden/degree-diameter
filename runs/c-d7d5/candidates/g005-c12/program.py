"""Targets d=7 D=5 with a different search engine.

Construction family: bi-Cayley lifts over Z_m x|_r Z_k2 with K vertices per side
and DEG darts per vertex (the same family as before, so the existing exact
constructions and the spare-degree extension are kept as fallbacks).

What changed: the C engine is no longer simulated annealing. It is a tabu search
with sampled best-improvement moves (voltage changes and within-layer target
swaps), aspiration on the global best, stagnation-triggered perturbations of the
best state, and a fresh random restart when a basin is exhausted. Group orders
are chosen so that the lift order exceeds the current best by at least 2
(aiming past the record 1134 for d=7, D=5). Every output is checked with
lib.is_valid, and a K_{d,d} fallback is always kept.
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
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define SAMPLE 48
#define STAG 2500

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[64];
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static int *tabuS, *tabuJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static long long iter = 1;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static inline int tenure(void) { return 5 + rndint(10); }

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

static void apply_volt(int e, int s) {
    dS[e] = s;
    set_perm(e);
}

static void apply_swap(int e1, int e2) {
    int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
}

/* Cost = (unreached pairs from the 2K representatives) + PEN * duplicate darts. */
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
    tabuS = calloc((size_t)NE * G, sizeof(int));
    tabuJ = calloc((size_t)NE * K, sizeof(int));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt ||
        !fr || !nx || !vis || !tabuS || !tabuJ || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;

    while (!found && elapsed(t0) < slice) {
        /* Epoch start: fresh random lift, or kick the best state found so far. */
        if (bestCost >= BIGCOST || rnd01() < 0.2) {
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
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = 2 + rndint(NE / 4 + 1);
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
        }

        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        long long lastImp = iter;
        while (!found) {
            if (elapsed(t0) >= slice) break;
            if (iter - lastImp > STAG) break;
            iter++;

            int bNc = BIGCOST, bType = -1, be1 = 0, be2 = 0, bs = 0;
            for (int smp = 0; smp < SAMPLE; smp++) {
                if (K > 1 && rnd01() < 0.3) {
                    int l = rndint(DEG);
                    int i1 = rndint(K);
                    int i2 = rndint(K - 1);
                    if (i2 >= i1) i2++;
                    int e1 = l * K + i1, e2 = l * K + i2;
                    int o1 = dJ[e1], o2 = dJ[e2];
                    if (o1 == o2) continue;
                    int tb = (tabuJ[e1 * K + o2] > iter) || (tabuJ[e2 * K + o1] > iter);
                    apply_swap(e1, e2);
                    int nc = cost_fn();
                    apply_swap(e1, e2);
                    if (tb && nc >= bestCost) continue;
                    if (nc < bNc || (nc == bNc && rnd01() < 0.5)) {
                        bNc = nc; bType = 1; be1 = e1; be2 = e2;
                    }
                } else {
                    int e = rndint(NE);
                    int old = dS[e];
                    int ns = rndint(G);
                    if (ns == old) continue;
                    int tb = tabuS[e * G + ns] > iter;
                    apply_volt(e, ns);
                    int nc = cost_fn();
                    apply_volt(e, old);
                    if (tb && nc >= bestCost) continue;
                    if (nc < bNc || (nc == bNc && rnd01() < 0.5)) {
                        bNc = nc; bType = 0; be1 = e; bs = ns;
                    }
                }
            }
            if (bType < 0) continue;

            if (bType == 1) {
                int e1 = be1, e2 = be2;
                int o1 = dJ[e1], o2 = dJ[e2];
                apply_swap(e1, e2);
                tabuJ[e1 * K + o1] = (int)(iter + tenure());
                tabuJ[e2 * K + o2] = (int)(iter + tenure());
            } else {
                int e = be1;
                int old = dS[e];
                apply_volt(e, bs);
                tabuS[e * G + old] = (int)(iter + tenure());
            }
            cur = bNc;
            if (cur < bestCost) {
                bestCost = cur;
                save_best();
                lastImp = iter;
            }
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
# Exact / safe constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Spare-degree extension (no-op for regular lifts, kept as a safe step).
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _extend_spare(n, edges, d, D, deadline):
    """Greedily add fresh vertex pairs while the graph stays valid. Returns (n, edges)."""
    if d < 2:
        return n, edges
    col = _two_colour(n, edges)
    if col is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A_sp = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B_sp = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A_sp or not B_sp:
            break
        grown = False
        for k in range(d - 1, 0, -1):
            if k > len(A_sp) or k > len(B_sp):
                continue
            a, b = n, n + 1
            cand_new = [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
            cand = edges + cand_new
            if lib.is_valid(n + 2, cand, d, D):
                edges = cand
                n += 2
                col += [0, 1]
                deg += [0, 0]
                deg[a] = k + 1
                deg[b] = k + 1
                for x in B_sp[:k]:
                    deg[x] += 1
                for y in A_sp[:k]:
                    deg[y] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Group sampling.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        r = 1  # r = 1 is the direct product, always valid
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m)
                     if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.9 * budget
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

    # Tabu search over bi-Cayley lifts. Each call aims strictly above the
    # current best order, so every success is a strict improvement.
    fails = 0
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining, rng.uniform(10.0, 16.0))
        k = rng.choice([1, 1, 1, 2, 2, 3, 4])
        need = best[0] + 2
        target = -(-need // (2 * k)) + rng.randrange(0, 3)
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 8.0,
            )
        except RuntimeError:
            fails += 1
            if fails >= 2:
                break
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with whatever time remains.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
