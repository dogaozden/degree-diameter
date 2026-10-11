import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: orbit-reduced group voltage lifts with simulated annealing.
#
# Vertices A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, group G = Z_m x| Z_k2.
# Layered structure: for each of d layers, a permutation pi_l of the k base
# indices; dart (i, pi_l(i), s) joins A_{i,g} to B_{pi_l(i), g*s} for all g.
# Every vertex then has degree exactly d, and the graph is bipartite and simple
# once the (i, j, s) darts are distinct.
#
# Left multiplication is a transitive automorphism on each side, so diameter
# <= D iff a depth-D BFS from each of the 2k base representatives reaches all.
#
# NEW IDEA (base growth with warm start): once a valid lift with k base indices
# and group G is known, try k+1 with the SAME group. Each layer's permutation is
# extended by sending the new A index to the new B index (or swapping it with one
# existing index), so every old dart stays in place except one per layer. The
# new vertex count is 2G larger, and annealing only has to repair the new darts.
# This is tried in two out of three rounds while growth keeps succeeding; the
# other rounds are the parent's random restarts at larger group orders.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1024
#define MAXN 2048
#define MAXD 32
#define MAXK 16
#define MAXT (MAXD * MAXK)
#define MAXE (MAXG * MAXD)
#define BIGC 1000000000L

static int GM[MAXG * MAXG];
static int GO = 0;
static int CM = 1, CK2 = 1, CR = 1;
static int DI[MAXT], DJ[MAXT], DS[MAXT];
static int ADJ[MAXN * MAXD];
static int CNT[MAXN];
static int VIS[MAXN];
static int QU[MAXN];
static int STAMP = 0;
static int MARK[MAXK * MAXK * MAXG];
static int MSTAMP = 0;
static int BE[2 * MAXE + 16];
static int BEcount = 0;
static int best_n = 0;
static int HAVE = 0;
static int BK = 0, BG = 0, BM = 1, BK2 = 1, BR = 1;
static int BDI[MAXT], BDJ[MAXT], BDS[MAXT];
static double DEADLINE = 0.0;
static const int KCH[6] = {1, 1, 2, 2, 3, 4};

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return n <= 0 ? 0 : (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Semidirect product Z_m x| Z_k2 with (a,b)(c,d) = (a + r^b c, b + d); element a*k2+b. */
static void build_group(int m, int k2, int r) {
    int G = m * k2;
    int pw[16];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e2 = y % k2;
            int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
            GM[x * G + y] = aa * k2 + (b + e2) % k2;
        }
    }
    GO = G;
}

static int choose_group(int G) {
    int cand[12], nc = 0;
    for (int k2 = 1; k2 <= 12; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    if (nc == 0) return 0;
    int k2 = cand[rndint(nc)];
    int m = G / k2;
    int r = 1;
    if (k2 > 1) {
        for (int t = 0; t < 200; t++) {
            int c = 1 + rndint(m - 1);
            if (gcd_i(c, m) == 1 && powmod_i(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    build_group(m, k2, r);
    CM = m; CK2 = k2; CR = r;
    return 1;
}

static void random_darts(int k, int d) {
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(GO);
        }
    }
}

/* Base growth: kold -> kold+1 keeping every layer a permutation. The new A index
   maps to the new B index, or swaps targets with one old index at random. */
static void extend_darts(int kold, int d, const int *sJ, const int *sS) {
    int k1 = kold + 1;
    int p[MAXK + 1];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kold; i++) p[i] = sJ[l * kold + i];
        p[kold] = kold;
        int x = rndint(kold + 1);
        if (x < kold) { p[kold] = p[x]; p[x] = kold; }
        for (int i = 0; i < k1; i++) {
            int t = l * k1 + i;
            DI[t] = i;
            DJ[t] = p[i];
            DS[t] = (i < kold) ? sS[l * kold + i] : rndint(GO);
        }
    }
}

static long eval_cost(int k, int d, int D) {
    int G = GO, N = 2 * k * G, T = k * d;
    if (N > MAXN || k > MAXK) return BIGC;
    MSTAMP++;
    if (MSTAMP == 0x7fffffff) { memset(MARK, 0, sizeof(MARK)); MSTAMP = 1; }
    for (int t = 0; t < T; t++) {
        int idx = (DI[t] * MAXK + DJ[t]) * MAXG + DS[t];
        if (MARK[idx] == MSTAMP) return BIGC;
        MARK[idx] = MSTAMP;
    }
    for (int v = 0; v < N; v++) CNT[v] = 0;
    for (int t = 0; t < T; t++) {
        int i = DI[t], j = DJ[t], s = DS[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + GM[g * G + s];
            if (CNT[a] >= d || CNT[b] >= d) return BIGC;
            ADJ[a * MAXD + CNT[a]++] = b;
            ADJ[b * MAXD + CNT[b]++] = a;
        }
    }
    for (int v = 0; v < N; v++) if (CNT[v] != d) return BIGC;

    long total = 0;
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        STAMP++;
        if (STAMP == 0x7fffffff) { memset(VIS, 0, sizeof(VIS)); STAMP = 1; }
        int head = 0, tail = 0;
        QU[tail++] = src;
        VIS[src] = STAMP;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                int u = QU[head];
                for (int c = 0; c < d; c++) {
                    int v = ADJ[u * MAXD + c];
                    if (VIS[v] != STAMP) { VIS[v] = STAMP; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long anneal(int k, int d, int D, long iters) {
    int G = GO, T = k * d;
    long cur = eval_cost(k, d, D);
    double temp0 = 0.5 * G + 1.0;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 1023) == 0 && now_s() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = temp0 * (1.0 - frac) + 0.3;
        if (rndint(2) == 0) {
            int t = rndint(T);
            int old = DS[t];
            int ns = rndint(G);
            if (ns == old) continue;
            DS[t] = ns;
            long c2 = eval_cost(k, d, D);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else DS[t] = old;
        } else {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int t1 = l * k + i1, t2 = l * k + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = eval_cost(k, d, D);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    return cur;
}

static void store_best(int k, int d) {
    int G = GO, T = k * d;
    BEcount = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            BE[2 * BEcount] = DI[t] * G + g;
            BE[2 * BEcount + 1] = (k + DJ[t]) * G + GM[g * G + DS[t]];
            BEcount++;
        }
    best_n = 2 * k * G;
    HAVE = 1;
    BK = k; BG = G; BM = CM; BK2 = CK2; BR = CR;
    memcpy(BDI, DI, sizeof(int) * T);
    memcpy(BDJ, DJ, sizeof(int) * T);
    memcpy(BDS, DS, sizeof(int) * T);
}

/* Warm-started growth from the best state: k -> k+1, same group. Returns 1 on success. */
static int grow_attempt(int d, int D, long iters) {
    int k1 = BK + 1;
    if (k1 > MAXK || 2 * k1 * BG > MAXN) return 0;
    build_group(BM, BK2, BR);
    CM = BM; CK2 = BK2; CR = BR;
    extend_darts(BK, d, BDJ, BDS);
    long c = anneal(k1, d, D, iters);
    if (c == 0 && 2 * k1 * GO > best_n) { store_best(k1, d); return 1; }
    return c == 0 ? 1 : 0;
}

/* Parent-style random restart at a group order above the current best. */
static int restart_attempt(int d, int D, int step) {
    int k = KCH[rndint(6)];
    int nmin = best_n + step;
    int gmin = (nmin + 2 * k - 1) / (2 * k);
    if (gmin < 2) gmin = 2;
    int G = gmin + rndint(1 + gmin / 12);
    int gcap = MAXN / (2 * k);
    if (gcap > MAXG) gcap = MAXG;
    if (G > gcap) G = gcap;
    if (G < 2) return -1;
    if (!choose_group(G)) return -1;
    random_darts(k, d);
    long c = anneal(k, d, D, 20000);
    if (c == 0 && 2 * k * GO > best_n) store_best(k, d);
    return c == 0 ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();
    DEADLINE = now_s() + tl;
    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    int step = 16, rfails = 0, gfails = 0;
    while (now_s() < DEADLINE) {
        int grow_ok = HAVE && gfails < 40 && BK + 1 <= MAXK && 2 * (BK + 1) * BG <= MAXN;
        if (grow_ok && rndint(3) != 0) {
            if (grow_attempt(d, D, 30000)) gfails = 0;
            else gfails++;
            continue;
        }
        int prev = best_n;
        int r = restart_attempt(d, D, step);
        if (best_n > prev) gfails = 0;
        if (r == 1) {
            rfails = 0;
            step = step * 2;
            int cap = 16 + best_n / 8;
            if (step > cap) step = cap;
        } else if (++rfails >= 4) {
            rfails = 0;
            step = step / 2;
            if (step < 2) step = 2;
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, BEcount);
    for (int e = 0; e < BEcount; e++) printf("%d %d\n", BE[2 * e], BE[2 * e + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and fallback search.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Python hill-climb over voltages (fallback only, used if the C engine fails)."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < 0.02:
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, time_limit - 4.0)
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

    # Main search: the C engine climbs from small graphs itself (random restarts
    # interleaved with warm-started base growth), so no start graph is passed.
    c_ok = False
    remaining = end - time.monotonic()
    if d >= 2 and D >= 2 and remaining > 5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, 0.9 * remaining - 1.0],
                            stdin_graph=None, timeout=remaining)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                c_ok = True
                consider(n, e)
        except Exception:
            c_ok = False

    # Python fallback, used only if the C engine produced nothing.
    if not c_ok:
        while time.monotonic() < end:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
            res = _search(d, D, k, G, rng, 600, end)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
