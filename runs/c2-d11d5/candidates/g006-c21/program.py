"""Bi-Cayley lift search in C over semidirect products Z_m x| Z_k2 (base size k <= 6).

A candidate (k, m, k2, r) defines a lift with 2*k*m*k2 vertices. The C engine tries the
candidates in ascending order of order. Each one is annealed over layer permutations and
voltages until every pair is within distance D, and the largest success is kept. Every
returned graph is checked with lib.is_valid. K_{d,d} or an exact construction is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift search.
 * Group Z_M x| Z_K2 (element (a,b) coded as a*K2+b, (a,b)*(c,e) = (a + r^b c, b + e)), G = M*K2.
 * Vertices: A_{i,g} = i*G+g (i < K), B_{p,h} = (K+p)*G+h.
 * Layer l pairs A_i with B_{lay[l][i]} through voltage svol[l][i]: A_{i,g} ~ B_{p, g*s}.
 * Every layer is a permutation, so the graph is d-regular and bipartite.
 * Left multiplication is an automorphism, so diameter <= D iff every vertex is within D of
 * every block representative (b*G). The cost counts unreached (vertex, representative) pairs.
 *
 * usage: prog d D seed budget slice (k m k2 r)*   (candidates, ascending order of order)
 * stdout: best valid graph as "n m" + edges, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 20000
#define MAXD 16
#define MAXK 16
#define MAXK2 64
#define PEN 1000L
#define PATIENCE 4000

static int d, D;
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

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M, K2, G, N;
static int pw[MAXK2];
static int nbr[MAXN * MAXD];
static int lay[MAXD][MAXK];
static int svol[MAXD][MAXK];
static uint32_t bufA[MAXN], bufB[MAXN], reach_new[MAXN], reach[MAXN];
static int bestnbr[MAXN * MAXD];
static int bK, bG, bN;
static int bestN = 0;

static inline int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int aa = (a + (int)(((long)pw[b] * c) % M)) % M;
    int bb = (b + e) % K2;
    return aa * K2 + bb;
}

static inline int ginv(int x) {
    int a = x / K2, b = x - a * K2;
    int nb = (K2 - b) % K2;
    int t = (int)(((long)pw[nb] * a) % M);
    int ai = (M - t) % M;
    return ai * K2 + nb;
}

static void setup_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    G = m * k2;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        pw[b] = (int)p;
        p = (p * r) % m;
    }
}

/* Layer l: A-block i joined to B-block p through voltage s. */
static void set_dart(int l, int i, int p, int s) {
    int ia = i * G, pb = (K + p) * G;
    int si = ginv(s);
    for (int g = 0; g < G; g++) {
        nbr[(ia + g) * d + l] = pb + gmul(g, s);
        nbr[(pb + g) * d + l] = ia + gmul(g, si);
    }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            svol[l][i] = rndint(G);
            set_dart(l, i, lay[l][i], svol[l][i]);
        }
    }
}

/* Number of repeated (i, p, s) keys across layers (would create parallel edges). */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && svol[l][i] == svol[l2][i]) c++;
    return c;
}

/* Cost = unreached (vertex, representative) pairs + PEN * duplicates. Reach goes to reach_new. */
static long evaluate(void) {
    int nb = 2 * K;
    uint32_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < nb; b++) cur[(size_t)b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            const int *nv = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nv[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) {
        reach_new[v] = cur[v];
        unreached += nb - __builtin_popcount(cur[v]);
    }
    return unreached + PEN * dupcount();
}

/* Simulated annealing with stagnation restarts. Returns 1 when a valid lift is in nbr. */
static int anneal(double until) {
    int nb = 2 * K;
    uint32_t full = (uint32_t)((1ULL << nb) - 1ULL);
    random_state();
    long cost = evaluate();
    memcpy(reach, reach_new, sizeof(uint32_t) * (size_t)N);
    long bestc = cost, it = 0, last_imp = 0;
    double T = 2.0 + 0.01 * (double)cost;
    while (cost > 0) {
        if (now() > until) return 0;
        it++;
        if (it - last_imp > PATIENCE) {
            random_state();
            cost = evaluate();
            memcpy(reach, reach_new, sizeof(uint32_t) * (size_t)N);
            bestc = cost;
            last_imp = it;
            T = 2.0 + 0.01 * (double)cost;
            continue;
        }
        T *= 0.9995;
        if (T < 0.3) T = 0.3;
        long c2;
        if (K >= 2 && rndint(10) < 3) {
            /* swap the B-targets of two A-blocks in one layer */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = t;
            set_dart(l, i1, lay[l][i1], svol[l][i1]);
            set_dart(l, i2, lay[l][i2], svol[l][i2]);
            c2 = evaluate();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
                memcpy(reach, reach_new, sizeof(uint32_t) * (size_t)N);
            } else {
                t = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = t;
                set_dart(l, i1, lay[l][i1], svol[l][i1]);
                set_dart(l, i2, lay[l][i2], svol[l][i2]);
            }
        } else {
            /* change one voltage, focusing on an unreached vertex half of the time */
            int fl = -1, fi = -1;
            if (rnd01() < 0.5) {
                for (int tr = 0; tr < 40; tr++) {
                    int v = rndint(N);
                    if (reach[v] != full) {
                        int blk = v / G;
                        fl = rndint(d);
                        if (blk < K) {
                            fi = blk;
                        } else {
                            int p = blk - K;
                            for (int j = 0; j < K; j++)
                                if (lay[fl][j] == p) { fi = j; break; }
                        }
                        break;
                    }
                }
            }
            if (fi < 0) {
                fl = rndint(d);
                fi = rndint(K);
            }
            int old = svol[fl][fi];
            int nv = rndint(G);
            if (nv == old) continue;
            svol[fl][fi] = nv;
            set_dart(fl, fi, lay[fl][fi], nv);
            c2 = evaluate();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
                memcpy(reach, reach_new, sizeof(uint32_t) * (size_t)N);
            } else {
                svol[fl][fi] = old;
                set_dart(fl, fi, lay[fl][fi], old);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last_imp = it;
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    double slice_max = atof(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t_end = now() + budget * 0.9 - 0.2;
    int ncand = (argc - 6) / 4;
    for (int c = 0; c < ncand; c++) {
        int k = atoi(argv[6 + 4 * c]);
        int m = atoi(argv[7 + 4 * c]);
        int k2 = atoi(argv[8 + 4 * c]);
        int r = atoi(argv[9 + 4 * c]);
        if (k < 1 || k > MAXK || m < 2 || k2 < 1 || k2 > MAXK2 || r < 0 || r >= m) continue;
        long Nc = 2L * k * m * k2;
        if (Nc > MAXN || Nc <= bestN) continue;
        double remaining = t_end - now();
        if (remaining <= 0.05) break;
        K = k;
        setup_group(m, k2, r);
        N = 2 * K * G;
        double until = now() + (slice_max < remaining ? slice_max : remaining);
        if (anneal(until)) {
            bestN = N;
            bK = K;
            bG = G;
            bN = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)N * d);
        }
    }
    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bN, bK * bG * d);
    for (int u = 0; u < bK * bG; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, bestnbr[u * d + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent program).
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
# Candidate generation for the C lift search.
# ----------------------------------------------------------------------------

_KS = (1, 2, 2, 3, 4, 5, 6)


def _group_for(G, rng):
    """Return (m, k2, r) with m * k2 == G and Z_m x| Z_k2 a valid semidirect product (r^k2 = 1 mod m).

    Prefers non-cyclic groups; falls back to the cyclic group Z_G.
    """
    divs = [x for x in range(2, min(G, 40) + 1) if G % x == 0 and G // x >= 2]
    if divs and rng.random() < 0.85:
        k2 = rng.choice(divs)
        m = G // k2
        for _ in range(300):
            r = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return G, 1, 1


def _candidates(lo, hi, count, rng):
    """Candidates (k, m, k2, r) with orders spread over [lo, hi], in ascending order."""
    out = []
    for i in range(count):
        target = lo + ((hi - lo) * i) // max(1, count - 1)
        k = rng.choice(_KS)
        G = max(2, -(-target // (2 * k)))
        m, k2, r = _group_for(G, rng)
        out.append((2 * k * m * k2, k, m, k2, r))
    out.sort()
    return [c[1:] for c in out]


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main phase: one C call that tries bi-Cayley lifts over semidirect products,
    # ascending in order from 0.2 to 0.3 of the Moore bound.
    moore = lib.moore_bound(d, D)
    if d <= 16 and D >= 3 and best_n < moore:
        lo = max(best_n + 2, int(0.20 * moore))
        hi = min(int(0.30 * moore), 16000)
        remaining = final - time.monotonic() - 1.0
        if hi > lo and remaining > 2.0:
            try:
                cands = _candidates(lo, hi, 60, rng)
                slice_s = min(6.0, max(1.0, remaining / 12.0))
                args = [d, D, seed, round(remaining, 2), round(slice_s, 2)]
                for c in cands:
                    args.extend(c)
                text = lib.run_c(C_SOURCE, args, stdin_graph=None, timeout=remaining + 10.0)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
