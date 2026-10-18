"""Bi-Cayley lift annealing in C with exact-order semidirect groups.

Python handles only the exact small constructions (projective planes, Araujo-Lopez, W(q)) and the
fallback. The main search for D >= 5 runs in a C engine. It fixes a base size K (2K blocks), an exact
group order G = m * k2 (semidirect Z_m x| Z_k2, or a direct product when r = 1), and anneals
one voltage per dart plus block permutations per layer. Cost is the number of (block representative,
vertex) pairs at distance > D. Left translations are automorphisms, so checking only the 2K block
representatives is exact. A ratchet pushes the order above the best found so far.

Every returned graph is checked with lib.is_valid. K_{d,d} is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley voltage-lift annealer.
 * Usage: prog d D seed time_limit
 * stdout: "n m" + edges of the best valid lift found ("0 0" if none).
 *
 * Vertices: A-block i (i < K) has vertices i*G + g; B-block j has vertices (K+j)*G + h.
 * Layer l pairs A-block i with B-block pi[l][i] through voltage S[l][i]:
 *   A_{i,g} ~ B_{pi,g*s},  B_{j,h} ~ A_{i,h*s^-1}.
 * Each layer is a perfect matching of blocks, so every vertex has degree d.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 16
#define MAXN 8192
#define PEN 50

static int d, D, K, G, N, m, k2;
static int rpow[64];
static int pi_[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN], reachC[MAXN], trialC[MAXN];
static int bestNbr[MAXD][MAXN];
static int bestN = 0, bestK = 0, bestG = 0;
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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void setup_group(int k2_, int m_, int r) {
    k2 = k2_;
    m = m_;
    G = m * k2;
    rpow[0] = 1 % m;
    for (int b = 1; b < k2; b++) rpow[b] = (int)((long)rpow[b - 1] * r % m);
}

/* Semidirect product Z_m x| Z_k2: (a,b)*(c,e) = (a + r^b c, b + e); element coded a*k2 + b. */
static int mulg(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long t = (a + (long)rpow[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

static int invg(int s) {
    int a = s / k2, b = s % k2, nb = (k2 - b) % k2;
    long t = ((long)rpow[nb] * a) % m;
    long ai = (m - t) % m;
    return (int)(ai * k2 + nb);
}

/* Choose a group of exact order Gt: random divisor k2, random r with r^k2 = 1 mod m, else r = 1. */
static void pick_group(int Gt) {
    int divs[64];
    int nd = 0;
    for (int t = 1; t <= 48 && t <= Gt; t++)
        if (Gt % t == 0) divs[nd++] = t;
    int kc = divs[rndint(nd)];
    int mm = Gt / kc;
    int r = 1 % mm;
    if (kc > 1 && mm > 2) {
        for (int tries = 0; tries < 200; tries++) {
            int c = 2 + rndint(mm - 2);
            long p = 1;
            for (int e = 0; e < kc; e++) p = p * c % mm;
            if (p == 1 % mm) {
                r = c;
                break;
            }
        }
    }
    setup_group(kc, mm, r);
}

static void set_dart(int l, int i) {
    int j = pi_[l][i], s = S[l][i], si = invg(s);
    for (int g = 0; g < G; g++) nbr[l][i * G + g] = (K + j) * G + mulg(g, s);
    for (int h = 0; h < G; h++) nbr[l][(K + j) * G + h] = i * G + mulg(h, si);
}

static void build_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Cost = unreached (representative, vertex) pairs + PEN * duplicate darts.
 * Writes the reach masks to out: bit b set when block representative b is within D of the vertex. */
static long evaluate(uint64_t *out) {
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[b * G] |= 1ULL << b;
    for (int it = 0; it < D; it++) {
        int ch = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            ch |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!ch) break;
    }
    long un = 0;
    for (int v = 0; v < N; v++) un += 2 * K - __builtin_popcountll(cur[v]);
    memcpy(out, cur, sizeof(uint64_t) * (size_t)N);
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (pi_[l1][i] == pi_[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return un + PEN * dup;
}

static void store_best(void) {
    bestN = 2 * K * G;
    bestK = K;
    bestG = G;
    for (int l = 0; l < d; l++)
        for (int v = 0; v < N; v++) bestNbr[l][v] = nbr[l][v];
}

static void print_best(void) {
    if (bestN == 0) {
        printf("0 0\n");
        return;
    }
    int blocks = bestK * bestG;
    long M = (long)d * blocks;
    printf("%d %ld\n", bestN, M);
    for (int l = 0; l < d; l++)
        for (int A = 0; A < blocks; A++) printf("%d %d\n", A, bestNbr[l][A]);
}

/* Simulated annealing over voltages and layer permutations for the current K, G. */
static int anneal(double deadline, long patience) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) pi_[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pi_[l][i];
            pi_[l][i] = pi_[l][j];
            pi_[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
    build_all();
    long cost = evaluate(reachC);
    long bestc = cost, last = 0;
    uint64_t F = (1ULL << (2 * K)) - 1;

    for (long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 15) == 0 && now() > deadline) return 0;
        if (it - last > patience) return 0;
        double T = 0.3 + 3.0 * exp(-(double)it / 2000.0);

        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = pi_[l][i1];
            pi_[l][i1] = pi_[l][i2];
            pi_[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long nc = evaluate(trialC);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                memcpy(reachC, trialC, sizeof(uint64_t) * (size_t)N);
                if (cost < bestc) {
                    bestc = cost;
                    last = it;
                }
            } else {
                t = pi_[l][i1];
                pi_[l][i1] = pi_[l][i2];
                pi_[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = -1, i = -1;
            if (rnd01() < 0.6) {
                int v = -1;
                for (int tries = 0; tries < 20; tries++) {
                    int w = rndint(N);
                    if (reachC[w] != F) {
                        v = w;
                        break;
                    }
                }
                if (v >= 0) {
                    int blk = v / G;
                    l = rndint(d);
                    if (blk < K) {
                        i = blk;
                    } else {
                        int j = blk - K;
                        i = -1;
                        for (int t = 0; t < K; t++)
                            if (pi_[l][t] == j) {
                                i = t;
                                break;
                            }
                    }
                }
            }
            if (l < 0 || i < 0) {
                l = rndint(d);
                i = rndint(K);
            }
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            long nc = evaluate(trialC);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                memcpy(reachC, trialC, sizeof(uint64_t) * (size_t)N);
                if (cost < bestc) {
                    bestc = cost;
                    last = it;
                }
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long cap_total = moore < MAXN ? moore : MAXN;
    static const int Ks[] = {1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 8, 8, 10, 12, 14, 16};
    int nK = 16;
    long best_n = 0;
    int fails = 0;

    while (now() < t_end) {
        int Kc = Ks[rndint(nK)];
        long Gmin = best_n / (2L * Kc) + 1;
        long extra = fails < 4 ? (long)rndint((int)(Gmin / 40) + 1) : 0;
        long Gt = Gmin + extra;
        long cap = cap_total / (2L * Kc);
        if (Gt > cap) Gt = cap;
        if (Gt < Gmin || Gt < 1) continue;

        pick_group((int)Gt);
        K = Kc;
        G = (int)Gt;
        N = 2 * K * G;

        double remaining = t_end - now();
        double slice = remaining / 4.0;
        if (slice < 3.0) slice = 3.0;
        if (slice > remaining) slice = remaining;
        if (slice <= 0) break;

        if (anneal(now() + slice, 4000)) {
            best_n = N;
            store_best();
            fails = 0;
        } else {
            fails++;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact small constructions.
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions. Calibration-style cases return immediately.
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

    # Main search: C bi-Cayley annealing with exact-order semidirect groups and a ratchet.
    budget = 0.85 * time_limit - 2.5 - (time.monotonic() - t0)
    if budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 15)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
