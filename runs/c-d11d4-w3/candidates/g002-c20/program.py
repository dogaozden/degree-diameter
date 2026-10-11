import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over groups, searched by hill climbing.
#
# A candidate is a base graph with KB left orbits and KB right orbits, each of
# size G, and degree DEGD = d. Layer t (t < d) is a permutation P[t] of the
# orbits plus a group element E[t][i] per left orbit i. Left vertex (i, g) is
# joined to right vertex (P[t][i], g*E[t][i]) for each layer t. The group is
# Z_m x|_r Z_k (r = 1 gives the direct product, k = 1 gives cyclic).
#
# Left translations are automorphisms, so diameter <= D is equivalent to a
# BFS of depth D from (e, a) reaching all 2*KB*G vertices, for each of the 2*KB
# base vertices a. The cost is the number of unreached pairs, plus a penalty for
# parallel edges. Cost 0 gives a valid graph of order 2*KB*G.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1200
#define MAXK 4
#define MAXD 16
#define MAXV (2 * MAXK * MAXG)
#define WIN 4
#define ITERS 3000
#define TEMP 0.7

static int DEGD, DIAM;
static int KB, GG;
static int PW[MAXG];
static int MT[MAXG * MAXG];
static int INV[MAXG];
static int P[MAXD][MAXK], Pinv[MAXD][MAXK], E[MAXD][MAXK];

static int stampArr[MAXV], distArr[MAXV], qbuf[MAXV];
static int stampCur = 0;

static uint64_t rs = 1;
static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }
static double rnd01(void) { return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Elements x = a*k + b, a in [0,m), b in [0,k); (a,b)(c,d) = (a + r^b c, b + d). */
static void build_group(int m, int k, int r) {
    GG = m * k;
    for (int b = 0; b < k; b++) PW[b] = (int)powmod(r, b, m);
    for (int x = 0; x < GG; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GG; y++) {
            int c = y / k, d = y % k;
            int am = (int)(((long long)a + (long long)PW[b] * c) % m);
            int bd = (b + d) % k;
            MT[x * GG + y] = am * k + bd;
        }
    }
    for (int x = 0; x < GG; x++) {
        INV[x] = 0;
        for (int y = 0; y < GG; y++)
            if (MT[x * GG + y] == 0) {
                INV[x] = y;
                break;
            }
    }
}

/* Node ids: left (i, g) -> i*GG + g; right (j, h) -> KB*GG + j*GG + h. */
static int bfs_count(int src) {
    stampCur++;
    int qh = 0, qt = 0, half = KB * GG;
    qbuf[qt++] = src;
    stampArr[src] = stampCur;
    distArr[src] = 0;
    while (qh < qt) {
        int u = qbuf[qh++];
        int du = distArr[u];
        if (du >= DIAM) continue;
        if (u < half) {
            int i = u / GG, g = u % GG;
            for (int t = 0; t < DEGD; t++) {
                int w = half + P[t][i] * GG + MT[g * GG + E[t][i]];
                if (stampArr[w] != stampCur) {
                    stampArr[w] = stampCur;
                    distArr[w] = du + 1;
                    qbuf[qt++] = w;
                }
            }
        } else {
            int v = u - half, j = v / GG, h = v % GG;
            for (int t = 0; t < DEGD; t++) {
                int i2 = Pinv[t][j];
                int g2 = MT[h * GG + INV[E[t][i2]]];
                int w = i2 * GG + g2;
                if (stampArr[w] != stampCur) {
                    stampArr[w] = stampCur;
                    distArr[w] = du + 1;
                    qbuf[qt++] = w;
                }
            }
        }
    }
    return qt;
}

static long long eval_cost(void) {
    int N = 2 * KB * GG;
    long long c = 0;
    for (int i = 0; i < KB; i++)
        for (int t = 0; t < DEGD; t++)
            for (int t2 = t + 1; t2 < DEGD; t2++)
                if (P[t][i] == P[t2][i] && E[t][i] == E[t2][i]) c += 4LL * N;
    for (int s = 0; s < 2 * KB; s++) {
        int src = (s < KB) ? s * GG : KB * GG + (s - KB) * GG;
        c += N - bfs_count(src);
    }
    return c;
}

static void fix_pinv(int t) {
    for (int i = 0; i < KB; i++) Pinv[t][P[t][i]] = i;
}

static void random_config(void) {
    for (int t = 0; t < DEGD; t++) {
        int perm[MAXK];
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int x = perm[i];
            perm[i] = perm[j];
            perm[j] = x;
        }
        for (int i = 0; i < KB; i++) P[t][i] = perm[i];
        fix_pinv(t);
        for (int i = 0; i < KB; i++) E[t][i] = rnd(GG);
    }
}

static int climb(long iters) {
    random_config();
    long long c = eval_cost();
    for (long it = 0; it < iters && c > 0; it++) {
        int sP[MAXD][MAXK], sPi[MAXD][MAXK], sE[MAXD][MAXK];
        memcpy(sP, P, sizeof P);
        memcpy(sPi, Pinv, sizeof Pinv);
        memcpy(sE, E, sizeof E);
        int t = rnd(DEGD), i = rnd(KB);
        if (KB == 1 || rnd(4) != 0) {
            int nw = rnd(GG);
            if (nw == E[t][i]) nw = (nw + 1) % GG;
            E[t][i] = nw;
        } else {
            int i2 = rnd(KB - 1);
            if (i2 >= i) i2++;
            int x = P[t][i];
            P[t][i] = P[t][i2];
            P[t][i2] = x;
            fix_pinv(t);
        }
        long long c2 = eval_cost();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / TEMP)) {
            c = c2;
        } else {
            memcpy(P, sP, sizeof P);
            memcpy(Pinv, sPi, sizeof Pinv);
            memcpy(E, sE, sizeof E);
        }
    }
    return c == 0;
}

static int bestKB = 0, bestM = 0, bestK2 = 0, bestR = 0;
static int bestP[MAXD][MAXK], bestE[MAXD][MAXK];
static long long bestN = 0;

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEGD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    double tgt = argc >= 6 ? atof(argv[5]) : 1700.0;
    if (DEGD < 2 || DEGD > MAXD || DIAM < 2 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    double t0 = now_sec();
    int fails = 0;
    while (now_sec() - t0 < tl) {
        int k = 1 + rnd(MAXK);
        double lo = ceil(tgt / (2.0 * k));
        if (bestN > 0) {
            double g2 = (double)(bestN / (2 * k)) + 1.0;
            if (g2 > lo) lo = g2;
        }
        int G = (int)lo + rnd(WIN);
        if (G < 2) G = 2;
        if (G >= MAXG) G = MAXG - 1;

        int divs[64], nd = 0;
        for (int mm = 1; mm <= G && nd < 64; mm++)
            if (G % mm == 0) divs[nd++] = mm;
        int m = divs[rnd(nd)];
        int kk = G / m;
        int cands[MAXG], nc = 0;
        for (int rr = 0; rr < m; rr++)
            if (gcd_int(rr, m) == 1 && powmod(rr, kk, m) == 1 % m) cands[nc++] = rr;
        if (nc == 0) continue;
        int r = cands[rnd(nc)];

        KB = k;
        build_group(m, kk, r);
        int ok = climb(ITERS);
        if (ok) {
            fails = 0;
            long long N = 2LL * k * G;
            if (N > bestN) {
                bestN = N;
                bestKB = k;
                bestM = m;
                bestK2 = kk;
                bestR = r;
                memcpy(bestP, P, sizeof P);
                memcpy(bestE, E, sizeof E);
            }
        } else if (bestN == 0) {
            if (++fails >= 15) {
                tgt -= tgt / 100.0 + 1.0;
                fails = 0;
            }
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    KB = bestKB;
    build_group(bestM, bestK2, bestR);
    memcpy(P, bestP, sizeof P);
    memcpy(E, bestE, sizeof E);
    for (int t = 0; t < DEGD; t++) fix_pinv(t);
    int half = KB * GG;
    long long edges = (long long)half * DEGD;
    printf("%d %lld\n", 2 * half, edges);
    for (int i = 0; i < KB; i++)
        for (int g = 0; g < GG; g++)
            for (int t = 0; t < DEGD; t++)
                printf("%d %d\n", i * GG + g, half + P[t][i] * GG + MT[g * GG + E[t][i]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) incidence graph for the largest prime power q <= 9 with q + 1 <= d (fallback only)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3: projective plane incidence, and the Araujo-Pardo-Lopez graph when d-2 is a prime power.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
        return best

    if D == 2:
        return best

    # D >= 4: generalized quadrangle fallback, then the bi-Cayley lift search in C.
    moore = lib.moore_bound(d, D)
    if D == 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    remaining = start + 0.9 * tl - time.monotonic() - 2.0
    if d >= 2 and remaining > 3.0:
        tgt = max(best_n + 2, int(0.76 * moore))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", str(tgt)],
                            stdin_graph=None, timeout=remaining + 5.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    return best
