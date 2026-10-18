"""Bi-Cayley lift annealing in C: lifts over Z_m x| Z_k with k base orbits, scored by
BFS from one representative per block (vertex-transitivity under left translation)."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: bi-Cayley lifts over Z_m x| Z_k. Vertices A_{i,g} = i*GO + g and
# B_{j,h} = (BK+j)*GO + h. Layer l matches A_i with B_{layers[l][i]} through
# voltage s: A_{i,g} ~ B_{j, g*s}. Left translation is an automorphism, so the
# diameter test is one BFS from each of the 2*BK block representatives.
# Simulated annealing over layers and voltages; the group order is chosen
# just above the current best order, with random divisor/semidirect choices.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXDEG 16
#define MAXK 8
#define MAXG 16384

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Group Z_GM x| Z_GK, element (a,b) = a*GK+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int GM, GK, GO;
static int RP[MAXG];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long ta = ((long)a + (long)RP[b] * c) % GM;
    return (int)(ta * GK + (b + e) % GK);
}

static int choose_group(int order) {
    static int divs[512];
    for (int attempt = 0; attempt < 50; attempt++) {
        int nd = 0;
        for (int k = 1; k <= order / 2 && nd < 512; k++)
            if (order % k == 0) divs[nd++] = k;
        if (nd == 0) return 0;
        int kk = divs[rndint(nd)];
        int m = order / kk;
        int r = 1 % m;
        if (kk > 1) {
            int ok = 0;
            for (int t = 0; t < 400; t++) {
                int c = 1 + rndint(m - 1);
                if (gcd_i(c, m) == 1 && powmod(c, kk, m) == 1 % m) {
                    r = c;
                    ok = 1;
                    break;
                }
            }
            if (!ok) continue;
        }
        GM = m;
        GK = kk;
        GO = order;
        RP[0] = 1 % m;
        for (int b = 1; b < kk; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
        return 1;
    }
    return 0;
}

/* Current configuration. */
static int BK, NV;
static int layers[MAXDEG][MAXK];
static int S[MAXDEG][MAXK];
static int nb[MAXN * MAXDEG];
static int bestnb[MAXN * MAXDEG];
static int bestNV = 0;

static void rebuild(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < BK; i++) {
            int j = layers[l][i], s = S[l][i];
            int ba = i * GO, bb = (BK + j) * GO;
            for (int g = 0; g < GO; g++) {
                int a = ba + g;
                int b = bb + gmul(g, s);
                nb[a * d + l] = b;
                nb[b * d + l] = a;
            }
        }
}

static int stampv[MAXN];
static int curstamp = 0;
static int qv[MAXN];

/* Number of vertices within distance D of src. */
static int ball(int src) {
    if (++curstamp == 0x7fffffff) {
        memset(stampv, 0, sizeof stampv);
        curstamp = 1;
    }
    int head = 0, tail = 0;
    stampv[src] = curstamp;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            const int *p = nb + qv[head++] * d;
            for (int l = 0; l < d; l++) {
                int u = p[l];
                if (stampv[u] != curstamp) {
                    stampv[u] = curstamp;
                    qv[tail++] = u;
                }
            }
        }
    }
    return tail;
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < BK; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

static long evaluate(void) {
    long unreached = 0;
    for (int b = 0; b < 2 * BK; b++) unreached += NV - ball(b * GO);
    return unreached + 300L * dupcount();
}

static void random_config(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < BK; i++) layers[l][i] = i;
        for (int i = BK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < BK; i++) S[l][i] = rndint(GO);
    }
    rebuild();
}

static int anneal(long iters, double until) {
    random_config();
    long cur = evaluate();
    long c0 = cur > 1 ? cur : 1;
    double T0 = 0.02 * (double)c0;
    if (T0 < 1.0) T0 = 1.0;
    const double Tend = 0.2;
    long last = 0, best = cur;
    long patience = iters / 3 + 200;
    for (long t = 0; t < iters; t++) {
        if (cur == 0) return 1;
        if ((t & 15) == 0 && now() > until) return 0;
        if (t - last > patience) return 0;
        double T = T0 * pow(Tend / T0, (double)t / (double)iters);
        if (BK >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(BK), i2 = rndint(BK - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = tmp;
            rebuild();
            long c2 = evaluate();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                rebuild();
            }
        } else {
            int l = rndint(d), i = rndint(BK);
            int old = S[l][i], nw = rndint(GO);
            if (nw == old) continue;
            S[l][i] = nw;
            rebuild();
            long c2 = evaluate();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                S[l][i] = old;
                rebuild();
            }
        }
        if (cur < best) {
            best = cur;
            last = t;
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [minN]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long minN = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    long best_n = minN;
    int have = 0;
    int skips = 0;
    while (now() < t_end && best_n < cap && skips < 2000) {
        int bk = 1 + rndint(6);
        long unit = 2L * bk;
        long gmin = best_n / unit + 1;
        if (gmin < 2) gmin = 2;
        long gmax = cap / unit;
        if (gmax < gmin) {
            skips++;
            continue;
        }
        long spread = gmin / 10 + 2;
        long gt = gmin + rndint((int)spread);
        if (gt > gmax) gt = gmax;
        if (!choose_group((int)gt)) {
            skips++;
            continue;
        }
        skips = 0;
        BK = bk;
        NV = 2 * BK * GO;
        if (anneal(8000, t_end) && NV > best_n) {
            best_n = NV;
            have = 1;
            bestNV = NV;
            memcpy(bestnb, nb, sizeof(int) * (size_t)NV * d);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    int half = bestNV / 2;
    printf("%d %d\n", bestNV, half * d);
    for (int v = 0; v < half; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, bestnb[v * d + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace best with (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Search: C bi-Cayley lift annealing, seeded with the best graph so far.
    if D >= 2 and d <= 16:
        budget = end - time.monotonic() - 0.5
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                                 stdin_graph=None, timeout=budget + 10)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
