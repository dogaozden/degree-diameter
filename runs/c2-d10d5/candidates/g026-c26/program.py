import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lift search with source-only eccentricity cost.
#
# A graph is a K-block voltage lift over a group G = Z_M x|_r Z_K2: base
# vertices A_0..A_{K-1}, B_0..B_{K-1}, and for each layer l a permutation
# sig_l of the base indices with group voltage vol[l][i], so A_{i,g} ~ B_{sig_l(i), g*s}.
# G acts on the left by automorphisms, so the diameter equals the maximum
# eccentricity of the 2K identity vertices. The cost is the number of
# (source, vertex) pairs left unreached within DIAM steps, computed with
# 2K-bit masks, plus a penalty for multi-edges. Simulated annealing changes
# voltages and layer permutations. Groups are sampled per trial, with the
# target order just above the best valid graph found so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXDEG 32
#define PEN 20

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static const int KPICK[6] = {1, 1, 2, 2, 3, 4};
static const int K2CH[12] = {1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 6, 8};

static int DEG, DIAM, CAP;
static int K, K2, M, R, G;
static int64_t PWR[16];
static int *nbr;
static int sig[MAXDEG * MAXK];
static int vol[MAXDEG * MAXK];
static uint8_t *ra, *rb;
static uint8_t POP[256];
static double tstart, TL;
static int timed_out;
static int *bestnbr;
static int have_best, bestK, bestG;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* element (a,b) coded as a*K2+b; (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int bx = x % K2, ax = x / K2;
    int cy = y / K2, ey = y % K2;
    int64_t a2 = (ax + PWR[bx] * (int64_t)cy) % M;
    int b2 = (bx + ey) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = x % K2, a = x / K2;
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb] * (int64_t)a) % M) % M;
    return (int)(a2 * K2 + nb);
}

static void set_dart(int l, int i) {
    int j = sig[l * K + i];
    int s = vol[l * K + i];
    int is = ginv(s);
    int Ab = i * G, Bb = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[(size_t)(Ab + g) * DEG + l] = Bb + gmul(g, s);
        nbr[(size_t)(Bb + g) * DEG + l] = Ab + gmul(g, is);
    }
}

static void build_all(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i);
}

static int64_t eval_unreached(void) {
    int S = 2 * K, NN = 2 * K * G;
    memset(ra, 0, (size_t)NN);
    for (int b = 0; b < S; b++) ra[b * G] |= (uint8_t)(1u << b);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            uint8_t x = ra[v];
            const int *nb = nbr + (size_t)v * DEG;
            for (int l = 0; l < DEG; l++) x |= ra[nb[l]];
            rb[v] = x;
            if (x != ra[v]) changed = 1;
        }
        uint8_t *tmp = ra;
        ra = rb;
        rb = tmp;
        if (!changed) break;
    }
    int64_t s = 0;
    for (int v = 0; v < NN; v++) s += POP[ra[v]];
    return (int64_t)S * NN - s;
}

/* multi-edges show up as repeated neighbours of an A-side vertex */
static int64_t dupcount(void) {
    int64_t dup = 0;
    int KG = K * G;
    for (int v = 0; v < KG; v++) {
        const int *nb = nbr + (size_t)v * DEG;
        for (int l = 1; l < DEG; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (nb[l] == nb[l2]) {
                    dup++;
                    break;
                }
    }
    return dup;
}

static int64_t total_cost(void) {
    return eval_unreached() + (int64_t)PEN * dupcount();
}

static int run_trial(int iters) {
    int ne = DEG * K;
    timed_out = 0;
    for (int l = 0; l < DEG; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) sig[l * K + i] = perm[i];
    }
    for (int e = 0; e < ne; e++) vol[e] = rndint(G);
    build_all();

    int64_t cost = total_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;

    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double T = 0.03 * c0 * (1.0 - (double)t / iters) + 0.3;
        double mv = rnd01();
        int64_t c2 = cost;

        if (K >= 2 && mv < 0.3) {
            /* swap the base targets of two sources in one layer */
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tp = sig[e1];
            sig[e1] = sig[e2];
            sig[e2] = tp;
            set_dart(l, i1);
            set_dart(l, i2);
            c2 = total_cost();
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))) {
                tp = sig[e1];
                sig[e1] = sig[e2];
                sig[e2] = tp;
                set_dart(l, i1);
                set_dart(l, i2);
                continue;
            }
        } else if (DEG >= 2 && mv < 0.45) {
            /* swap voltages of one base vertex between two layers */
            int l1 = rndint(DEG);
            int l2 = rndint(DEG - 1);
            if (l2 >= l1) l2++;
            int i = rndint(K);
            int e1 = l1 * K + i, e2 = l2 * K + i;
            if (vol[e1] == vol[e2]) continue;
            int v1 = vol[e1], v2 = vol[e2];
            vol[e1] = v2;
            vol[e2] = v1;
            set_dart(l1, i);
            set_dart(l2, i);
            c2 = total_cost();
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))) {
                vol[e1] = v1;
                vol[e2] = v2;
                set_dart(l1, i);
                set_dart(l2, i);
                continue;
            }
        } else {
            /* change one voltage */
            int l = rndint(DEG);
            int i = rndint(K);
            int e = l * K + i;
            int old = vol[e];
            int nw = rndint(G);
            if (nw == old) continue;
            vol[e] = nw;
            set_dart(l, i);
            c2 = total_cost();
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))) {
                vol[e] = old;
                set_dart(l, i);
                continue;
            }
        }
        cost = c2;
    }
    return cost == 0;
}

/* choose a group of order about target, with 2 <= K2 and r^K2 = 1 mod M */
static int sample_group(int64_t target) {
    for (int att = 0; att < 400; att++) {
        int k2 = K2CH[rndint(12)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = 1;
        if (k2 > 1 && m >= 3 && rnd01() < 0.65) {
            int ok = 0;
            for (int t = 0; t < 100; t++) {
                int64_t c = 2 + rndint((int)(m - 2));
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    ok = 1;
                    break;
                }
            }
            if (!ok) continue;
        }
        M = (int)m;
        K2 = k2;
        R = (int)r;
        G = M * K2;
        for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D found cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long found = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = ((uint64_t)seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (uint8_t)c;
    }

    if (DEG < 3 || DEG > MAXDEG || DIAM < 3 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    nbr = malloc(sizeof(int) * (size_t)CAP * DEG);
    ra = malloc((size_t)CAP);
    rb = malloc((size_t)CAP);
    bestnbr = malloc(sizeof(int) * (size_t)CAP * DEG);
    if (!nbr || !ra || !rb || !bestnbr) {
        printf("0 0\n");
        return 0;
    }

    have_best = 0;
    bestK = 0;
    bestG = 0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = KPICK[rndint(6)];
        int64_t Gmin = found / (2 * k) + 1;
        int64_t span = Gmin / 16 + 2;
        int64_t target = Gmin + rndint((int)span);
        if (!sample_group(target)) continue;
        long long N = 2LL * k * G;
        if (N <= found || N > CAP) continue;

        K = k;
        int ok = run_trial(20000);
        if (ok) {
            found = N;
            int KG = K * G;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)KG * DEG);
            bestK = K;
            bestG = G;
            have_best = 1;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int KG = bestK * bestG;
    printf("%d %d\n", 2 * KG, KG * DEG);
    for (int v = 0; v < KG; v++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", v, bestnbr[(size_t)v * DEG + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact starting constructions.
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
# Main build: exact constructions, then the C lift search, then fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                consider(*_gq_w(q))
                if D == 4 and q == d - 1:
                    return best
                break

    # Main search, entirely in C, starting from the best exact graph.
    if 3 <= d <= 32 and D >= 3:
        budget = max(1.0, min(0.75 * time_limit, time_limit - 10.0))
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), 40000)
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF,
                                  round(remaining, 2)],
                                 timeout=remaining + 5.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
