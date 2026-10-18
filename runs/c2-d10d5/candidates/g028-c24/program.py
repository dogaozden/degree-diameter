import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: Haar graphs over non-abelian groups instead of multi-base voltage lifts.
#
# A Haar graph H(G, S) has parts A = {a_g} and B = {b_h}, with a_g ~ b_{gs} for
# s in S, |S| = d. Left multiplication is an automorphism, so the graph is
# vertex-transitive on each side. The diameter is therefore at most D exactly
# when BFS from a_e and from b_e reaches everything within D steps. Each cost
# evaluation is then two BFS passes over 2|G| vertices, which is cheap.
#
# The group family is Z_m x|_r Z_k2 (elements (a,b), (a,b)(c,e) = (a + r^b c, b + e)),
# with r^k2 = 1 mod m. Simulated annealing replaces one element of S at a time.
# The C engine grows |G| past the best known order, and the Python side keeps
# exact constructions (PG(2,q), W(q)) and K_{d,d} as safe fallbacks.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define ITERS 20000

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

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
static double TSTART, TL;
static double elapsed(void) {
    return now_s() - TSTART;
}

static int DEG, DIAM, CAP;
static int M, K2, R, G;
static int64_t PWR[64];
static int S[MAXD], SI[MAXD];
static int *dist, *queue;
static int bestS[MAXD];
static int bestM, bestK2, bestR, bestG;
static int have_best;
static int timed_out;
static int64_t cost_now;

static const int K2C[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24};
#define NK 16

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

static void set_group(void) {
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
}

/* (a,b)(c,e) = (a + r^b c, b + e), element coded as a*K2 + b */
static inline int gmul(int x, int y) {
    int bx = x % K2, ax = x / K2;
    int ay = y / K2, by = y % K2;
    int64_t a2 = (ax + PWR[bx] * (int64_t)ay) % M;
    int b2 = (bx + by) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = x % K2, a = x / K2;
    int nb = (K2 - b) % K2;
    int64_t t = (PWR[nb] * (int64_t)a) % M;
    int64_t a2 = (M - t) % M;
    return (int)(a2 * K2 + nb);
}

static int sample_group(int64_t target) {
    for (int attempt = 0; attempt < 200; attempt++) {
        int k2 = K2C[rndint(NK)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = -1;
        if (k2 == 1) {
            r = 1;
        } else {
            for (int tries = 0; tries < 80; tries++) {
                int64_t c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
            if (r < 0) continue;
        }
        if (m * k2 < DEG) continue;
        M = (int)m;
        K2 = k2;
        R = (int)r;
        G = M * K2;
        set_group();
        return 1;
    }
    return 0;
}

/* BFS from one side's identity vertex; returns number of vertices not reached within DIAM. */
static int64_t bfs_cost(int side0) {
    int N2 = 2 * G;
    for (int i = 0; i < N2; i++) dist[i] = -1;
    int head = 0, tail = 0;
    int s0 = side0 * G;
    dist[s0] = 0;
    queue[tail++] = s0;
    while (head < tail) {
        int v = queue[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        if (v < G) {
            for (int j = 0; j < DEG; j++) {
                int w = G + gmul(v, S[j]);
                if (dist[w] < 0) {
                    dist[w] = dv + 1;
                    queue[tail++] = w;
                }
            }
        } else {
            int h = v - G;
            for (int j = 0; j < DEG; j++) {
                int w = gmul(h, SI[j]);
                if (dist[w] < 0) {
                    dist[w] = dv + 1;
                    queue[tail++] = w;
                }
            }
        }
    }
    return (int64_t)(N2 - tail);
}

static int64_t total_cost(void) {
    return bfs_cost(0) + bfs_cost(1);
}

static void random_S(void) {
    for (int j = 0; j < DEG; j++) {
        int c;
        int ok;
        do {
            c = rndint(G);
            ok = 1;
            for (int q = 0; q < j; q++)
                if (S[q] == c) ok = 0;
        } while (!ok);
        S[j] = c;
        SI[j] = ginv(c);
    }
}

static int anneal(int iters) {
    cost_now = total_cost();
    double c0 = cost_now > 1 ? (double)cost_now : 1.0;
    for (int t = 0; t < iters && cost_now > 0; t++) {
        if (elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double temp = 0.15 * c0 * (1.0 - (double)t / iters) + 0.3;
        int j = rndint(DEG);
        int nw = -1;
        for (int tries = 0; tries < 100; tries++) {
            int c = rndint(G);
            int dup = 0;
            for (int q = 0; q < DEG; q++)
                if (S[q] == c) {
                    dup = 1;
                    break;
                }
            if (!dup) {
                nw = c;
                break;
            }
        }
        if (nw < 0) continue;
        int old = S[j];
        S[j] = nw;
        SI[j] = ginv(nw);
        int64_t c2 = total_cost();
        if (c2 <= cost_now || rnd01() < exp(-(double)(c2 - cost_now) / temp)) {
            cost_now = c2;
        } else {
            S[j] = old;
            SI[j] = ginv(old);
        }
    }
    return cost_now == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    TSTART = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > MAXD || DIAM < 3 || CAP < 2 * DEG) {
        printf("0 0\n");
        return 0;
    }
    int maxG = CAP / 2;
    dist = malloc(sizeof(int) * (size_t)(2 * maxG + 2));
    queue = malloc(sizeof(int) * (size_t)(2 * maxG + 2));
    if (!dist || !queue) {
        printf("0 0\n");
        return 0;
    }

    long long bestN = best0;
    while (elapsed() < TL) {
        long long bestGc = bestN / 2;
        long long span = bestGc / 20 + 2;
        long long tg = bestGc + 1 + rndint((int)span);
        if (!sample_group(tg)) continue;
        if (2LL * G <= bestN || 2LL * G > CAP) continue;

        random_S();
        int ok = anneal(ITERS);
        int extra = 0;
        while (!ok && !timed_out && extra < 3 && cost_now <= 6 && elapsed() < TL) {
            ok = anneal(ITERS);
            extra++;
        }
        if (ok) {
            bestN = 2LL * G;
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            bestM = M;
            bestK2 = K2;
            bestR = R;
            bestG = G;
            have_best = 1;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    M = bestM;
    K2 = bestK2;
    R = bestR;
    G = bestG;
    set_group();
    for (int j = 0; j < DEG; j++) {
        S[j] = bestS[j];
        SI[j] = ginv(S[j]);
    }
    long long m = (long long)G * DEG;
    printf("%d %lld\n", 2 * G, m);
    for (int g = 0; g < G; g++)
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", g, G + gmul(g, S[j]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (kept as strong starts and calibration answers).
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
# Main build: exact constructions, then the Haar-graph annealing in C, with a
# validated fallback at every step.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    final_deadline = start + max(1.0, time_limit - 3.0)

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: Haar graphs over Z_m x| Z_k annealed in C.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best_n:
                try:
                    text = lib.run_c(
                        C_SOURCE,
                        [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                        timeout=remaining + 3.0,
                    )
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
