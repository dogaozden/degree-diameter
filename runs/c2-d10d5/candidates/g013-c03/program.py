import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: Cayley-type bipartite search over groups G = Z_m x| Z_k2.
#
# Graph: A_g = g and B_h = G + h for g, h in G. The connection set S has DEG
# distinct elements, and A_g ~ B_{g*s} for s in S. Every vertex then has degree
# exactly DEG, and the graph is simple and bipartite.
#
# Left multiplication is an automorphism, so the diameter is at most DIAM iff
# every vertex is within DIAM of A_e and of B_e. The cost is the number of
# vertices unreached by those two BFS runs. Cost 0 means a valid graph of order
# 2|G|. Simulated annealing replaces one element of S at a time.
#
# Groups are sampled with order just above (best/2), so each success raises the
# order by a little. Group choices include abelian products (r = 1) and
# semidirect products with r^k = 1 mod m, built from random units.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK2 128

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

static const int K2_CH[] = {1, 2, 2, 3, 4, 4, 5, 6, 6, 8, 8, 9, 10, 12, 12,
                            15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40, 48, 50, 60};
#define NCH ((int)(sizeof(K2_CH) / sizeof(K2_CH[0])))

static int DEG, DIAM, CAP;
static int M, K2, G;
static int64_t R;
static int64_t PWR[MAXK2];
static int *AA, *BB;
static int S[MAXD], SI[MAXD];
static int *qu;
static uint32_t *vis;
static uint32_t stamp;
static double tstart, TL;
static int timedout;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    if (b < 0) b += m;
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

/* (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb);
}

static int sample_group(int64_t target) {
    for (int att = 0; att < 400; att++) {
        int k2 = K2_CH[rndint(NCH)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > CAP / 2) continue;
        int64_t r = 1;
        if (k2 > 1 && m > 2 && rnd01() < 0.8) {
            int64_t phi = 0;
            for (int64_t c = 1; c <= m; c++)
                if (gcd64(c, m) == 1) phi++;
            if (phi % k2 != 0) continue;
            int64_t u = 0;
            for (int tr = 0; tr < 50; tr++) {
                int64_t c = 2 + rndint((int)(m - 2));
                if (gcd64(c, m) == 1) {
                    u = c;
                    break;
                }
            }
            if (u == 0) continue;
            r = powmod(u, phi / k2, m);   /* r^k2 = u^phi = 1 mod m */
        }
        M = (int)m;
        K2 = k2;
        R = r % m;
        G = (int)(m * k2);
        if (G < DEG + 1) continue;
        return 1;
    }
    return 0;
}

static void setup_group(void) {
    PWR[0] = 1 % M;
    for (int t = 1; t < K2; t++) PWR[t] = PWR[t - 1] * R % M;
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

static void set_inv(int j) {
    SI[j] = ginv(S[j]);
}

/* true if x equals S[i] for some i < n, i != skip */
static int inS_ex(int x, int skip, int n) {
    for (int i = 0; i < n; i++)
        if (i != skip && S[i] == x) return 1;
    return 0;
}

static int64_t eval_cost(void) {
    int64_t total = 0;
    int N = 2 * G;
    for (int side = 0; side < 2; side++) {
        int src = side ? G : 0;
        stamp++;
        if (stamp == 0) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)(CAP + 1));
            stamp = 1;
        }
        int tail = 0;
        qu[tail++] = src;
        vis[src] = stamp;
        int fs = 0, fe = 1;
        for (int t = 0; t < DIAM && fs < fe; t++) {
            for (int i = fs; i < fe; i++) {
                int v = qu[i];
                if (v < G) {
                    for (int j = 0; j < DEG; j++) {
                        int w = G + gmul(v, S[j]);
                        if (vis[w] != stamp) {
                            vis[w] = stamp;
                            qu[tail++] = w;
                        }
                    }
                } else {
                    int h = v - G;
                    for (int j = 0; j < DEG; j++) {
                        int w = gmul(h, SI[j]);
                        if (vis[w] != stamp) {
                            vis[w] = stamp;
                            qu[tail++] = w;
                        }
                    }
                }
            }
            fs = fe;
            fe = tail;
        }
        total += N - tail;
    }
    return total;
}

/* Simulated annealing on S for the current group. Returns the final cost;
   on cost 0, S holds a valid connection set. */
static int64_t anneal(int iters, int patience) {
    for (int j = 0; j < DEG; j++) {
        int x;
        do {
            x = rndint(G);
        } while (inS_ex(x, -1, j));
        S[j] = x;
        set_inv(j);
    }
    int64_t cost = eval_cost();
    int64_t best = cost;
    int last = 0;
    double c0 = cost > 1 ? (double)cost : 1.0;
    double T0 = 1.0 + 0.02 * c0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 15) == 0 && elapsed() > TL) {
            timedout = 1;
            break;
        }
        double T = T0 * (1.0 - (double)t / iters) + 0.05;
        int j = rndint(DEG);
        int old = S[j];
        int x;
        do {
            x = rndint(G);
        } while (inS_ex(x, j, DEG));
        S[j] = x;
        set_inv(j);
        int64_t c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            S[j] = old;
            set_inv(j);
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    long long found = atoll(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 7) * 0x9E3779B97F4A7C15ULL ^ 0xA0761D6478BD642FULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > MAXD || DIAM < 2 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    AA = malloc(sizeof(int) * (size_t)(CAP + 1));
    BB = malloc(sizeof(int) * (size_t)(CAP + 1));
    qu = malloc(sizeof(int) * (size_t)(CAP + 1));
    vis = calloc((size_t)(CAP + 1), sizeof(uint32_t));
    int half_cap = CAP / 2 + 1;
    int *bu = malloc(sizeof(int) * (size_t)half_cap * DEG);
    int *bv = malloc(sizeof(int) * (size_t)half_cap * DEG);
    if (!AA || !BB || !qu || !vis || !bu || !bv) {
        printf("0 0\n");
        return 0;
    }

    int bestN = 0, bestE = 0;
    while (elapsed() < TL) {
        if (found >= CAP) break;
        int64_t half = found / 2;
        int64_t span = found / 30 + 4;
        int64_t target = half + 1 + rndint((int)span);
        if (!sample_group(target)) continue;
        int N = 2 * G;
        if (N <= found || N > CAP) continue;
        setup_group();
        int ok = 0;
        for (int trial = 0; trial < 3 && !ok && elapsed() < TL; trial++) {
            int64_t c = anneal(8000, 2500);
            if (c == 0) ok = 1;
            if (timedout) break;
        }
        if (ok) {
            found = N;
            bestN = N;
            bestE = 0;
            for (int g = 0; g < G; g++) {
                for (int j = 0; j < DEG; j++) {
                    bu[bestE] = g;
                    bv[bestE] = G + gmul(g, S[j]);
                    bestE++;
                }
            }
        }
        if (timedout) break;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestE);
    for (int i = 0; i < bestE; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Main build: exact small constructions, then the C Cayley-type search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: Cayley-type bipartite graphs over sampled groups, in C.
    if d >= 3 and D >= 2:
        remaining = deadline - time.monotonic()
        cap = lib.moore_bound(d, D)
        if remaining > 3.0 and best_n < cap:
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, cap, int(seed) & 0x7FFFFFFF, round(remaining - 2.0, 2), best_n],
                    timeout=remaining + 5.0,
                )
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
