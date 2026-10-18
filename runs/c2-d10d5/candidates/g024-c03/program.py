import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold variant: voltage lifts of FIXED small base graphs, searched in C.
#
# A base graph B (bipartite, simple, up to 512 vertices) is lifted by a group
# G of order g (cyclic or Z_m x|_r Z_k2). The lift has |B|*g vertices and the
# same degrees as B. Group multiplication acts on the left and is an
# automorphism, so distance(p, q) only depends on the sources (u, e) for each
# base vertex u. The cost is the number of (source, vertex) pairs at distance
# more than D, computed with per-vertex bitsets over the |B| sources.
#
# Base graphs used:
#   - the point-line incidence graph of PG(2, q), q + 1 <= d (order 182 for d = 10),
#   - a Haar graph on 6d + 6d vertices with d random shifts (a second base).
# Search: simulated annealing over one voltage per base edge, defect-targeted
# moves, and iterated local search from the best near miss.
# The start graph is the base itself, which is always valid, and every
# candidate is checked with lib.is_valid before it is returned.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define WMAX 8
#define MAXB 512
#define MAXDEG 64
#define MAXE 16384
#define MAXN 40000
#define KMAX 64

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

static double TL, tstart;
static int timed_out;
static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
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

/* base graph: side A = 0..NA-1, side B = NA..NB-1 */
static int DIAM, NA, NB, NE, DEG, W;
static int EA[MAXE], EB[MAXE];
static int bdeg[MAXB];
static int binc[MAXB][MAXDEG];

/* group Z_M x|_R Z_K2, element (a,b) coded as a*K2+b, order G */
static int M, K2, R, G, N;
static int64_t PWR[KMAX];
static int AA[MAXN], BB[MAXN];

static int S[MAXE], SI[MAXE];
static int bestS[MAXE], nearS[MAXE];
static int nbr[MAXN * MAXDEG];
static uint64_t RA[MAXN * WMAX], RB[MAXN * WMAX];
static int vA[MAXN], vB[MAXN];
static int *vcur = vA, *vnew = vB;

static void set_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    R = r;
    G = m * k2;
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
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

static int sample_group(int target) {
    static const int ch[12] = {1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    for (int att = 0; att < 100; att++) {
        int k2 = ch[rndint(12)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t g = m * k2;
        if (g * NB > MAXN) continue;
        int64_t r = 1;
        if (k2 > 1 && m > 2) {
            for (int tries = 0; tries < 200; tries++) {
                int64_t c = 2 + rndint((int)(m - 2));
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }
        set_group((int)m, k2, (int)r);
        return 1;
    }
    return 0;
}

static void build_nbr(void) {
    for (int e = 0; e < NE; e++) SI[e] = ginv(S[e]);
    for (int v = 0; v < N; v++) {
        int u = v / G;
        int x = v - u * G;
        for (int j = 0; j < bdeg[u]; j++) {
            int e = binc[u][j];
            int w, y;
            if (u < NA) {
                w = EB[e];
                y = gmul(x, S[e]);
            } else {
                w = EA[e];
                y = gmul(x, SI[e]);
            }
            nbr[v * DEG + j] = w * G + y;
        }
    }
}

/* Returns the number of (source, vertex) pairs at distance > DIAM.
   vout[v] = number of sources not reaching v. */
static int64_t evaluate(int *vout) {
    build_nbr();
    size_t WW = (size_t)W;
    memset(RA, 0, sizeof(uint64_t) * (size_t)N * WW);
    for (int u = 0; u < NB; u++) {
        size_t idx = (size_t)(u * G) * WW + (size_t)(u >> 6);
        RA[idx] |= 1ULL << (u & 63);
    }
    uint64_t *cur = RA, *nxt = RB;
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            int u = v / G;
            uint64_t acc[WMAX];
            const uint64_t *pv = cur + (size_t)v * WW;
            for (int k = 0; k < W; k++) acc[k] = pv[k];
            for (int j = 0; j < bdeg[u]; j++) {
                const uint64_t *pw = cur + (size_t)nbr[v * DEG + j] * WW;
                for (int k = 0; k < W; k++) acc[k] |= pw[k];
            }
            uint64_t *out = nxt + (size_t)v * WW;
            for (int k = 0; k < W; k++) out[k] = acc[k];
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    int64_t cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *pv = cur + (size_t)v * WW;
        for (int k = 0; k < W; k++) c += popc64(pv[k]);
        vout[v] = NB - c;
        cost += NB - c;
    }
    return cost;
}

static int64_t anneal(int iters, int patience) {
    int64_t cost = evaluate(vcur);
    int64_t best = cost;
    int last = 0;
    double c0 = (double)(cost > 1 ? cost : 1);
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        int e = -1;
        if (rnd01() < 0.5) {
            /* defect-targeted: pick a vertex with unreached sources */
            int cnt = 0, pick = -1;
            for (int v = 0; v < N; v++) {
                if (vcur[v] > 0) {
                    cnt++;
                    if (rndint(cnt) == 0) pick = v;
                }
            }
            if (pick >= 0) {
                int u = pick / G;
                if (bdeg[u] > 0) e = binc[u][rndint(bdeg[u])];
            }
        }
        if (e < 0) e = rndint(NE);
        int old = S[e];
        int nw = rndint(G);
        if (nw == old) continue;
        S[e] = nw;
        int64_t c2 = evaluate(vnew);
        double temp = (0.02 * c0 + 0.2) * (1.0 - (double)t / iters) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            int *tp = vcur;
            vcur = vnew;
            vnew = tp;
            cost = c2;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            S[e] = old;
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DIAM = atoi(argv[1]);
    NA = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    int nb, m;
    if (scanf("%d %d", &nb, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (nb < 2 || nb > MAXB || m < 1 || m > MAXE || NA < 1 || NA >= nb || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    NB = nb;
    NE = m;
    W = (NB + 63) / 64;
    for (int u = 0; u < NB; u++) bdeg[u] = 0;
    for (int e = 0; e < NE; e++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (a > b) {
            int t = a;
            a = b;
            b = t;
        }
        if (a < 0 || a >= NA || b < NA || b >= NB) {
            printf("0 0\n");
            return 0;
        }
        if (bdeg[a] >= MAXDEG || bdeg[b] >= MAXDEG) {
            printf("0 0\n");
            return 0;
        }
        EA[e] = a;
        EB[e] = b;
        binc[a][bdeg[a]++] = e;
        binc[b][bdeg[b]++] = e;
    }
    DEG = 0;
    for (int u = 0; u < NB; u++)
        if (bdeg[u] > DEG) DEG = bdeg[u];
    if (DEG < 1) {
        printf("0 0\n");
        return 0;
    }

    long long found = NB; /* the base itself (G = 1) is valid by construction */
    int have_best = 0, bestM = 0, bestK2 = 0, bestR = 0, bestG = 0;
    int have_near = 0, nM = 0, nK2 = 0, nR = 0, nN = 0;
    int64_t nearcost = 0;
    const int ITERS = 6000, PAT = 2000;

    while (elapsed() < TL) {
        int g0 = (int)(found / NB) + 1;
        int target = g0 + ((rnd01() < 0.5) ? 0 : rndint(3));
        int from_near = 0;
        if (have_near && (long long)nN > found && rnd01() < 0.5) from_near = 1;

        if (from_near) {
            set_group(nM, nK2, nR);
            N = NB * G;
            memcpy(S, nearS, sizeof(int) * (size_t)NE);
            int kicks = 2 + rndint(5);
            for (int k = 0; k < kicks; k++) S[rndint(NE)] = rndint(G);
        } else {
            if (target > MAXN / NB) continue;
            if (!sample_group(target)) continue;
            N = NB * G;
            if (N <= found || N > MAXN) continue;
            for (int e = 0; e < NE; e++) S[e] = rndint(G);
        }

        int64_t c = anneal(ITERS, PAT);

        if (c == 0) {
            found = N;
            have_best = 1;
            bestM = M;
            bestK2 = K2;
            bestR = R;
            bestG = G;
            memcpy(bestS, S, sizeof(int) * (size_t)NE);
            have_near = 0;
        } else {
            if (!have_near || c < nearcost || (long long)nN <= found) {
                have_near = 1;
                nearcost = c;
                nN = N;
                nM = M;
                nK2 = K2;
                nR = R;
                memcpy(nearS, S, sizeof(int) * (size_t)NE);
            }
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestM, bestK2, bestR);
    int nv = NB * G;
    long long mc = (long long)NE * G;
    printf("%d %lld\n", nv, mc);
    for (int e = 0; e < NE; e++) {
        int a = EA[e], b = EB[e];
        for (int x = 0; x < G; x++) {
            int y = gmul(x, bestS[e]);
            printf("%d %d\n", a * G + x, b * G + y);
        }
    }
    (void)bestG;
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (used as fallbacks and for calibration cases).
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
# Main build: exact constructions, then voltage-lift searches over two bases.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
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

    # Exact constructions; return immediately on calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Voltage-lift searches over different base graphs, each in its own C run.
    if d >= 3 and D >= 3:
        bases = []
        pg = _best_pg(d)
        if pg is not None and pg[0] <= 512:
            bases.append((pg[0], pg[1], pg[0] // 2))
        m = 6 * d
        if 2 * m <= 512:
            rng = random.Random(int(seed) + 17)
            shifts = rng.sample(range(m), d)
            hn, he = lib.haar_graph(m, shifts)
            bases.append((hn, he, m))

        for idx, (bn, be, na) in enumerate(bases):
            left = deadline - time.monotonic()
            if left < 3.0:
                break
            share = left * (0.6 if (idx == 0 and len(bases) > 1) else 1.0)
            c_budget = share - 1.5  # margin for process start and compile
            if c_budget < 1.0:
                continue
            try:
                text = lib.run_c(C_SOURCE,
                                 [D, na, int(seed) & 0x7FFFFFFF, round(c_budget, 2)],
                                 stdin_graph=(bn, be),
                                 timeout=c_budget + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
