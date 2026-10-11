import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parents).
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
# C engine: bi-Cayley lifts over Z_m x|_r Z_k2 with voltage annealing,
# reheating from the best state of each group, coordinate polish near zero,
# and group orders chosen just above the best order found so far.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart e = l*K+i joins
# A_{i,g} to B_{dJ[e], g*dS[e]}. Each layer is a permutation, so the graph is
# DEG-regular. Left multiplication is an automorphism, so BFS from the 2K
# representatives decides the diameter exactly.
# Cost = unreached (representative, vertex) pairs + PEN * duplicate darts.
#
# Usage: prog d D seed time_limit min_n
# Prints a valid graph with more than min_n vertices as "n m" + edges, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGC (1 << 30)
#define MAXE 256
#define MAXG 8000
#define VCAP (6 * MAXG)
#define ITERS 40000
#define POLISH_T 80
#define NKF 25

static const int KF[NKF] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                            18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

static int DEG, DIAM;
static int K, MM, K2, G, N, NE;
static int POWR[64];
static int dJ[MAXE], dS[MAXE], bJ[MAXE], bS[MAXE], gJ[MAXE], gS[MAXE];
static int gcost;
static int *adj, *cnt, *fr, *nx;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * (long long)c) % MM;
    return (int)(t * K2 + (b + d) % K2);
}

static void set_group(int Kc, int M, int k2, int r) {
    K = Kc;
    MM = M;
    K2 = k2;
    G = M * k2;
    N = 2 * K * G;
    NE = DEG * K;
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (e1 % K == e2 % K && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int i = e % K;
        int ba = i * G, bb = (K + dJ[e]) * G, s = dS[e];
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + gmul(g, s);
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    long total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)VCAP);
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
            int *tmp = cur;
            cur = nxt;
            nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return (int)total + PEN * dup;
}

static void random_state(void) {
    int p[4];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < K; i++) dJ[l * K + i] = p[i];
    }
    for (int e = 0; e < NE; e++) dS[e] = rndint(G);
}

static void kick(int nk) {
    for (int q = 0; q < nk; q++) dS[rndint(NE)] = rndint(G);
}

static void load_group_best(void) {
    memcpy(dJ, gJ, sizeof(int) * (size_t)NE);
    memcpy(dS, gS, sizeof(int) * (size_t)NE);
}

static void record(int c) {
    if (c < gcost) {
        gcost = c;
        memcpy(gJ, dJ, sizeof(int) * (size_t)NE);
        memcpy(gS, dS, sizeof(int) * (size_t)NE);
    }
}

/* Annealing; leaves the state at the best cost seen and returns that cost. */
static int anneal(long iters, double T0, double tend) {
    int cur = cost_fn();
    int bestc = cur;
    memcpy(bJ, dJ, sizeof(int) * (size_t)NE);
    memcpy(bS, dS, sizeof(int) * (size_t)NE);
    for (long t = 0; t < iters && cur != 0; t++) {
        if ((t & 255) == 0 && now_s() > tend) break;
        double T = T0 * (1.0 - (double)t / (double)iters) + 0.02;
        if (K > 1 && rndint(10) < 3) {
            int l = rndint(DEG), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tmp = dJ[e1];
            dJ[e1] = dJ[e2];
            dJ[e2] = tmp;
            int c2 = cost_fn();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                tmp = dJ[e1];
                dJ[e1] = dJ[e2];
                dJ[e2] = tmp;
            }
        } else {
            int e = rndint(NE), old = dS[e], ns = rndint(G);
            if (ns == old) continue;
            dS[e] = ns;
            int c2 = cost_fn();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                dS[e] = old;
            }
        }
        if (cur < bestc) {
            bestc = cur;
            memcpy(bJ, dJ, sizeof(int) * (size_t)NE);
            memcpy(bS, dS, sizeof(int) * (size_t)NE);
        }
    }
    memcpy(dJ, bJ, sizeof(int) * (size_t)NE);
    memcpy(dS, bS, sizeof(int) * (size_t)NE);
    return bestc;
}

/* Best-improvement sweeps over every single voltage, plus dart-target swaps. */
static int polish(double tend) {
    int cur = cost_fn();
    int improved = 1;
    while (improved && cur != 0) {
        improved = 0;
        for (int e = 0; e < NE && cur != 0; e++) {
            int old = dS[e];
            int bestv = old, bestc = cur;
            for (int s = 0; s < G; s++) {
                if ((s & 15) == 0 && now_s() > tend) {
                    dS[e] = old;
                    return cur;
                }
                if (s == old) continue;
                dS[e] = s;
                int c2 = cost_fn();
                if (c2 < bestc) {
                    bestc = c2;
                    bestv = s;
                }
            }
            dS[e] = bestv;
            if (bestv != old) {
                cur = bestc;
                improved = 1;
            }
        }
        if (K > 1) {
            for (int l = 0; l < DEG && cur != 0; l++)
                for (int i1 = 0; i1 < K && cur != 0; i1++)
                    for (int i2 = i1 + 1; i2 < K && cur != 0; i2++) {
                        if (now_s() > tend) return cur;
                        int e1 = l * K + i1, e2 = l * K + i2;
                        int t = dJ[e1];
                        dJ[e1] = dJ[e2];
                        dJ[e2] = t;
                        int c2 = cost_fn();
                        if (c2 < cur) {
                            cur = c2;
                            improved = 1;
                        } else {
                            t = dJ[e1];
                            dJ[e1] = dJ[e2];
                            dJ[e2] = t;
                        }
                    }
        }
    }
    return cur;
}

static void sample_group(long target, int *oM, int *oK2, int *oR) {
    int k = KF[rndint(NKF)];
    long long m = ((long long)target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
            long long c = 2 + (long long)rndint((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = (int)m;
    *oK2 = k;
    *oR = r;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int best_n = atoi(argv[5]);
    if (DEG < 1 || DEG > 60 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    adj = malloc(sizeof(int) * (size_t)VCAP * (size_t)DEG);
    cnt = malloc(sizeof(int) * (size_t)VCAP);
    fr = malloc(sizeof(int) * (size_t)VCAP);
    nx = malloc(sizeof(int) * (size_t)VCAP);
    vis = calloc((size_t)VCAP, sizeof(uint32_t));
    if (!adj || !cnt || !fr || !nx || !vis) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd64();

    double t0 = now_s();
    deadline = t0 + tl;

    int have = 0;
    int outN = 0, outK = 1, outM = 1, outK2 = 1, outR = 1;
    static int oJ[MAXE], oS[MAXE];

    while (now_s() < deadline - 0.1) {
        int rr = rndint(100);
        int Kc = rr < 60 ? 1 : (rr < 88 ? 2 : 3);
        if (DEG * Kc > MAXE) Kc = 1;
        long g0 = (long)best_n / (2 * Kc) + 1;
        long target = g0 + (long)rndint((int)(g0 / 20 + 5));
        int M, k2, R;
        sample_group(target, &M, &k2, &R);
        long GG = (long)M * k2;
        if (GG > MAXG) continue;
        long Nc = 2L * Kc * GG;
        if (Nc <= best_n) continue;
        set_group(Kc, M, k2, R);

        double cap = 3.0 + 0.5 * (double)rndint(13);
        double gend = now_s() + cap;
        if (gend > deadline) gend = deadline;
        gcost = BIGC;
        random_state();
        int c = anneal(ITERS, 1.5, gend);
        if (c > 0 && c <= POLISH_T) c = polish(gend);
        record(c);
        while (gcost > 0 && now_s() < gend) {
            if (rndint(4) == 0) {
                random_state();
            } else {
                load_group_best();
                kick(NE / 8 + 1);
            }
            c = anneal(ITERS / 2, 0.8, gend);
            if (c > 0 && c <= POLISH_T) c = polish(gend);
            record(c);
        }
        if (gcost == 0) {
            have = 1;
            best_n = (int)Nc;
            outN = (int)Nc;
            outK = Kc;
            outM = M;
            outK2 = k2;
            outR = R;
            memcpy(oJ, gJ, sizeof(int) * (size_t)NE);
            memcpy(oS, gS, sizeof(int) * (size_t)NE);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    (void)outN;
    set_group(outK, outM, outK2, outR);
    memcpy(dJ, oJ, sizeof(int) * (size_t)NE);
    memcpy(dS, oS, sizeof(int) * (size_t)NE);
    printf("%d %d\n", N, NE * G);
    for (int e = 0; e < NE; e++) {
        int i = e % K;
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", i * G + g, (K + dJ[e]) * G + gmul(g, dS[e]));
        }
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then one C search run.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

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
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: one C run that anneals bi-Cayley lifts until its budget ends.
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic() - 0.5
        if remaining >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{remaining:.2f}", best[0]],
                                timeout=time_limit - 2.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
