import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
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
# C engine: simulated annealing over bi-Cayley (K = 1) lifts on semidirect
# products Z_m x| Z_k. The graph has vertices A_g = g and B_h = G + h, with
# A_g adjacent to B_{g*s} for each generator s in S (|S| = d, distinct).
# Left multiplication is an automorphism, so the graph is diameter <= D iff
# every vertex of A and every vertex of B is reached within D steps from
# A_e and from B_e. The cost is the number of unreached vertices from those
# two sources; cost 0 means a valid graph. Groups are sampled at order just
# above the best known, so every success raises the target order.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXG 1500
#define ITERS 25000
#define REPS 3

static int Dd = 3, DD = 3;
static int G = 1, GM = 1, GK = 1, GR = 1;
static int mt[MAXG * MAXG];      /* multiplication table, mt[x*G+y] = x*y */
static int iv[MAXG];            /* inverses */
static int pw[MAXG];            /* r^b mod m */
static int S[MAXD], sinv[MAXD];
static int vis[2 * MAXG];
static int que[2 * MAXG];
static int vis_stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

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

/* Group Z_m x|_r Z_k, element (a, b) coded a*k + b,
   (a, b)(c, d) = (a + r^b c, b + d). Requires r^k = 1 mod m. */
static void build_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    G = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        pw[b] = (int)p;
        p = p * r % m;
    }
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, d = y % k;
            long long t = ((long long)a + (long long)pw[b] * c) % m;
            mt[x * G + y] = (int)(t * k + (b + d) % k);
        }
    }
    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            if (mt[x * G + y] == 0) {
                iv[x] = y;
                break;
            }
        }
    }
}

static void sample_group(int g) {
    static const int KL[] = {2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18,
                             20, 21, 24, 27, 28, 30, 32, 36, 40};
    int nk = (int)(sizeof(KL) / sizeof(KL[0]));
    int cand[64];
    int nc = 0;
    for (int i = 0; i < nk; i++) {
        if (g % KL[i] == 0 && g / KL[i] >= 2) cand[nc++] = KL[i];
    }
    int k = 1;
    if (nc > 0 && rint_(100) >= 40) k = cand[rint_(nc)];
    int m = g / k;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 300; t++) {
            long long c = 2 + (long long)rint_(m - 2);
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    build_group(m, k, r);
}

static int in_S(int v, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[j] == v) return 1;
    return 0;
}

/* Number of vertices NOT within DD steps of src. */
static int bfs_unreached(int src) {
    if (vis_stamp > (1 << 30)) {
        memset(vis, 0, sizeof(vis));
        vis_stamp = 0;
    }
    vis_stamp++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = vis_stamp;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = que[head++];
            if (u < G) {
                const int *row = mt + (size_t)u * G;
                for (int l = 0; l < Dd; l++) {
                    int v = G + row[S[l]];
                    if (vis[v] != vis_stamp) {
                        vis[v] = vis_stamp;
                        que[tail++] = v;
                    }
                }
            } else {
                const int *row = mt + (size_t)(u - G) * G;
                for (int l = 0; l < Dd; l++) {
                    int v = row[sinv[l]];
                    if (vis[v] != vis_stamp) {
                        vis[v] = vis_stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
    }
    return 2 * G - tail;
}

static int cost_S(void) {
    for (int l = 0; l < Dd; l++) sinv[l] = iv[S[l]];
    return bfs_unreached(0) + bfs_unreached(G);
}

/* Simulated annealing over the generator set S (distinct elements of the
   group). Writes the best set to bestS and returns its cost. */
static int sa_run(int iters, double T0, double T1, int *bestS) {
    for (int l = 0; l < Dd; l++) {
        int v;
        do {
            v = rint_(G);
        } while (in_S(v, l));
        S[l] = v;
    }
    int cur = cost_S();
    int best = cur;
    memcpy(bestS, S, sizeof(int) * (size_t)Dd);
    for (int it = 0; it < iters && best > 0; it++) {
        if ((it & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int l = rint_(Dd);
        int old = S[l];
        int v = rint_(G);
        if (in_S(v, Dd)) continue;
        S[l] = v;
        int c2 = cost_S();
        int acc = 0;
        if (c2 <= cur) {
            acc = 1;
        } else {
            double u = (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
            if (u < exp(-(double)(c2 - cur) / T)) acc = 1;
        }
        if (acc) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)Dd);
            }
        } else {
            S[l] = old;
        }
    }
    return best;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int best_n = min_n;
    int have = 0;
    int bestG = 0, bM = 1, bK = 1, bR = 1;
    int bestS[MAXD];
    int tmpS[MAXD];
    int fails = 0;

    while (now_s() < deadline) {
        int gmin = best_n / 2 + 1;
        if (gmin < Dd) gmin = Dd;
        if (gmin > MAXG) break;
        int span = 2 + fails / 6;
        if (span > 80) span = 80;
        int g = gmin + rint_(span);
        if (g > MAXG) g = gmin;

        sample_group(g);
        int found = 0;
        for (int rep = 0; rep < REPS && !found && now_s() < deadline; rep++) {
            int c = sa_run(ITERS, 3.0, 0.2, tmpS);
            if (c == 0) {
                found = 1;
                memcpy(bestS, tmpS, sizeof(int) * (size_t)Dd);
            }
        }
        if (found) {
            have = 1;
            bestG = G;
            bM = GM;
            bK = GK;
            bR = GR;
            best_n = 2 * G;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    build_group(bM, bK, bR);
    int n = 2 * G;
    long m = (long)Dd * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int x = 0; x < G; x++) {
            printf("%d %d\n", x, G + mt[x * G + bestS[l]]);
        }
    }
    (void)bestG;
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer over semidirect
# product lifts, seeded with the best known order.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealing over bi-Cayley lifts on semidirect products, seeded with the
    # best known order as a lower bound.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
