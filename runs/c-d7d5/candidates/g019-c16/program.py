import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged from the parent): projective plane and W(q).
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
# C engine: simulated annealing over semidirect-product voltage lifts.
#
# This is a different search from the breakout engine. Each attempt draws a
# base size K in {1,2,3,4,6} and a semidirect group Z_m x| Z_k of order about
# target/(2K). The state is d darts per base index: a permutation P[l] of the
# K right fibres and a group element S[l][i]. Cost is the number of
# (fibre representative, vertex) pairs at distance > DD, plus a penalty per
# duplicate dart. Left multiplication is an automorphism of the lift, so BFS
# from one representative per fibre is enough. Cost 0 is a valid graph.
# Moves are accepted by Metropolis rule under a geometric cooling schedule.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <limits.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define MAXN 32768
#define MT_LIMIT 2600
#define PEN 3
#define ATTEMPT_ITERS 150000L

static int Dd = 3, DD = 3;
static int K = 1, G = 1;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static int *mt = NULL;
static size_t mt_cap = 0;
static int mt_on = 0;

static int P[MAXD][MAXK], S[MAXD][MAXK];
static int bestP[MAXD][MAXK], bestS[MAXD][MAXK];

static int adj[MAXN * MAXD];
static int cnt[MAXN];
static int vis[MAXN];
static int qu[MAXN];
static int stamp = 0;

static double deadline = 0.0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    mt_on = 0;
    if (GG <= MT_LIMIT) {
        size_t need = (size_t)GG * (size_t)GG;
        if (need > mt_cap) {
            free(mt);
            mt = malloc(sizeof(int) * need);
            if (!mt) {
                fprintf(stderr, "out of memory\n");
                exit(1);
            }
            mt_cap = need;
        }
        for (int x = 0; x < GG; x++)
            for (int y = 0; y < GG; y++)
                mt[(size_t)x * (size_t)GG + (size_t)y] = gmul_raw(x, y);
        mt_on = 1;
    }
}

static inline int gmul(int x, int y) {
    if (mt_on) return mt[(size_t)x * (size_t)GG + (size_t)y];
    return gmul_raw(x, y);
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

/* Semidirect group Z_m x| Z_k with r^k = 1 mod m. Falls back to direct product (r = 1). */
static void sample_group(long long target, int k, int *oM, int *oR) {
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 300; t++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = (int)m;
    *oR = r;
}

/* Full cost evaluation of the current state (P, S, K, G). */
static long long cost_full(void) {
    int N = 2 * K * G;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    if (stamp >= INT_MAX - 4) {
        memset(vis, 0, sizeof(vis));
        stamp = 0;
    }
    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int head = 0, tail = 0;
        int src = r * G;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    return raw + (long long)PEN * dup;
}

static void random_state(void) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(GG);
    }
}

/* Metropolis annealing from the current state. Leaves the best state found in P, S.
   Returns its cost. */
static long long anneal(long iters, double T0, double T1) {
    long long cur = cost_full();
    long long best = cur;
    memcpy(bestP, P, sizeof P);
    memcpy(bestS, S, sizeof S);
    for (long t = 0; t < iters && cur > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(K);
        int kind = (K >= 2 && rint_(3) == 0);
        int i2 = 0, old = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
        } else {
            old = S[l][i];
            S[l][i] = rint_(GG);
        }
        long long nc = cost_full();
        long long dl = nc - cur;
        if (dl <= 0 || urand() < exp(-(double)dl / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(bestP, P, sizeof P);
                memcpy(bestS, S, sizeof S);
            }
        } else {
            if (kind) {
                int tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                S[l][i] = old;
            }
        }
    }
    memcpy(P, bestP, sizeof P);
    memcpy(S, bestS, sizeof S);
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
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have = 0;
    int recK = 1, recM = 1, recR = 1, recGK = 1;
    static int recP[MAXD][MAXK], recS[MAXD][MAXK];

    const int Ks[] = {1, 1, 1, 2, 2, 3, 4, 6};
    const int GKs[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};

    while (now_s() < deadline) {
        int kk = Ks[rint_(8)];
        int gk = GKs[rint_(16)];
        long long g0 = (long long)best_n / (2LL * kk) + 1;
        long long g = g0 + (long long)rint_((int)(g0 / 40 + 4));
        int M, R;
        sample_group(g, gk, &M, &R);
        set_group(M, gk, R);
        if (GG > MT_LIMIT) continue;
        long long N = 2LL * kk * GG;
        if (N <= best_n || N > MAXN) continue;

        K = kk;
        G = GG;
        random_state();
        long long c = anneal(ATTEMPT_ITERS, 1.0, 0.05);
        if (c == 0) {
            best_n = (int)N;
            memcpy(recP, P, sizeof P);
            memcpy(recS, S, sizeof S);
            recK = kk;
            recM = M;
            recR = R;
            recGK = gk;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(recM, recGK, recR);
    K = recK;
    G = GG;
    memcpy(P, recP, sizeof P);
    memcpy(S, recS, sizeof S);
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions as the safe fallback, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 6.0))

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

    # Annealed semidirect-lift search in C, seeded with the best known order.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 2.0
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
