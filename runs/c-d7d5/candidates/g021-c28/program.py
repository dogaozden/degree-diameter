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
# C engine: simulated annealing over semidirect-product bi-lifts.
#
# Vertices: A_{i,g} = i*G+g (i < K), B_{j,h} = (K+j)*G+h.
# Dart (l, i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}, where each P[l] is a
# permutation of 0..K-1 (so the graph is Dd-regular and bipartite).
# Group: Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a+r^b c, b+d).
# Cost = unreached (rep, vertex) pairs within DD steps + PEN * duplicate darts.
# Cost 0 means a valid graph. Failed attempts warm-restart from the near-miss.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 4
#define MAXG 2000
#define MAXN (2 * MAXK * MAXG)
#define PEN 40
#define ITERS 150000L

static int Dd = 3, DD = 3;
static int K = 1, G = 1, GM = 1, GK = 1, R = 1;
static int gpow[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int bestP[MAXD][MAXK], bestS[MAXD][MAXK];
static int snapP[MAXD][MAXK], snapS[MAXD][MAXK];
static int nearP[MAXD][MAXK], nearS[MAXD][MAXK];
static int adj[MAXN * MAXD];
static int cntd[MAXN];
static long vis[MAXN];
static int qu[MAXN];
static long stampv = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    G = m * k;
    R = r;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, d = y - c * GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    int bd = b + d;
    if (bd >= GK) bd -= GK;
    return (int)t * GK + bd;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20, 24, 28, 30, 32, 36, 40};

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
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
    *oK = k;
    *oR = r;
}

static void random_cfg(void) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(G);
    }
}

/* Unreached (rep, vertex) pairs within DD steps, plus PEN per duplicate dart. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int v = 0; v < N; v++) cntd[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + l] = b;
                adj[b * Dd + cntd[b]++] = a;
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    long long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        stampv++;
        int src = r * G;
        int head = 0, tail = 0;
        vis[src] = stampv;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                const int *au = adj + u * Dd;
                for (int t = 0; t < Dd; t++) {
                    int v = au[t];
                    if (vis[v] != stampv) {
                        vis[v] = stampv;
                        qu[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached + (long long)PEN * dup;
}

static const int KPICK[] = {1, 2, 3, 4};

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long best_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int have = 0;
    int bestK = 1, bGM = 1, bGK = 1, bR = 1;
    int have_near = 0;
    long long near_cost = 0;
    int nK = 1, nGM = 1, nGK = 1, nR = 1;
    long long fails = 0;

    while (now_s() < deadline) {
        int warm = have_near && (rint_(100) < 50);
        if (warm) {
            K = nK;
            set_group(nGM, nGK, nR);
            memcpy(P, nearP, sizeof P);
            memcpy(S, nearS, sizeof S);
            int pert = 2 + rint_(4);
            for (int t = 0; t < pert; t++) {
                int l = rint_(Dd), i = rint_(K);
                if (K >= 2 && rint_(2)) {
                    int i2 = rint_(K - 1);
                    if (i2 >= i) i2++;
                    int tmp = P[l][i];
                    P[l][i] = P[l][i2];
                    P[l][i2] = tmp;
                } else {
                    S[l][i] = rint_(G);
                }
            }
        } else {
            int rk = rint_(100);
            K = rk < 50 ? KPICK[0] : rk < 80 ? KPICK[1] : rk < 92 ? KPICK[2] : KPICK[3];
            long long gmin = best_n / (2LL * K) + 1;
            long long span = gmin / 40 + 3 + fails / 20;
            if (span > gmin / 8 + 3) span = gmin / 8 + 3;
            long long target = gmin + (long long)rint_((int)span);
            int m, k, r;
            sample_group(target, &m, &k, &r);
            set_group(m, k, r);
            if (G > MAXG) continue;
            random_cfg();
        }

        int N = 2 * K * G;
        if ((long long)N <= best_n || N > MAXN) continue;

        double T0 = warm ? 1.0 : 2.5;
        double T1 = 0.12;
        long long c = eval_cost();
        long long abest = c;
        memcpy(snapP, P, sizeof P);
        memcpy(snapS, S, sizeof S);
        int success = (c == 0);

        for (long it = 0; it < ITERS && !success; it++) {
            if ((it & 511) == 0 && now_s() > deadline) break;
            double T = T0 * pow(T1 / T0, (double)it / (double)ITERS);
            int l = rint_(Dd), i = rint_(K);
            int swp = (K >= 2 && rint_(3) == 0);
            int i2 = 0, olds = 0;
            if (swp) {
                i2 = rint_(K - 1);
                if (i2 >= i) i2++;
                int tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                olds = S[l][i];
                S[l][i] = rint_(G);
            }
            long long c2 = eval_cost();
            int acc = (c2 <= c) || (urand() < exp(-(double)(c2 - c) / T));
            if (acc) {
                c = c2;
                if (c < abest) {
                    abest = c;
                    memcpy(snapP, P, sizeof P);
                    memcpy(snapS, S, sizeof S);
                }
                if (c == 0) success = 1;
            } else {
                if (swp) {
                    int tmp = P[l][i];
                    P[l][i] = P[l][i2];
                    P[l][i2] = tmp;
                } else {
                    S[l][i] = olds;
                }
            }
        }

        if (success) {
            best_n = N;
            have = 1;
            bestK = K;
            bGM = GM;
            bGK = GK;
            bR = R;
            memcpy(bestP, P, sizeof P);
            memcpy(bestS, S, sizeof S);
            have_near = 0;
            fails = 0;
        } else {
            fails++;
            if (!have_near || abest < near_cost) {
                have_near = 1;
                near_cost = abest;
                nK = K;
                nGM = GM;
                nGK = GK;
                nR = R;
                memcpy(nearP, snapP, sizeof snapP);
                memcpy(nearS, snapS, sizeof snapS);
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    K = bestK;
    set_group(bGM, bGK, bR);
    int N = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestP[l][i], s = bestS[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search, with a fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.90 * time_limit, time_limit - 5.0))

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

    # Simulated annealing over semidirect-product lifts in C, seeded with the best order so far.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
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
