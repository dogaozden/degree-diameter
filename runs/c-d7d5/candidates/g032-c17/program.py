import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (valid fallbacks).
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
# C engine: a different search family from the parent. Each attempt picks a
# random group G of order about the target (a semidirect product Z_m x| Z_k,
# or a direct product when r = 1) and a base with K vertices per side. The
# graph is the lift with dart (l, i) joining A_{i,x} to B_{P[l][i], x*S[l][i]},
# where each layer l of P is a permutation, so the graph is Dd-regular and
# bipartite. Left multiplication by group elements is an automorphism, so the
# cost only needs BFS from the 2K representatives r*G. Simulated annealing on
# (unreached representative pairs + PEN * duplicate darts) searches voltages
# and permutations. The target order rises after each success.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 3
#define MAXGG 2600
#define MAXN (2 * MAXK * MAXGG)
#define PEN 1000
#define ITERS 120000
#define T0 4.0
#define T1 0.3

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double u01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int K = 1, GG = 1;
static int *mt = NULL;
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int adjv[MAXN * MAXD];
static int cnt[MAXN];
static int vis[MAXN];
static int qu[MAXN];
static int stampc = 0;

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};
#define NKF ((int)(sizeof(KF) / sizeof(KF[0])))

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

/* Group Z_m x|_r Z_k, element a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static void build_group(int m, int k, int r) {
    GG = m * k;
    int pw[64];
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        pw[b] = (int)p;
        p = (p * r) % m;
    }
    free(mt);
    mt = malloc(sizeof(int) * (size_t)GG * (size_t)GG);
    if (!mt) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    for (int x = 0; x < GG; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GG; y++) {
            int c = y / k, d = y % k;
            long long aa = ((long long)a + (long long)pw[b] * c) % m;
            mt[x * GG + y] = (int)aa * k + (b + d) % k;
        }
    }
}

static long long cost_now(void) {
    int N = 2 * K * GG;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (K + j) * GG + mt[g * GG + s];
                adjv[a * Dd + cnt[a]++] = b;
                adjv[b * Dd + cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stampc++;
        int head = 0, tail = 0;
        int src = r * GG;
        vis[src] = stampc;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adjv[u * Dd + t];
                    if (vis[v] != stampc) {
                        vis[v] = stampc;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    return raw + (long long)PEN * dup;
}

static void rand_state(void) {
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

/* Simulated annealing; returns 1 if a zero-cost (valid) state was reached,
   and leaves that state in P, S. */
static int anneal(long long iters, double dl) {
    long long cur = cost_now();
    double lr = log(T1 / T0);
    for (long long t = 0; t < iters; t++) {
        if (cur == 0) return 1;
        if ((t & 1023) == 0 && now_s() > dl) return 0;
        double T = T0 * exp(lr * (double)t / (double)iters);
        int l = rint_(Dd), i = rint_(K);
        if (K > 1 && rint_(3) == 0) {
            int i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
            long long nc = cost_now();
            if (nc <= cur || u01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            }
        } else {
            int old = S[l][i];
            S[l][i] = rint_(GG);
            long long nc = cost_now();
            if (nc <= cur || u01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                S[l][i] = old;
            }
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    Dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double dl = now_s() + tl;
    long long best_n = min_n;
    int have = 0;
    int bK = 1, bm = 1, bk = 1, br = 1;
    int bP[MAXD][MAXK], bS[MAXD][MAXK];
    memset(bP, 0, sizeof bP);
    memset(bS, 0, sizeof bS);
    int fails = 0;

    while (now_s() < dl) {
        int Kc = 1;
        if (rint_(100) >= 60) Kc = (rint_(100) < 75) ? 2 : 3;

        long long step = best_n / 150 + 2;
        long long span = step * (1 + fails / 6);
        if (span > best_n / 4 + 8) span = best_n / 4 + 8;
        long long Nt = best_n + 2 + step / 2 + (long long)rint_((int)span);
        long long G = (Nt + 2 * Kc - 1) / (2 * Kc);
        if (G < 2) G = 2;

        int kk = KF[rint_(NKF)];
        long long m = (G + kk - 1) / kk;
        if (m < 2) m = 2;
        if (m * kk > MAXGG) {
            fails++;
            continue;
        }
        int r = 1;
        if (kk > 1 && m > 2) {
            for (int t = 0; t < 200; t++) {
                long long c = 2 + (long long)rint_((int)(m - 2));
                if (gcdll(c, m) == 1 && powmod(c, kk, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
        }
        long long Nn = 2LL * Kc * m * kk;
        if (Nn <= best_n) continue;

        K = Kc;
        build_group((int)m, kk, r);
        rand_state();
        if (anneal(ITERS, dl)) {
            best_n = Nn;
            bK = K;
            bm = (int)m;
            bk = kk;
            br = r;
            memcpy(bP, P, sizeof P);
            memcpy(bS, S, sizeof S);
            have = 1;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    K = bK;
    build_group(bm, bk, br);
    int n = 2 * K * GG;
    long m_e = (long)Dd * K * GG;
    printf("%d %ld\n", n, m_e);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bP[l][i], s = bS[l][i];
            for (int g = 0; g < GG; g++) {
                printf("%d %d\n", i * GG + g, (K + j) * GG + mt[g * GG + s]);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search.
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

    # Group-lift annealing search, seeded with the best order found so far.
    if d >= 2 and D >= 2:
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
