import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as cheap, certain fallbacks for D = 3 and D = 4).
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
# C engine: simulated annealing over bi-Cayley / small-base group lifts.
#
# This replaces the breakout search with a different strategy:
#   * Group sampling: Z_m x|_r Z_k with K base vertices per side (K = 1..3).
#   * Cost = unreached (representative, vertex) pairs within DD steps
#     + PEN * duplicate darts. The group acts by left multiplication, so only
#     2K representatives need BFS. Cost 0 means diameter <= DD.
#   * Annealing with a geometric temperature schedule per run; a run that
#     reaches cost 0 raises the order floor, otherwise a fresh group is drawn.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Every vertex has degree exactly Dd.
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
#define NMAX 20000
#define PEN 20
#define RUN 40000
#define T0 3.0
#define T1 0.15

static uint64_t rs = 88172645463325252ULL;

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

static int Dd = 3, DD = 3;
static int K = 1, GM = 1, GK = 1, GG = 1;
static int gpow[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int adj[NMAX * MAXD];
static int cnt[NMAX], vis[NMAX], qu[NMAX];
static int stamp = 0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

/* Semidirect product (a,b)*(c,d) = (a + r^b c, b + d), coded as a*k + b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static long long evaluate(void) {
    int N = 2 * K * GG;
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (K + j) * GG + gmul(g, s);
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int src = r * GG;
        int h = 0, t = 0;
        vis[src] = stamp;
        qu[t++] = src;
        for (int lvl = 0; lvl < DD && h < t; lvl++) {
            int end = t;
            while (h < end) {
                int u = qu[h++];
                int *au = adj + u * Dd;
                for (int kk = 0; kk < Dd; kk++) {
                    int v = au[kk];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[t++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - t);
    }
    return raw + (long long)PEN * dup;
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
        for (int i = 0; i < K; i++) S[l][i] = rint_(GG);
    }
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
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

    double deadline = now_s() + tl;
    int best_n = min_n;
    int have = 0;
    int bKc = 1, bM = 1, bGk = 1, bR = 1;
    static int bP[MAXD][MAXK], bS[MAXD][MAXK];
    int fails = 0;

    while (now_s() < deadline) {
        int r0 = rint_(100);
        K = (r0 < 50) ? 1 : ((r0 < 85) ? 2 : 3);
        long long lo = (long long)best_n / (2 * K) + 1;
        long long span = lo / 40 + 3 + (long long)(fails / 8) * (lo / 80 + 1);
        if (span > lo / 3 + 3) span = lo / 3 + 3;
        long long target = lo + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(target, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (2 * K * GG > NMAX) continue;
        if (2 * K * GG <= best_n) continue;

        random_cfg();
        long long cur = evaluate();
        int found = (cur == 0);

        for (int it = 0; it < RUN && !found; it++) {
            if ((it & 255) == 0 && now_s() > deadline) break;
            double T = T0 * pow(T1 / T0, (double)it / (double)RUN);
            int l = rint_(Dd);
            int i = rint_(K);
            if (K >= 2 && rint_(4) == 0) {
                int i2 = rint_(K - 1);
                if (i2 >= i) i2++;
                int t = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = t;
                long long nc = evaluate();
                if (nc <= cur || urand() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = P[l][i];
                    P[l][i] = P[l][i2];
                    P[l][i2] = t;
                }
            } else {
                int old = S[l][i];
                int nv = rint_(GG);
                if (nv == old) continue;
                S[l][i] = nv;
                long long nc = evaluate();
                if (nc <= cur || urand() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    S[l][i] = old;
                }
            }
            if (cur == 0) found = 1;
        }

        if (found) {
            best_n = 2 * K * GG;
            bKc = K;
            bM = M;
            bGk = Kk;
            bR = R;
            memcpy(bP, P, sizeof(P));
            memcpy(bS, S, sizeof(S));
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
    K = bKc;
    set_group(bM, bGk, bR);
    memcpy(P, bP, sizeof(P));
    memcpy(S, bS, sizeof(S));
    int G = GG;
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
# Python glue: exact constructions for D = 3, 4, then the annealing lift search.
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

    # Exact constructions for small diameters.
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

    # Annealing search over group lifts. The starting floor is a fraction of the
    # Moore bound; if that yields nothing, a second run starts from zero.
    if d >= 2 and D >= 3:
        moore = lib.moore_bound(d, D)
        hint = max(best_n, int(0.25 * moore))
        c_budget = deadline - time.monotonic() - 2.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", hint],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        if best_n <= hint:
            rest = deadline - time.monotonic() - 2.0
            if rest >= 3.0:
                try:
                    out = lib.run_c(C_SOURCE, [d, D, seed + 1, f"{rest:.2f}", best_n],
                                    timeout=time_limit - 3.0)
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
