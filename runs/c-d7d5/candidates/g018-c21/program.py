import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged): projective planes and generalized quadrangles.
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
# C engine: simulated annealing over permutation-based lifts of K+K base
# vertices with voltages in a finite group. The group is drawn from a wider
# family (cyclic, direct products Z_m x Z_k, and semidirect products
# Z_m x| Z_k), with K = 1, 2, 3 base vertices per side. Each dart layer is a
# permutation, so the lift is d-regular. Cost = unreached (representative,
# vertex) pairs within DD steps + PEN * duplicate darts. Cost 0 is valid.
# Representatives are the 2K base vertices at identity, which suffices
# because left multiplication by the group is an automorphism.
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
#define MAXV (2 * MAXK * MAXG)
#define PEN 1000
#define ITERS 120000

static int Dd = 3, DD = 3;
static double deadline = 0.0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int K = 1, G = 1;
static int *mt = NULL;
static long long gpw[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int adj[MAXV * MAXD], cnt[MAXV], vis[MAXV], que[MAXV];
static int stamp = 0;
static int outU[MAXD * MAXK * MAXG], outV[MAXD * MAXK * MAXG];
static int outM = 0, outN = 0;

/* Group of order m*k: elements (a,b) coded a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static void set_group(int m, int k, int r) {
    G = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpw[b] = p;
        p = (p * r) % m;
    }
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, d = y % k;
            long long t = ((long long)a + gpw[b] * (long long)c) % m;
            mt[x * G + y] = (int)t * k + (b + d) % k;
        }
    }
}

static long long pw_mod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24};

static void sample_group(int target, int *om, int *ok, int *orr) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    int m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2 && rint_(3) != 0) {
        for (int t = 0; t < 300; t++) {
            int c = 2 + rint_(m - 2);
            if (gcd_i(c, m) == 1 && pw_mod(c, k, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    *om = m;
    *ok = k;
    *orr = r;
}

static long dupcount(void) {
    long d = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) d++;
    return d;
}

static long eval(void) {
    int N = 2 * K * G;
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + mt[g * G + s];
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int src = r * G;
        int head = 0, tail = 0;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = que[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached + (long)PEN * dupcount();
}

static void random_init(void) {
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

/* Simulated annealing; leaves P,S at the best state seen and returns its cost. */
static long anneal(long iters, double T0, double T1) {
    random_init();
    long cur = eval();
    long best = cur;
    static int bP[MAXD][MAXK], bS[MAXD][MAXK];
    memcpy(bP, P, sizeof P);
    memcpy(bS, S, sizeof S);
    for (long t = 0; t < iters && cur > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double frac = (double)t / (double)iters;
        double T = T0 * pow(T1 / T0, frac);
        int l = rint_(Dd), i = rint_(K);
        int kind = (K >= 2 && rint_(4) == 0);
        int oldS = 0, i2 = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
        } else {
            oldS = S[l][i];
            S[l][i] = rint_(G);
        }
        long nc = eval();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(bP, P, sizeof P);
                memcpy(bS, S, sizeof S);
            }
        } else {
            if (kind) {
                int tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                S[l][i] = oldS;
            }
        }
    }
    memcpy(P, bP, sizeof P);
    memcpy(S, bS, sizeof S);
    return best;
}

static void save_solution(void) {
    int m = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                outU[m] = i * G + g;
                outV[m] = (K + j) * G + mt[g * G + s];
                m++;
            }
        }
    }
    outM = m;
    outN = 2 * K * G;
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
    mt = malloc(sizeof(int) * (size_t)MAXG * (size_t)MAXG);
    if (!mt) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have = 0;

    while (now_s() < deadline) {
        int roll = rint_(100);
        int Kc = roll < 60 ? 1 : (roll < 90 ? 2 : 3);
        int g0 = best_n / (2 * Kc) + 1;
        int span = g0 / 30 + 4;
        int target = g0 + rint_(span);
        int m, k, r;
        sample_group(target, &m, &k, &r);
        if ((long)m * k > MAXG) continue;
        if (2 * Kc * m * k <= best_n) continue;
        K = Kc;
        set_group(m, k, r);
        long c = anneal(ITERS, 1.5, 0.05);
        if (c == 0) {
            save_solution();
            best_n = outN;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", outN, outM);
    for (int e = 0; e < outM; e++) printf("%d %d\n", outU[e], outV[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search, with fallbacks.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

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

    # Annealed lift search over a wider family of groups, seeded with the best known order.
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
