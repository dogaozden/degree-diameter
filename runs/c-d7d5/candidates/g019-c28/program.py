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
# C engine: simulated annealing over bi-Cayley lifts.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation, so the
# graph is Dd-regular. Left translation by x is an automorphism, so the
# distances from the 2K representatives A_{i,1}, B_{j,1} determine validity.
# Cost = unreached (representative, vertex) pairs within DD steps
# + PEN * duplicate darts. Cost 0 means valid.
#
# Search: simulated annealing (not breakout). Group orders are sampled just
# above an adaptive target that starts at a hint and descends on repeated
# failure, and rises to best+1 after each success.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXK 3
#define MAXN 8192
#define MT_LIMIT 2500
#define PEN 20
#define ITERS 30000
#define FAIL_LIMIT 6

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

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

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[64];
static int *gmt = NULL;
static int gmt_on = 0;
static double deadline = 0.0;

static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
    gmt_on = 0;
    if (GG <= MT_LIMIT) {
        if (!gmt) {
            gmt = malloc(sizeof(int) * (size_t)MT_LIMIT * (size_t)MT_LIMIT);
            if (!gmt) {
                fprintf(stderr, "out of memory\n");
                exit(1);
            }
        }
        for (int x = 0; x < GG; x++)
            for (int y = 0; y < GG; y++)
                gmt[(size_t)x * (size_t)GG + (size_t)y] = gmul_raw(x, y);
        gmt_on = 1;
    }
}

static inline int gmul(int x, int y) {
    return gmt_on ? gmt[(size_t)x * (size_t)GG + (size_t)y] : gmul_raw(x, y);
}

static int adj[MAXN * MAXD];
static int ccnt[MAXN], vs[MAXN], qq[MAXN];
static int stampv = 0;

/* Returns cost = raw unreached pairs + PEN * duplicates; raw via *raw_out. */
static int evalc(const Cfg *c, int *raw_out) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(ccnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + ccnt[a]++] = b;
                adj[b * Dd + ccnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    int raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stampv++;
        int src = r * G;
        int head = 0, tail = 0;
        vs[src] = stampv;
        qq[tail++] = src;
        for (int lev = 0; lev < DD; lev++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qq[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vs[v] != stampv) {
                        vs[v] = stampv;
                        qq[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
    }
    *raw_out = raw;
    return raw + PEN * dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(GG);
    }
}

/* Simulated annealing; leaves best state in *best and returns its cost. */
static int anneal(Cfg *c, int iters, Cfg *best) {
    int raw = 0;
    int cur = evalc(c, &raw);
    int bestc = cur;
    *best = *c;
    double T0 = 1.5, T1 = 0.1;
    double T = T0;
    double fac = pow(T1 / T0, 1.0 / (double)iters);
    int K = c->K;
    for (int t = 0; t < iters && bestc > 0; t++) {
        if ((t & 63) == 0 && now_s() > deadline) break;
        int l = rint_(Dd);
        int i = rint_(K);
        int kind = (K >= 2 && rint_(3) == 0);
        int i2 = 0, old = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        int nc = evalc(c, &raw);
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                *best = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old;
            }
        }
        T *= fac;
    }
    return bestc;
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

/* Group of order m*k: semidirect Z_m x| Z_k with r^k = 1 mod m (r = 1 is direct). */
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
    long long best_n = argc > 5 ? atoll(argv[5]) : 0;
    long long hint = argc > 6 ? atoll(argv[6]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    deadline = now_s() + tl;
    long long target_n = hint > best_n + 1 ? hint : best_n + 1;
    int have = 0, fails = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg bestcfg;
    memset(&bestcfg, 0, sizeof(bestcfg));

    while (now_s() < deadline) {
        int K = (rint_(100) < 70) ? 1 : 2;
        long long g0 = (target_n + 2 * K - 1) / (2 * K);
        long long span = g0 / 50 + 3;
        long long g = g0 + (long long)rint_((int)span);
        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        if ((long long)M * Kk * 2 * K > MAXN) continue;
        set_group(M, Kk, R);
        int N = 2 * K * GG;
        if (N <= best_n) continue;

        Cfg cur, tb;
        memset(&cur, 0, sizeof(cur));
        cur.K = K;
        cur.G = GG;
        random_cfg(&cur);
        int bc = anneal(&cur, ITERS, &tb);
        if (bc == 0) {
            best_n = N;
            bestcfg = tb;
            bM = M;
            bK = Kk;
            bR = R;
            have = 1;
            target_n = best_n + 1;
            fails = 0;
        } else if (++fails >= FAIL_LIMIT) {
            fails = 0;
            long long lower = target_n - target_n / 100 - 1;
            if (lower < best_n + 1) lower = best_n + 1;
            target_n = lower;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    int K = bestcfg.K, G = bestcfg.G;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestcfg.P[l][i], s = bestcfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer.
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

    # Annealing search in C: target orders start at a hint near the best known
    # density and adapt downward on failure.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            hint = max(best_n + 1, int(0.35 * lib.moore_bound(d, D)))
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, seed, f"{c_budget:.2f}", best_n, hint],
                                timeout=time_limit - 2.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
