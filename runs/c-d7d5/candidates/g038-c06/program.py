import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged from the parent): PG(2,q) for D = 3 and W(q) for D = 4.
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
# C engine (new in this version): simulated annealing over bi-Cayley lifts.
#
# Replaces the breakout local search of the parent. The state is a Z_m x| Z_k
# lift with K vertex classes per side. Layer l has a permutation P[l] of the
# classes and a voltage S[l][i] in the group, so every vertex has degree Dd.
# Cost = (unreached representative-vertex pairs within DD steps) + PEN * duplicate
# darts. Cost 0 is a valid graph. Moves: resample one voltage, or swap two
# classes within one layer. Metropolis acceptance with a geometric cooling
# schedule. Each attempt uses a fresh random state in a sampled group whose
# order is steered upward after every success.
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
#define MAXG 2200
#define MAXN (2 * MAXK * MAXG)
#define PEN 40
#define ITERS 30000L
#define T0 2.0
#define T1 0.12

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

static int ri(int n) { return (int)(rnd() % (uint64_t)n); }

static double rf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 7, DD = 5;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static int *mt = NULL;
static size_t mt_cap = 0;
static double deadline = 0.0;

static int adjv[MAXN * MAXD];
static int dcnt[MAXN];
static int vis[MAXN];
static int qu[MAXN];
static int stampc = 0;

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

/* Z_m x|_r Z_k, element a*k+b, product (a,b)(c,d) = (a + r^b c, b + d). */
static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
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
    for (int x = 0; x < GG; x++) {
        int xa = x / GK, xb = x % GK;
        for (int y = 0; y < GG; y++) {
            int ya = y / GK, yb = y % GK;
            long long t = ((long long)xa + (long long)gpow[xb] * (long long)ya) % GM;
            mt[x * GG + y] = (int)(t * GK + (xb + yb) % GK);
        }
    }
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20,
                         21, 24, 27, 28, 30, 32, 36, 40};

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[ri(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
            long long c = 2 + (long long)ri((int)(m - 2));
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

static void random_cfg(Cfg *c) {
    c->G = GG;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = ri(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = ri(GG);
    }
}

/* Fill adjv: A vertices are 0..K*G-1, B vertices K*G..2*K*G-1. Each vertex has
   exactly Dd neighbours because every layer P[l] is a permutation. */
static void build_adj(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    for (int v = 0; v < N; v++) dcnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + mt[g * GG + s];
                adjv[a * Dd + dcnt[a]++] = b;
                adjv[b * Dd + dcnt[b]++] = a;
            }
        }
    }
}

static long long eval(const Cfg *c, long long *raw_out, int *dup_out) {
    int K = c->K, G = c->G, N = 2 * K * G;
    build_adj(c);
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stampc++;
        int h = 0, t = 0;
        int src = r * G;
        vis[src] = stampc;
        qu[t++] = src;
        for (int lv = 0; lv < DD && t < N; lv++) {
            int end = t;
            while (h < end) {
                int u = qu[h++];
                const int *nb = adjv + u * Dd;
                for (int k = 0; k < Dd; k++) {
                    int v = nb[k];
                    if (vis[v] != stampc) {
                        vis[v] = stampc;
                        qu[t++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - t);
    }
    *raw_out = raw;
    *dup_out = dup;
    return raw + (long long)PEN * dup;
}

/* Simulated annealing from *cur. Returns 1 if a valid state (cost 0) is
   reached; then *cur holds that state. */
static int anneal(Cfg *cur, long iters) {
    long long raw;
    int dup;
    long long cost = eval(cur, &raw, &dup);
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && now_s() > deadline) break;
        double frac = (double)it / (double)iters;
        double T = T0 * pow(T1 / T0, frac);
        int typ = (cur->K >= 2 && ri(10) < 3);
        int l = ri(Dd);
        int i = ri(cur->K);
        int i2 = 0, old = 0;
        if (typ) {
            i2 = ri(cur->K - 1);
            if (i2 >= i) i2++;
            int t = cur->P[l][i];
            cur->P[l][i] = cur->P[l][i2];
            cur->P[l][i2] = t;
        } else {
            old = cur->S[l][i];
            int ns = ri(GG - 1);
            if (ns >= old) ns++;
            cur->S[l][i] = ns;
        }
        long long c2 = eval(cur, &raw, &dup);
        if (c2 <= cost || rf() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            if (typ) {
                int t = cur->P[l][i];
                cur->P[l][i] = cur->P[l][i2];
                cur->P[l][i2] = t;
            } else {
                cur->S[l][i] = old;
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long start_n = argc > 5 ? atoll(argv[5]) : 100;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    long long tgt = start_n < 4 ? 4 : start_n;
    long long best_n = 0;
    int have = 0;
    Cfg bestc;
    memset(&bestc, 0, sizeof(bestc));
    int bM = 1, bK = 1, bR = 1;
    int fails = 0;

    while (now_s() < deadline) {
        int K = ri(100) < 60 ? 1 : (ri(100) < 75 ? 2 : 3);
        long long G0 = tgt / (2 * K) + 1;
        long long span = G0 / 30 + 3 + (long long)(fails / 25) * (G0 / 100 + 1);
        if (span > G0 / 4 + 5) span = G0 / 4 + 5;
        long long Gt = G0 + (long long)ri((int)span + 1);
        int M, k, r;
        sample_group(Gt, &M, &k, &r);
        if ((long long)M * k > MAXG) continue;
        set_group(M, k, r);
        long long N = 2LL * K * GG;
        if (have && N <= best_n) {
            fails++;
            continue;
        }
        Cfg cur;
        memset(&cur, 0, sizeof(cur));
        cur.K = K;
        random_cfg(&cur);
        int ok = anneal(&cur, ITERS);
        if (ok) {
            best_n = N;
            bestc = cur;
            bM = M;
            bK = k;
            bR = r;
            have = 1;
            tgt = N + (N / 100 > 2 ? N / 100 : 2);
            fails = 0;
        } else {
            fails++;
            if (!have && fails % 30 == 0) {
                tgt = tgt * 95 / 100;
                if (tgt < 4) tgt = 4;
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    int K = bestc.K, G = bestc.G;
    int N = 2 * K * G;
    build_adj(&bestc);
    long m = (long)K * G * Dd;
    printf("%d %ld\n", N, m);
    for (int a = 0; a < K * G; a++)
        for (int t = 0; t < Dd; t++)
            printf("%d %d\n", a, adjv[a * Dd + t]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_end = start + max(2.0, min(0.85 * time_limit, time_limit - 6.0))

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

    if D >= 4 and time.monotonic() < budget_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Simulated annealing over bi-Cayley lifts. The start target is a quarter of
    # the Moore bound, and the C engine climbs from there after each success.
    if 3 <= d <= 16 and D >= 3:
        c_budget = budget_end - time.monotonic() - 1.0
        if c_budget >= 2.0:
            start_n = max(best_n + 2, lib.moore_bound(d, D) // 4)
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", start_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
