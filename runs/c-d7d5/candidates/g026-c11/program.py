import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as safe fallbacks).
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
# C engine (new construction): simulated annealing over semidirect-product
# voltage lifts with K = 1..3 base vertices per side. Each dart layer is a
# permutation P[l] of the base vertices plus a voltage S[l][i] in the group.
# Cost = unreached (representative, vertex) pairs within DD steps plus a
# heavy penalty for duplicate darts. Cost 0 means a valid graph.
# Group orders are chosen just above the current best order and the search
# climbs; near-miss configurations are reheated with small perturbations.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXD 64
#define MAXK 4
#define MAXGAP 256
#define MAXG 6000
#define ITERS 30000
#define DUPW 200

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static int Dd = 3, DD = 3;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rfloat(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static double deadline = 0.0;

static int GM = 1, GK = 1, GG = 1;
static int gpow[MAXGAP];

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

/* Semidirect product Z_m x|_r Z_k, element (a,b) coded as a*k+b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
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

static int cap_n = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;

static void ensure(int N) {
    if (N <= cap_n) return;
    free(adj);
    free(cnt);
    free(vis);
    free(qu);
    cap_n = N;
    adj = malloc(sizeof(int) * (size_t)N * MAXD);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !cnt || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 0;
}

static long long evaluate(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    ensure(N);
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * MAXD + cnt[a]++] = b;
                adj[b * MAXD + cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * MAXD + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        unreached += (long long)(N - tail);
    }
    return unreached + (long long)DUPW * dup;
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

/* Simulated annealing with geometric cooling from T0 to T1. Writes the best
   configuration seen to *out and returns its cost. The group must be set. */
static long long anneal(const Cfg *start, int iters, double T0, double T1, Cfg *out) {
    Cfg c = *start;
    long long cost = evaluate(&c);
    long long bc = cost;
    *out = c;
    for (int t = 0; t < iters && bc > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(c.K);
        int kind = (c.K >= 2 && rint_(3) == 0);
        int i2 = 0, olds = 0;
        if (kind) {
            i2 = rint_(c.K - 1);
            if (i2 >= i) i2++;
            int tmp = c.P[l][i];
            c.P[l][i] = c.P[l][i2];
            c.P[l][i2] = tmp;
        } else {
            olds = c.S[l][i];
            c.S[l][i] = rint_(GG);
        }
        long long nc = evaluate(&c);
        long long delta = nc - cost;
        if (delta <= 0 || rfloat() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost < bc) {
                bc = cost;
                *out = c;
            }
        } else {
            if (kind) {
                int tmp = c.P[l][i];
                c.P[l][i] = c.P[l][i2];
                c.P[l][i2] = tmp;
            } else {
                c.S[l][i] = olds;
            }
        }
    }
    return bc;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18,
                         20, 21, 24, 28, 30, 32, 36, 40};

/* Pick a factorisation G = m * k (exact) and, for k > 1, an r with r^k = 1 mod m. */
static void choose_group(int G, int *om, int *ok, int *orr) {
    int cand[64];
    int nc = 0;
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    for (int t = 0; t < nk; t++) {
        int k = KF[t];
        if (k < MAXGAP && G % k == 0 && G / k >= 2 && nc < 64) cand[nc++] = k;
    }
    int k = nc ? cand[rint_(nc)] : 1;
    int m = G / k;
    if (m < 2) {
        m = G;
        k = 1;
    }
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
    *om = m;
    *ok = k;
    *orr = r;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    deadline = now_s() + tl;
    long long best_n = min_n;
    int have = 0;
    Cfg bestg;
    memset(&bestg, 0, sizeof(bestg));
    int bm = 1, bk = 1, br = 1;

    int have_near = 0;
    Cfg nearc;
    memset(&nearc, 0, sizeof(nearc));
    int nm = 1, nk = 1, nr = 1;
    long long near_cost = LLONG_MAX;

    while (now_s() < deadline) {
        Cfg c;
        memset(&c, 0, sizeof(c));
        Cfg cb;
        memset(&cb, 0, sizeof(cb));
        int M = 1, Kk = 1, R = 1;

        if (have_near && 2LL * nearc.K * nearc.G <= best_n) have_near = 0;

        if (have_near && rint_(100) < 50) {
            c = nearc;
            M = nm;
            Kk = nk;
            R = nr;
            set_group(M, Kk, R);
            for (int t = 0; t < 3; t++) {
                int l = rint_(Dd);
                int i = rint_(c.K);
                c.S[l][i] = rint_(GG);
            }
        } else {
            int K = (rint_(100) < 60) ? 1 : ((rint_(100) < 70) ? 2 : 3);
            long long G0 = best_n / (2LL * K) + 1;
            long long span = G0 / 40 + 2;
            long long G = G0 + (long long)rint_((int)span);
            if (G < 2) G = 2;
            if (G > MAXG) G = MAXG;
            choose_group((int)G, &M, &Kk, &R);
            set_group(M, Kk, R);
            c.K = K;
            c.G = (int)G;
            random_cfg(&c);
        }

        if (2LL * c.K * c.G <= best_n) continue;

        long long bc = anneal(&c, ITERS, 2.5, 0.15, &cb);

        if (bc == 0) {
            best_n = 2LL * cb.K * cb.G;
            bestg = cb;
            bm = M;
            bk = Kk;
            br = R;
            have = 1;
            have_near = 0;
            near_cost = LLONG_MAX;
        } else if (!have_near || bc < near_cost) {
            nearc = cb;
            nm = M;
            nk = Kk;
            nr = R;
            near_cost = bc;
            have_near = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bm, bk, br);
    int K = bestg.K, G = bestg.G;
    printf("%d %d\n", 2 * K * G, Dd * K * G);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestg.P[l][i], s = bestg.S[l][i];
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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # New construction: annealed semidirect-product voltage lifts.
    if 3 <= d <= 64 and D >= 3:
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
