import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (small, always valid, used as the safe fallback).
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
# C engine: simulated annealing over bi-Cayley / K-orbit lifts of a base
# multigraph, with a group window that climbs past the best order found.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]} for all g in the group. Each P[l] is a
# permutation, so every vertex has degree Dd. Cost = unreached pairs from the
# 2K representative vertices within DD steps + PEN * duplicate darts.
# Cost 0 is a valid graph (left translations make reps sufficient).
# Groups: Z_m x|_r Z_k with r^k = 1 mod m.
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
#define MAXN 3400
#define MAXG 1700
#define PEN 1000
#define ITERS 60000
#define T0 2.0
#define T1 0.1

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

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[64];
static double deadline = 0.0;

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int adj[MAXN * MAXD];
static int acnt[MAXN];
static int vis[MAXN];
static int qu[MAXN];
static int stamp = 0;

static void build_adj(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(acnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + acnt[a]++] = b;
                adj[b * Dd + acnt[b]++] = a;
            }
        }
    }
}

static long long eval(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    build_adj(c);
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
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
        raw += N - tail;
    }
    return raw + (long long)PEN * dup;
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

/* Simulated annealing at fixed group. Returns the best cost seen and stores
   the matching configuration in *best. */
static long long anneal(Cfg *c, Cfg *best) {
    long long cur = eval(c);
    long long bc = cur;
    *best = *c;
    for (long t = 0; t < ITERS && bc > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double frac = (double)t / (double)ITERS;
        double T = T0 * pow(T1 / T0, frac);
        int l = rint_(Dd);
        int i = rint_(c->K);
        int swapk = (c->K >= 2 && rint_(3) == 0);
        int old_s = 0, i2 = 0;
        if (swapk) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            int ns = rint_(GG);
            if (ns == old_s) continue;
            c->S[l][i] = ns;
        }
        long long nc = eval(c);
        long long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < bc) {
                bc = cur;
                *best = *c;
            }
        } else {
            if (swapk) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old_s;
            }
        }
    }
    return bc;
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
    Cfg bestcfg;
    memset(&bestcfg, 0, sizeof(bestcfg));
    int bM = 1, bK = 1, bR = 1;
    int fails = 0;
    Cfg cand, found;
    memset(&cand, 0, sizeof(cand));
    memset(&found, 0, sizeof(found));

    while (now_s() < deadline) {
        if (best_n >= MAXN) break;
        int K = rint_(100) < 60 ? 1 : (rint_(100) < 75 ? 2 : 3);
        long long maxG = MAXN / (2LL * K);
        if (maxG > MAXG) maxG = MAXG;
        long long g0 = (long long)best_n / (2LL * K) + 1;
        if (g0 > maxG) continue;

        long long span = g0 / 40 + 4 + (long long)(fails / 30) * (g0 / 60 + 1);
        if (span > g0 / 3 + 6) span = g0 / 3 + 6;
        long long G = g0 + (long long)rint_((int)span + 1);
        if (G > maxG) G = maxG;

        int k = KF[rint_((int)(sizeof(KF) / sizeof(KF[0])))];
        long long m = (G + k - 1) / k;
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
        set_group((int)m, k, r);
        if (GG > MAXG || 2 * K * GG > MAXN) {
            fails++;
            continue;
        }
        cand.K = K;
        cand.G = GG;
        random_cfg(&cand);
        long long res = anneal(&cand, &found);
        if (res == 0) {
            best_n = 2 * K * GG;
            bestcfg = found;
            bM = (int)m;
            bK = k;
            bR = r;
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
    set_group(bM, bK, bR);
    int K = bestcfg.K, G = bestcfg.G, N = 2 * K * G;
    printf("%d %ld\n", N, (long)Dd * K * G);
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
# Python glue: exact constructions first, then the annealing engine.
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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

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

    # Annealing over bi-Cayley / K-orbit lifts, climbing the group window
    # above the best order found so far.
    if 3 <= d <= 16 and D >= 3:
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
