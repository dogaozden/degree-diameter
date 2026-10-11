import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (small, always-valid fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
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


def _best_gq(d, qmax):
    """W(q) for the largest prime power q with q + 1 <= d and q <= qmax."""
    for q in range(min(d - 1, qmax), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-group lifts.
#
# Group G = Z_m x|_r Z_k (order G = m*k), K base vertices per side.
# A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart slot l and base vertex i give
# edges A_{i,g} -- B_{P[l][i], g*S[l][i]} for all g. P[l] is a permutation of
# 0..K-1, so every vertex has degree exactly Dd. Left translations are
# automorphisms, so only the K A-representatives and K B-representatives need
# BFS. Cost = unreached (rep, vertex) pairs within DD steps + PEN * duplicate
# darts. Cost 0 gives a valid graph.
# Search: annealing with geometric cooling, restarts, and a group order
# window that starts just above the best known order.
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
#define MAXN 8192
#define MAXG 4096
#define PEN 500
#define RUN_ITERS 120000L
#define T0 8.0
#define T1 0.3

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} State;

static int Dd = 3, DD = 3;
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

static int GM = 1, GK = 1, GG = 1, GR = 1;
static long long gpow[64];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    GR = r;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
}

/* (a,b)*(c,d) = (a + r^b c, b + d), coded as a*k + b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
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

/* Random group of order G: pick a divisor k <= 40 (k <= G/2), m = G/k. */
static void pick_group(int G, int *om, int *ok, int *orr) {
    int divs[64];
    int nd = 0;
    for (int k = 1; k <= 40 && 2 * k <= G; k++)
        if (G % k == 0) divs[nd++] = k;
    int k = divs[rint_(nd)];
    int m = G / k;
    int r = 1;
    if (k > 1 && m > 2) {
        if (k == 2 && rint_(2) == 0) {
            r = m - 1;
        } else {
            for (int t = 0; t < 200; t++) {
                int c = 2 + rint_(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }
    }
    *om = m;
    *ok = k;
    *orr = r;
}

static int adj[MAXN * MAXD];
static int deg[MAXN];
static int vis[MAXN];
static int qbuf[MAXN];
static int stamp_ = 0;

static long long evalState(const State *s, int *dupout, long long *rawout) {
    int K = s->K, G = GG, N = 2 * K * G;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = s->P[l][i], sv = s->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, sv);
                adj[a * Dd + deg[a]++] = b;
                adj[b * Dd + deg[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (s->P[l1][i] == s->P[l2][i] && s->S[l1][i] == s->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp_++;
        int head = 0, tail = 0;
        vis[src] = stamp_;
        qbuf[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qbuf[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp_) {
                        vis[v] = stamp_;
                        qbuf[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    *dupout = dup;
    *rawout = raw;
    return raw + (long long)PEN * dup;
}

static void randomState(State *s, int K) {
    s->K = K;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) s->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = s->P[l][i];
            s->P[l][i] = s->P[l][j];
            s->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) s->S[l][i] = rint_(GG);
    }
}

/* Simulated annealing on the current group. Returns 1 and leaves *s valid
   if cost 0 is reached; returns 0 on iteration or time exhaustion. */
static int anneal(State *s, long iters, double dl) {
    int dup = 0;
    long long raw = 0;
    long long cur = evalState(s, &dup, &raw);
    if (cur == 0) return 1;
    double ratio = T1 / T0;
    for (long it = 0; it < iters; it++) {
        if ((it & 255) == 0 && now_s() > dl) return 0;
        double temp = T0 * pow(ratio, (double)it / (double)iters);
        int l = rint_(Dd);
        int i = rint_(s->K);
        int swapmove = (s->K >= 2 && rint_(3) == 0);
        int i2 = 0, old = 0, tmp = 0;
        if (swapmove) {
            i2 = rint_(s->K - 1);
            if (i2 >= i) i2++;
            tmp = s->P[l][i];
            s->P[l][i] = s->P[l][i2];
            s->P[l][i2] = tmp;
        } else {
            old = s->S[l][i];
            s->S[l][i] = rint_(GG);
        }
        long long nc = evalState(s, &dup, &raw);
        long long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            if (swapmove) {
                tmp = s->P[l][i];
                s->P[l][i] = s->P[l][i2];
                s->P[l][i2] = tmp;
            } else {
                s->S[l][i] = old;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long min_n = argc > 5 ? atoll(argv[5]) : 0LL;

    if (Dd < 3 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    double t0 = now_s();
    double dl = t0 + tl;

    long long best_n = min_n;
    int have = 0;
    State best;
    memset(&best, 0, sizeof(best));
    int bM = 1, bk = 1, bR = 1;
    int fails = 0;

    while (now_s() < dl) {
        int K = (rint_(4) == 0) ? 2 : 1;
        long long lo = best_n / (2LL * K) + 1;
        int span = 3 + 2 * fails;
        if (span > 60) span = 60;
        long long G = lo + rint_(span);
        if (G < 4 || 2LL * K * G > MAXN || G > MAXG) {
            fails++;
            continue;
        }
        int m, k, r;
        pick_group((int)G, &m, &k, &r);
        set_group(m, k, r);
        State s;
        randomState(&s, K);
        if (anneal(&s, RUN_ITERS, dl)) {
            best_n = 2LL * K * GG;
            best = s;
            bM = m;
            bk = k;
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
    set_group(bM, bk, bR);
    int K = best.K, G = GG;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best.P[l][i], sv = best.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, sv));
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

    def consider(cand):
        nonlocal best, best_n
        if cand is None:
            return
        n, e = cand
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        consider(_best_pg(d))
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if D >= 4 and time.monotonic() < deadline:
        qmax = 9 if D == 4 else 7
        consider(_best_gq(d, qmax))
        if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
            return best

    # Annealed group-lift search in C, seeded with the best known order.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 3.0)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
