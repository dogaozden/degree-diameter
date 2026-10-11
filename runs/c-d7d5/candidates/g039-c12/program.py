import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (cheap, always valid when they pass lib.is_valid).
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
# C engine: a different search from the parent. Simulated annealing over
# bi-Cayley voltage assignments (K left blocks, K right blocks, group Z_m x| Z_k)
# with a Metropolis acceptance rule, instead of breakout clause weighting.
# Four base sides (K = 1..4) are sampled, so the order granularity is 2K*G.
#
# Vertices: left block i at i*G+g, right block j at (K+j)*G+h.
# Dart (l, i) joins A_{i,g} to B_{P[l][i], g*S[l][i]} for all g.
# Each P[l] is a permutation, so every vertex has degree exactly Dd.
# Energy = unreached pairs from the 2K block representatives within DD steps
# + PEN * duplicate darts. Energy 0 means a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 16
#define MAXK 4
#define PEN 1000

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

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;

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

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cap = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;

static void ensure(int N) {
    if (N <= cap) return;
    free(adj);
    free(cnt);
    free(vis);
    free(qu);
    cap = N;
    adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !cnt || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

/* Energy = unreached (rep, vertex) pairs + PEN * duplicate darts. */
static int evalc(const Cfg *c, int *dupout) {
    int K = c->K, G = c->G, N = 2 * K * G;
    ensure(N);
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
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
    *dupout = dup;
    return (int)(raw + (long long)PEN * dup);
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

static void swapP(Cfg *c, int l, int i, int i2) {
    int t = c->P[l][i];
    c->P[l][i] = c->P[l][i2];
    c->P[l][i2] = t;
}

/* Simulated annealing with geometric cooling. Returns the best energy seen
   and stores the best state in *out. Stops early at energy 0. */
static int anneal(Cfg *c, long iters, Cfg *out) {
    int dup;
    int cc = evalc(c, &dup);
    int best = cc;
    Cfg bc = *c;
    double lt0 = log(3.0), lt1 = log(0.05);
    for (long t = 0; t < iters && cc != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = exp(lt0 + (lt1 - lt0) * (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(3) == 0);
        int i2 = 0, os = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            swapP(c, l, i, i2);
        } else {
            os = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        int nc = evalc(c, &dup);
        int delta = nc - cc;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cc = nc;
            if (cc < best) {
                best = cc;
                bc = *c;
            }
        } else {
            if (kind) swapP(c, l, i, i2);
            else c->S[l][i] = os;
        }
    }
    *out = bc;
    return best;
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

/* Group of order m*k (at least target) as Z_m x|_r Z_k. */
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
    for (int w = 0; w < 6; w++) rnd();

    deadline = now_s() + tl;
    int best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));
    int fails = 0;

    while (now_s() < deadline) {
        int K = 1 + rint_(4);                     /* base sides 1..4 */
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 30 + 3 + (long long)(fails / 50) * (g0 / 40 + 1);
        if (span > g0 / 3 + 3) span = g0 / 3 + 3;
        long long g = g0 + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > 4000) continue;
        int N = 2 * K * GG;
        if (N <= best_n) {
            fails++;
            continue;
        }

        Cfg c;
        memset(&c, 0, sizeof(c));
        c.K = K;
        c.G = GG;
        random_cfg(&c);

        Cfg out;
        memset(&out, 0, sizeof(out));
        anneal(&c, 150000L, &out);
        int dup;
        int fin = evalc(&out, &dup);
        if (fin == 0) {
            best_n = N;
            best_cfg = out;
            bM = M;
            bK = Kk;
            bR = R;
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
    int K = best_cfg.K, G = best_cfg.G;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best_cfg.P[l][i], s = best_cfg.S[l][i];
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
    budget_end = start + max(3.0, min(0.9 * time_limit, time_limit - 6.0))

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

    if D == 4 and time.monotonic() < budget_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Simulated annealing over bi-Cayley voltage lifts, seeded with the best
    # valid order found so far as a lower bound.
    if d >= 3 and D >= 3 and d <= 16:
        c_budget = budget_end - time.monotonic() - 2.0
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
