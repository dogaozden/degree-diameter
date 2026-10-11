import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (always valid, used as fallbacks and as starting points).
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
# C engine: simulated annealing over semidirect-product lifts (a different
# search from breakout local search). Each candidate is a bi-regular lift
# with K base vertices per side over the group Z_m x|_r Z_k.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. P[l] is a permutation of 0..K-1, so the
# graph is d-regular. The lift is invariant under left translation by the
# group, so BFS from one vertex per fibre (2K reps) checks the diameter.
# Cost = unreached (rep, vertex) pairs within DD steps + PEN * duplicate darts.
# Cost 0 means a valid graph. When one is found, the group order is raised.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 4
#define MAXORD 6000
#define PEN 40
#define ITERS 60000
#define T0 1.2
#define T1 0.08

typedef struct {
    int K;
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

/* Element (a, b) is coded as a*GK + b; (a,b)*(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int capN = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;

static void ensure(int N) {
    if (N <= capN) return;
    free(adj);
    free(cnt);
    free(vis);
    free(qu);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    stamp = 0;
    if (!adj || !cnt || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

/* Cost of a configuration under the current group. */
static int eval_cfg(const Cfg *c, int *dupout) {
    int K = c->K, G = GG, N = 2 * K * G;
    ensure(N);
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                if (cnt[a] >= Dd || cnt[b] >= Dd) return 1000000000;
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
        int src = r * G;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                int cu = cnt[u];
                for (int t = 0; t < cu; t++) {
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
    long long total = raw + (long long)PEN * dup;
    if (total > 1000000000LL) total = 1000000000LL;
    return (int)total;
}

static void random_cfg(Cfg *c, int K) {
    c->K = K;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) c->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) c->S[l][i] = rint_(GG);
    }
}

/* Simulated annealing with exponentially cooling temperature.
   Returns the final cost; sets *found when the cost reaches 0. */
static int anneal(Cfg *c, long iters, int *found) {
    int dup = 0;
    int K = c->K;
    int cc = eval_cfg(c, &dup);
    double lr = log(T1 / T0);
    *found = 0;
    if (cc == 0) {
        *found = 1;
        return 0;
    }
    for (long t = 0; t < iters; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * exp(lr * (double)t / (double)iters);
        int mv = (K >= 2 && rint_(3) == 0);
        int l = rint_(Dd);
        int i = rint_(K);
        int i2 = 0, old = 0;
        if (mv) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        int nc = eval_cfg(c, &dup);
        int accept = (nc <= cc);
        if (!accept) {
            double x = -(double)(nc - cc) / T;
            accept = (x > -700.0) && (rdbl() < exp(x));
        }
        if (accept) {
            cc = nc;
            if (cc == 0) {
                *found = 1;
                return 0;
            }
        } else {
            if (mv) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old;
            }
        }
    }
    return cc;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18,
                         20, 21, 24, 28, 30, 32, 36, 40};

/* Sample a group Z_m x|_r Z_k with m*k >= target. */
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
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg bestcfg;
    memset(&bestcfg, 0, sizeof(bestcfg));

    while (now_s() < deadline) {
        int roll = rint_(100);
        int K = roll < 45 ? 1 : (roll < 75 ? 2 : (roll < 92 ? 3 : 4));
        long long Nt = (long long)best_n + 2 + (long long)rint_(best_n / 40 + 6);
        long long Gt = (Nt + 2 * K - 1) / (2 * K);
        long long span = Gt / 40 + 3;
        long long Gs = Gt + (long long)rint_((int)span);

        int M, k, R;
        sample_group(Gs, &M, &k, &R);
        set_group(M, k, R);
        if (GG > MAXORD) continue;
        int N = 2 * K * GG;
        if (N <= best_n) continue;

        Cfg cur;
        random_cfg(&cur, K);
        int found = 0;
        anneal(&cur, ITERS, &found);
        if (found) {
            best_n = N;
            bestcfg = cur;
            bM = M;
            bK = k;
            bR = R;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    int K = bestcfg.K, G = GG;
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
# Python glue: exact constructions first, then one annealing run that uses the
# remaining time. Every candidate is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _search(d, D, seed, budget, min_n):
    """One C search run. Returns (n, edges) if it produced a valid graph, else None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n],
                        timeout=budget + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


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

    # Annealing search over semidirect-product lifts, seeded above the baseline.
    if d >= 3 and D >= 3:
        total = deadline - time.monotonic() - 1.0
        if total >= 4.0:
            res = _search(d, D, seed, total, best_n)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
