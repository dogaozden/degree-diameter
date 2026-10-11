import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (used for D = 3 and D = 4).
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
# C engine: simulated annealing over bi-Cayley voltage lifts.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation, so every
# vertex has degree exactly Dd. The group is Z_M x|_r Z_k (semidirect,
# element (a,b) coded as a*k+b, r^k = 1 mod M), with exact order G = M*k.
#
# Search structure (differs from a breakout search):
#   * group order is drawn just above the current best, with random base size K in 1..4;
#   * for each candidate group, a time-sliced simulated annealing with a
#     geometric temperature schedule minimises the number of pairs
#     (representative, vertex) at distance > DD, plus a duplicate-dart penalty;
#   * a success raises the bound and the search continues upward.
# Cost 0 with no duplicates means a valid graph. Left multiplication by the
# group is an automorphism, so BFS from the identity of each base part suffices.
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
#define MAXG 6000
#define MAXDIV 48
#define PEN 40
#define SLICE 2.0
#define TSTART 1.2
#define TEND 0.12

typedef struct {
    int K, G, M, k, r;
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

static double rand01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static int capN = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;

static void ensure_cap(int N) {
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
    if (!adj || !cnt || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 0;
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

/* Cost = (pairs of representative and vertex at distance > DD) + PEN * duplicate darts. */
static long long eval_cfg(const Cfg *c, long long *rawp) {
    int K = c->K, G = c->G, N = 2 * K * G;
    for (int v = 0; v < N; v++) cnt[v] = 0;
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
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i]) dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (stamp >= 2000000000) {
            memset(vis, 0, sizeof(int) * (size_t)capN);
            stamp = 0;
        }
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
        raw += (long long)(N - tail);
    }
    *rawp = raw;
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

/* Time-sliced simulated annealing with geometric cooling. Returns the best
   cost reached; leaves *c at that best state. Group must already be set. */
static long long anneal(Cfg *c, double slice) {
    double ts = now_s();
    double te = ts + slice;
    long long rawc = 0;
    long long cc = eval_cfg(c, &rawc);
    long long best = cc;
    Cfg bc = *c;
    double Tcur = TSTART;
    long it = 0;
    while (best != 0) {
        if ((it & 63) == 0) {
            double t = now_s();
            if (t >= te || t >= deadline) break;
            double f = (t - ts) / slice;
            if (f < 0.0) f = 0.0;
            if (f > 1.0) f = 1.0;
            Tcur = TSTART * pow(TEND / TSTART, f);
        }
        it++;
        int l = rint_(Dd);
        int i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(4) == 0);
        int i2 = i, old = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = t;
        } else {
            old = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long nraw = 0;
        long long nc = eval_cfg(c, &nraw);
        long long delta = nc - cc;
        if (delta <= 0 || rand01() < exp(-(double)delta / Tcur)) {
            cc = nc;
            if (cc < best) {
                best = cc;
                bc = *c;
            }
        } else {
            if (kind) {
                int t = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = t;
            } else {
                c->S[l][i] = old;
            }
        }
    }
    *c = bc;
    return best;
}

/* Choose a group of exact order target = M * k with k a divisor <= MAXDIV.
   Fills c->M, c->k, c->r, c->G. */
static void pick_group(long long target, Cfg *c) {
    int divs[MAXDIV];
    int nd = 0;
    for (int k = 1; k <= MAXDIV && (long long)k <= target; k++)
        if (target % k == 0) divs[nd++] = k;
    int k = divs[rint_(nd)];
    int M = (int)(target / k);
    int r = 1;
    if (k > 1 && M > 2) {
        for (int t = 0; t < 300; t++) {
            long long cand = 2 + rint_(M - 2);
            if (gcdll(cand, M) == 1 && powmod(cand, k, M) == 1 % M) {
                r = (int)cand;
                break;
            }
        }
    }
    c->M = M;
    c->k = k;
    c->r = r;
    c->G = M * k;
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

    deadline = now_s() + tl;
    long long best_n = min_n;
    int have = 0;
    Cfg bestcfg;
    memset(&bestcfg, 0, sizeof(bestcfg));

    while (now_s() < deadline - 0.05) {
        double rem = deadline - now_s();
        int q = rint_(100);
        int K = q < 50 ? 1 : (q < 75 ? 2 : (q < 90 ? 3 : 4));
        long long lo = best_n / (2 * K) + 1;
        long long span = lo / 8 + 3;
        long long GT = lo + (long long)rint_((int)span);
        if (GT > MAXG) continue;

        Cfg c;
        memset(&c, 0, sizeof(c));
        pick_group(GT, &c);
        c.K = K;
        set_group(c.M, c.k, c.r);
        ensure_cap(2 * K * GG);
        random_cfg(&c);

        double slice = SLICE < rem - 0.2 ? SLICE : rem - 0.2;
        if (slice < 0.05) break;
        long long bc = anneal(&c, slice);
        if (bc == 0) {
            best_n = 2LL * K * GG;
            bestcfg = c;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestcfg.M, bestcfg.k, bestcfg.r);
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
# Python glue: exact constructions first, then the C annealer, always with a
# validated fallback.
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

    # Simulated annealing over semidirect-product voltage lifts, seeded with
    # the best order found so far as a lower bound.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 2.5)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
