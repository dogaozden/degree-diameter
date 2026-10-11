import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as cheap, certainly valid starting points).
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
# C engine: a different construction family from the parent. It enumerates
# ALL semidirect groups Z_m x|_r Z_k of a given order G (every divisor k of G,
# not a fixed list), then runs simulated annealing over the dart values of a
# bi-Cayley-type graph (K blocks per side, K <= 2). Cost = unreached pairs
# within DD steps from one representative per block, plus a duplicate-edge
# penalty. Vertex-transitivity within blocks means these reps cover all pairs.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Cost 0 means a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 2
#define MAXG 2048
#define MAXN (2 * MAXK * MAXG)
#define PEN 40
#define ITERS 20000

static int Dd = 3, DD = 3;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

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

typedef struct {
    int K, G, m, k, r;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

/* Current group: element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int GM = 1, GK = 1, GG = 1;
static int gpow[MAXG];
static int MT[MAXG * MAXG];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    for (int x = 0; x < GG; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GG; y++) {
            int c = y / k, d = y % k;
            long long t = ((long long)a + (long long)gpow[b] * (long long)c) % m;
            MT[x * GG + y] = (int)t * k + (b + d) % k;
        }
    }
}

static int adj[MAXN * MAXD];
static int deg[MAXN];
static int vis[MAXN];
static int qbuf[MAXN];
static int stamp = 0;

/* Cost of a configuration in the current group: unreached pairs + PEN * duplicate darts. */
static long long cost_cfg(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + MT[g * GG + s];
                adj[a * MAXD + deg[a]++] = b;
                adj[b * MAXD + deg[b]++] = a;
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
        qbuf[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qbuf[head++];
                for (int t = 0; t < deg[u]; t++) {
                    int v = adj[u * MAXD + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qbuf[tail++] = v;
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
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(c->G);
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

/* Random semidirect group of order G: uniform divisor k, then a random
   action r (or the cyclic group with probability 1/3). */
static void pick_group(int G, int *om, int *ok, int *orr) {
    int divs[64], nd = 0;
    for (int k = 1; k <= G && nd < 64; k++)
        if (G % k == 0) divs[nd++] = k;
    int k = divs[rint_(nd)];
    int m = G / k, r = 1;
    if (k > 1 && m > 2 && rint_(3) != 0) {
        for (int t = 0; t < 300; t++) {
            int c = 2 + rint_(m - 2);
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = c;
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
    Cfg best;
    memset(&best, 0, sizeof(best));

    while (now_s() < deadline) {
        int K = (rint_(100) < 80) ? 1 : 2;
        int G0 = best_n / (2 * K) + 1;
        if (G0 > MAXG) break;
        int span = 1 + G0 / 30;
        int G = G0 + rint_(span);
        if (G > MAXG) G = MAXG;

        int m, k, r;
        pick_group(G, &m, &k, &r);
        set_group(m, k, r);

        Cfg cur;
        memset(&cur, 0, sizeof(cur));
        cur.K = K;
        cur.G = G;
        cur.m = m;
        cur.k = k;
        cur.r = r;
        random_cfg(&cur);

        long long cc = cost_cfg(&cur);
        Cfg runbest = cur;
        long long rb = cc;

        for (int it = 0; it < ITERS && cc > 0; it++) {
            if ((it & 255) == 0 && now_s() > deadline) break;
            double T = 2.0 * pow(0.1, (double)it / ITERS);
            Cfg nw = cur;
            int l = rint_(Dd);
            int i = rint_(K);
            if (K >= 2 && rint_(4) == 0) {
                int i2 = rint_(K - 1);
                if (i2 >= i) i2++;
                int t = nw.P[l][i];
                nw.P[l][i] = nw.P[l][i2];
                nw.P[l][i2] = t;
            } else {
                nw.S[l][i] = rint_(G);
            }
            long long nc = cost_cfg(&nw);
            if (nc <= cc || rnd01() < exp(-(double)(nc - cc) / T)) {
                cur = nw;
                cc = nc;
                if (cc < rb) {
                    rb = cc;
                    runbest = cur;
                }
            }
        }

        if (rb == 0) {
            int N = 2 * K * G;
            if (N > best_n) {
                best = runbest;
                best_n = N;
                have = 1;
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(best.m, best.k, best.r);
    int K = best.K, G = best.G, N = 2 * K * G;
    long edges = (long)Dd * K * G;
    printf("%d %ld\n", N, edges);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best.P[l][i], s = best.S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + MT[g * GG + s];
                printf("%d %d\n", a, b);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search over semidirect
# products. The fallback K_{d,d} is always kept and every candidate is checked.
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

    # Exact constructions.
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

    # Semidirect-group bi-Cayley annealing in C, seeded with the best known order.
    if 2 <= d <= 16 and D >= 2:
        budget = deadline - time.monotonic() - 1.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
