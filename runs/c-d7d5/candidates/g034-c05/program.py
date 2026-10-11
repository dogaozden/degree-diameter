import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (safe fallbacks, all verified with lib.is_valid).
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
# C engine: simulated annealing over bi-Cayley voltage assignments.
#
# Different from the previous breakout search: the base has K in {1,2} vertices
# per side, each side-block i uses a shift p[l] (so B-side neighbours of A_i are a
# permutation), and the darts carry group elements of Z_m x| Z_k. Moves are
# single-dart changes accepted by the Metropolis rule on the number of pairs
# unreached within DD steps (BFS from the 2K representative vertices, which is
# exact because the group acts transitively on each side), plus a duplicate-edge
# penalty. The group order is sampled above the best order found so far, and the
# window widens after repeated failures.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h.
# Dart (l,i) joins A_{i,g} to B_{(i+p[l]) mod K, g*S[l][i]}.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 2
#define GMAX 4000
#define NMAX (2 * MAXK * GMAX)
#define PEN 30
#define ANN_IT 60000
#define T0 3.0
#define T1 0.15

typedef struct {
    int K, G;
    int p[MAXD];
    int S[MAXD][MAXK];
} Cfg;

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static int adj[NMAX * MAXD];
static int acnt[NMAX];
static int vis[NMAX];
static int qu[NMAX];
static int stamp = 0;

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16,
                         18, 20, 21, 24, 28, 30, 32, 36, 40};

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

/* Cost = pairs unreached within DD steps from the 2K representatives
   + PEN * duplicate darts. Zero cost means a valid graph. */
static long long eval(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(acnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = (i + c->p[l]) % K;
            int s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + acnt[a]++] = b;
                adj[b * Dd + acnt[b]++] = a;
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->p[l1] == c->p[l2] && c->S[l1][i] == c->S[l2][i])
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
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        unreached += (long long)(N - tail);
    }
    return unreached + (long long)PEN * dup;
}

/* Metropolis annealing with geometric cooling from T0 to T1.
   Returns the final cost; the state is left at the final accepted state. */
static long long anneal(Cfg *c, long iters) {
    long long cur = eval(c);
    for (long t = 0; t < iters && cur != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int kind = (c->K > 1 && rint_(4) == 0);
        int i = 0, oldp = 0, olds = 0;
        if (kind) {
            oldp = c->p[l];
            c->p[l] = rint_(c->K);
        } else {
            i = rint_(c->K);
            olds = c->S[l][i];
            c->S[l][i] = rint_(c->G);
        }
        long long nc = eval(c);
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else if (kind) {
            c->p[l] = oldp;
        } else {
            c->S[l][i] = olds;
        }
    }
    return cur;
}

/* Sample Z_m x| Z_k with m*k >= Gmin. The window widens with consecutive failures. */
static void sample_group(long long Gmin, int fails, int *oM, int *ok, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    if ((long long)k > Gmin) k = 1;
    long long mb = (Gmin + k - 1) / k;
    if (mb < 1) mb = 1;
    long long span = mb / 30 + 2 + (long long)(fails / 4) * (mb / 60 + 1);
    if (span > mb / 3 + 2) span = mb / 3 + 2;
    long long m = mb + (long long)rint_((int)(span + 1));
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 300; t++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, (long long)k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = (int)m;
    *ok = k;
    *oR = r;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long best_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int have = 0;
    Cfg best;
    memset(&best, 0, sizeof(best));
    int bM = 1, bk = 1, bR = 1;
    int fails = 0;

    while (now_s() < deadline) {
        int K = (rint_(100) < 70) ? 1 : 2;
        long long Gmin = best_n / (2 * K) + 1;
        if (Gmin < 2) Gmin = 2;
        int M, k, R;
        sample_group(Gmin, fails, &M, &k, &R);
        set_group(M, k, R);
        if (GG < Gmin || GG > GMAX) continue;

        Cfg cur;
        memset(&cur, 0, sizeof(cur));
        cur.K = K;
        cur.G = GG;
        for (int l = 0; l < Dd; l++) {
            cur.p[l] = (K > 1) ? rint_(K) : 0;
            for (int i = 0; i < K; i++) cur.S[l][i] = rint_(GG);
        }

        long long c = anneal(&cur, ANN_IT);
        if (c == 0) {
            best = cur;
            bM = M;
            bk = k;
            bR = R;
            best_n = (long long)2 * K * GG;
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
    int K = best.K, G = best.G;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = (i + best.p[l]) % K;
            int s = best.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealing search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 6.0))

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

    # Simulated annealing over bi-Cayley voltage assignments, seeded with the
    # best order found so far as a lower bound.
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
