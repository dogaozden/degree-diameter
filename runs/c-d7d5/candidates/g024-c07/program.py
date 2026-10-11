"""Bold variant: lifts over a wider family of groups (semidirect products Z_m x| Z_k,
including direct products when r = 1), base sizes K = 1..4, and simulated annealing
on the unreached-pair cost, with restarts that climb from the best valid order found.
Exact constructions (PG(2,q), W(q), K_{d,d}) remain the valid fallback."""

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
# C engine.
#
# Lift model: base bipartite multigraph with K vertices per side, each dart
# layer l (0..d-1) is a perfect matching between the A and B blocks given by a
# permutation P[l] and a voltage S[l][i] in a group G = Z_m x|_r Z_k (r = 1 gives
# the direct product). Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, and
# dart (l,i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}. Left multiplication is an
# automorphism, so the diameter check only needs BFS from the 2K block
# representatives. Search: simulated annealing on (unreached pairs + PEN*dups).
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
#define PEN 1000
#define MAXG 6000
#define RUN_ITERS 40000
#define NEAR_PCT 30
#define PERTURB 3

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

typedef struct {
    int K, M, Kk, R;
    Cfg c;
} Sol;

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

/* Element (a,b) coded as a*GK+b; (a,b)(c,d) = (a + r^b c, b + d). Identity is 0. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cap = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;

static void ensure_cap(int N) {
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
    stamp = 0;
}

static long long g_raw = 0, g_dup = 0;

/* Returns raw + PEN*dup. Cost 0 means a valid graph. */
static long long evalc(const Cfg *c) {
    int K = c->K, G = GG, N = 2 * K * G;
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
    g_raw = raw;
    g_dup = dup;
    return raw + (long long)PEN * dup;
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

static void perturb(Cfg *c, int K, int times) {
    for (int t = 0; t < times; t++) {
        int l = rint_(Dd);
        int i = rint_(K);
        c->S[l][i] = rint_(GG);
    }
}

/* Simulated annealing; *best receives the lowest-cost state seen. */
static long long anneal(Cfg *cur, long iters, double T0, double T1, Cfg *best, long long *bestcost) {
    int K = cur->K;
    long long cc = evalc(cur);
    long long bc = cc;
    *best = *cur;
    for (long t = 0; t < iters && cc != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(K);
        int kind = (K >= 2 && rint_(3) == 0);
        int i2 = 0, old = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = cur->P[l][i];
            cur->P[l][i] = cur->P[l][i2];
            cur->P[l][i2] = tmp;
        } else {
            old = cur->S[l][i];
            cur->S[l][i] = rint_(GG);
        }
        long long nc = evalc(cur);
        long long delta = nc - cc;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cc = nc;
            if (cc < bc) {
                bc = cc;
                *best = *cur;
            }
        } else {
            if (kind) {
                int tmp = cur->P[l][i];
                cur->P[l][i] = cur->P[l][i2];
                cur->P[l][i2] = tmp;
            } else {
                cur->S[l][i] = old;
            }
        }
    }
    *bestcost = bc;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21,
                         24, 27, 28, 30, 32, 36, 40, 42, 48, 54, 56, 60};

/* Group of order m*k with r^k = 1 mod m; r = 1 gives the direct product. */
static void sample_group(long long g, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (g + k - 1) / k;
    if (m < 1) m = 1;
    int r = 1;
    if (k > 1 && m > 2 && rint_(10) < 7) {
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
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    long long best_n = min_n;
    int have = 0;
    Sol bestsol;
    memset(&bestsol, 0, sizeof(bestsol));
    int have_near = 0;
    Sol near;
    memset(&near, 0, sizeof(near));
    long long near_cost = 0;

    while (now_s() < deadline) {
        Sol s;
        memset(&s, 0, sizeof(s));
        int reuse = have_near && (rint_(100) < NEAR_PCT);
        double T0;
        if (reuse) {
            s = near;
            set_group(s.M, s.Kk, s.R);
            perturb(&s.c, s.K, PERTURB);
            T0 = 1.2;
        } else {
            int rk = rint_(100);
            int K = rk < 50 ? 1 : (rk < 80 ? 2 : (rk < 92 ? 3 : 4));
            long long g0 = best_n / (2 * K) + 1;
            long long span = (rint_(2) == 0) ? (g0 / 100 + 2) : (g0 / 12 + 3);
            long long g = g0 + (long long)rint_((int)span);
            int M, Kk, R;
            sample_group(g, &M, &Kk, &R);
            if ((long long)M * Kk > MAXG) continue;
            set_group(M, Kk, R);
            s.K = K;
            s.M = M;
            s.Kk = Kk;
            s.R = R;
            random_cfg(&s.c, K);
            T0 = 4.0;
        }
        long long N = 2LL * s.K * GG;
        if (N <= best_n) {
            if (reuse) have_near = 0;
            continue;
        }
        ensure_cap((int)N);
        Cfg bc;
        long long bcost = 0;
        anneal(&s.c, RUN_ITERS, T0, 0.15, &bc, &bcost);
        if (bcost == 0) {
            best_n = N;
            bestsol = s;
            bestsol.c = bc;
            have = 1;
            have_near = 0;
        } else if (!have_near || bcost < near_cost) {
            near = s;
            near.c = bc;
            near_cost = bcost;
            have_near = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestsol.M, bestsol.Kk, bestsol.R);
    int K = bestsol.K, G = GG;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestsol.c.P[l][i], sv = bestsol.c.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, sv));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer, then validation.
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

    # Annealing search over wider group lifts, climbing above the best valid order.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
