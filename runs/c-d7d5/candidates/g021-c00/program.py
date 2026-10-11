import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged from the parent; they are the safe fallback).
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
# C engine (new in this version): simulated annealing over multi-vertex
# group lifts.
#
# Structure: base has K "A" vertices and K "B" vertices. Each of the d layers
# is a perfect matching between them given by a permutation P[l], and each
# matched pair carries a voltage S[l][i] in a finite group G (semidirect
# product Z_m x| Z_k, element (a,b) coded a*k+b). Vertices are
# A_{i,g} = i*G+g and B_{j,h} = (K+j)*G+h, with dart (l,i) joining
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Left multiplication by any h in G is an
# automorphism, so distances from the 2K representatives g = 0 cover all
# pairs. Cost = unreached (representative, vertex) pairs within DD steps
# + PEN * duplicate darts. Cost 0 means a valid graph.
#
# Moves: re-draw one voltage, or swap two B-targets inside one layer.
# Search: annealing with a restart schedule; near-misses are reused as seeds
# for perturbed restarts. Group orders climb above the best valid order found.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXG 6000
#define MAXN (2 * MAXK * MAXG)
#define MAXDD 64
#define PEN 1000
#define RUN_ITERS 30000
#define NEAR_PCT 50
#define PERTURB 2

typedef struct {
    int K;
    int P[MAXDD][MAXK];
    int S[MAXDD][MAXK];
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

static int *adj = NULL, *cnt = NULL, *vis = NULL, *que = NULL;
static int stamp = 0;

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

/* (a,b)*(c,d) = (a + r^b c, b + d), coded a*k+b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void build_adj(const Cfg *c, int K, int G) {
    int N = 2 * K * G;
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
}

static int count_dup(const Cfg *c, int K) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    return dup;
}

static long long eval(const Cfg *c, int K, int G) {
    int N = 2 * K * G;
    build_adj(c, K, G);
    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int h = 0, t = 0;
        int src = r * G;
        vis[src] = stamp;
        que[t++] = src;
        for (int lv = 0; lv < DD; lv++) {
            int end = t;
            if (h == end) break;
            while (h < end) {
                int u = que[h++];
                for (int q = 0; q < Dd; q++) {
                    int v = adj[u * Dd + q];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[t++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - t);
    }
    return raw + (long long)PEN * (long long)count_dup(c, K);
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

/* Simulated annealing on the cost. Leaves *best at the lowest cost seen. */
static long long anneal(Cfg *c, int K, int G, long iters, double T0, double T1,
                        Cfg *best, long long *bestcost) {
    long long cur = eval(c, K, G);
    *bestcost = cur;
    *best = *c;
    for (long t = 0; t < iters && cur > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(K);
        int swap = (K >= 2) && (rint_(2) == 0);
        int i2 = 0, oldS = 0;
        if (swap) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            oldS = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long nc = eval(c, K, G);
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < *bestcost) {
                *bestcost = cur;
                *best = *c;
            }
        } else {
            if (swap) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = oldS;
            }
        }
    }
    return cur;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

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
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXDD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    adj = malloc(sizeof(int) * (size_t)MAXN * (size_t)Dd);
    cnt = malloc(sizeof(int) * (size_t)MAXN);
    vis = calloc((size_t)MAXN, sizeof(int));
    que = malloc(sizeof(int) * (size_t)MAXN);
    if (!adj || !cnt || !vis || !que) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now_s();
    deadline = t0 + tl;
    long long best_n = min_n;
    int have = 0;
    Cfg bestc;
    memset(&bestc, 0, sizeof(bestc));
    int bM = 1, bKk = 1, bR = 1;

    int have_near = 0;
    Cfg nearc;
    memset(&nearc, 0, sizeof(nearc));
    int nK = 1, nM = 1, nKk = 1, nR = 1;
    long long nearcost = 0;

    while (now_s() < deadline) {
        Cfg c;
        int K, M, Kk, R;
        int from_near = have_near && (rint_(100) < NEAR_PCT);
        if (from_near) {
            K = nK;
            M = nM;
            Kk = nKk;
            R = nR;
            set_group(M, Kk, R);
            c = nearc;
            for (int t = 0; t < PERTURB; t++) {
                int l = rint_(Dd);
                int i = rint_(K);
                c.S[l][i] = rint_(GG);
            }
        } else {
            int rr = rint_(100);
            K = rr < 50 ? 1 : (rr < 75 ? 2 : (rr < 90 ? 3 : 4));
            long long G0 = best_n / (2 * K) + 1;
            long long span = G0 / 30 + 4;
            long long G = G0 + (long long)rint_((int)span);
            sample_group(G, &M, &Kk, &R);
            if ((long long)M * (long long)Kk > MAXG) continue;
            set_group(M, Kk, R);
            random_cfg(&c, K);
        }

        long long N = 2LL * K * GG;
        if (N <= best_n) {
            have_near = 0;
            continue;
        }
        Cfg bc;
        long long bcost = 0;
        anneal(&c, K, GG, RUN_ITERS, 1.5, 0.1, &bc, &bcost);
        if (bcost == 0) {
            best_n = N;
            bestc = bc;
            bM = M;
            bKk = Kk;
            bR = R;
            have = 1;
            have_near = 0;
        } else if (!have_near || bcost < nearcost) {
            nearc = bc;
            nK = K;
            nM = M;
            nKk = Kk;
            nR = R;
            nearcost = bcost;
            have_near = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bKk, bR);
    int K = bestc.K;
    int G = GG;
    long long n = 2LL * K * G;
    long long m = (long long)Dd * K * G;
    printf("%lld %lld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bestc.P[l][i], s = bestc.S[l][i];
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

    # Annealing over multi-vertex group lifts, seeded with the best known order.
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
