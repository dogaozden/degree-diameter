import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (safe fallbacks, always valid).
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
# C engine: simulated annealing over group lifts with multi-layer base graphs.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, where G = |group| and
# group = Z_m x|_r Z_k (element (a,b) coded a*k+b). Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}; P[l] is a permutation, so the lift is
# Dd-regular. Left multiplication is an automorphism, so BFS from the
# identity of each of the 2K blocks gives the full cost. Cost = unreached
# (rep, vertex) pairs within DD steps + PEN * duplicate darts. Cost 0 means
# a valid graph. Each success raises the order target.
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
#define MAXN 8192
#define PEN 8

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double unif(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3, K = 1;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;

static int P[MAXD][MAXK], S[MAXD][MAXK];
static int bP[MAXD][MAXK], bS[MAXD][MAXK];
static int fP[MAXD][MAXK], fS[MAXD][MAXK];
static int adj[MAXN * MAXD];
static int deg[MAXN];
static int vis[MAXN];
static int que[MAXN];
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

static const int KF[] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 6, 7, 8, 9, 10,
                         12, 14, 16, 18, 20, 21, 24, 27, 28, 30, 32};

static void sample_group(long long G, int *om, int *ok, int *orr) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (G + k - 1) / k;
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
    *om = (int)m;
    *ok = k;
    *orr = r;
}

/* Weighted-free cost: unreached (rep, vertex) pairs + PEN * duplicate darts. */
static long long eval_cost(void) {
    int N = 2 * K * GG;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (K + j) * GG + gmul(g, s);
                adj[a * MAXD + deg[a]] = b;
                deg[a]++;
                adj[b * MAXD + deg[b]] = a;
                deg[b]++;
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    long long unr = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int src = r * GG;
        int head = 0, tail = 0;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = que[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * MAXD + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        unr += (long long)(N - tail);
    }
    return unr + (long long)PEN * dup;
}

static void random_state(void) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(GG);
    }
}

/* Simulated annealing on the current group. Leaves P, S at the best state
   found and returns its cost (0 means a valid lift). */
static long long anneal(long long iters) {
    long long cur = eval_cost();
    long long bestc = cur;
    memcpy(bP, P, sizeof(P));
    memcpy(bS, S, sizeof(S));
    double T0 = 5.0, T1 = 0.2;
    for (long long t = 0; t < iters && cur > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(K);
        int doswap = (K >= 2 && rint_(3) == 0);
        int i2 = i, oldv = 0;
        if (doswap) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
        } else {
            oldv = S[l][i];
            S[l][i] = rint_(GG);
        }
        long long c2 = eval_cost();
        int acc = (c2 <= cur) || (unif() < exp(-(double)(c2 - cur) / T));
        if (acc) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bP, P, sizeof(P));
                memcpy(bS, S, sizeof(S));
            }
        } else {
            if (doswap) {
                int tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                S[l][i] = oldv;
            }
        }
    }
    memcpy(P, bP, sizeof(P));
    memcpy(S, bS, sizeof(S));
    return bestc;
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
    int bK = 1, bGM = 1, bGK = 1, bR = 1;

    while (now_s() < deadline) {
        double u = unif();
        K = (u < 0.5) ? 1 : ((u < 0.85) ? 2 : 3);
        long long base = best_n / (2 * K) + 1;
        long long span = base / 30 + 2;
        long long G = base + (long long)rint_((int)span);
        int m, k, r;
        sample_group(G, &m, &k, &r);
        set_group(m, k, r);
        long long N = 2LL * K * GG;
        if (N > MAXN || N <= best_n) continue;

        random_state();
        long long iters = 60000 + (long long)rint_(60000);
        long long c = anneal(iters);
        if (c == 0) {
            best_n = N;
            have = 1;
            bK = K;
            bGM = m;
            bGK = k;
            bR = r;
            memcpy(fP, P, sizeof(P));
            memcpy(fS, S, sizeof(S));
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    K = bK;
    set_group(bGM, bGK, bR);
    int N = 2 * K * GG;
    printf("%d %ld\n", N, (long)Dd * K * GG);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = fP[l][i], s = fS[l][i];
            for (int g = 0; g < GG; g++) {
                printf("%d %d\n", i * GG + g, (K + j) * GG + gmul(g, s));
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
    budget = max(3.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Simulated annealing over non-abelian group lifts, seeded by the best order so far.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic()
        if c_budget >= 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 2.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
