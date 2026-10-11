import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions used as the starting lower bound.
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
# C engine: simulated annealing over bi-Cayley lifts Z_m x| Z_k with K base
# vertices per side. Vertices A_{i,g} = i*G+g and B_{j,h} = (K+j)*G+h; dart
# (l, i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation,
# so the graph is biregular with degree Dd. Left multiplication is an
# automorphism, so only the 2K representative vertices need BFS, which keeps
# every evaluation cheap. Cost = unreached (rep, vertex) pairs within DD plus
# PEN per duplicate edge. Cost 0 is a valid graph. The search climbs the order
# by requiring each success to beat the previous best.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 4
#define MAXN 20000
#define PEN 4

static int Dd = 7, DD = 5;
static int K = 1, GM = 1, GK = 1, GG = 1, GR = 1;
static int gpow[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int bP[MAXD][MAXK], bS[MAXD][MAXK];
static int adj[MAXN * MAXD];
static int cnt[MAXN];
static int vis[MAXN], qbuf[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
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

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    GR = r;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

/* (a,b)*(c,d) = (a + r^b c, b + d), element coded as a*k+b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static const int KF[] = {1, 1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24};

static void sample_group(long long Gt) {
    int k = KF[rint_((int)(sizeof KF / sizeof KF[0]))];
    long long m = (Gt + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1) {
        int ok = 0;
        for (int t = 0; t < 400 && !ok; t++) {
            long long c = (long long)rint_((int)m);
            if (c < 2) continue;
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                ok = 1;
            }
        }
        if (!ok) {
            k = 1;
            r = 1;
            m = Gt < 2 ? 2 : Gt;
        }
    }
    set_group((int)m, k, r);
}

static void build_graph(void) {
    int N = 2 * K * GG;
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (K + j) * GG + gmul(g, s);
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
}

static long long evaluate(void) {
    int N = 2 * K * GG;
    build_graph();
    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * GG;
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qbuf[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qbuf[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qbuf[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return raw + (long long)PEN * dup;
}

static void random_cfg(void) {
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

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int best_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    deadline = now_s() + tl;
    int have = 0, bK = 1, bGM = 1, bGK = 1, bR = 1, fails = 0;
    const double T0 = 1.2, T1 = 0.08;
    const long L = 8000;

    while (now_s() < deadline) {
        int Kc = rint_(10) < 6 ? 1 : (rint_(10) < 6 ? 2 : 3);
        long long Glo = best_n / (2 * Kc) + 1;
        long long span = Glo / 40 + 3 + (long long)(fails / 8) * (Glo / 80 + 1);
        if (span > Glo / 4 + 5) span = Glo / 4 + 5;
        long long Gt = Glo + rint_((int)(span + 1));
        if (2LL * Kc * Gt > MAXN) Gt = MAXN / (2 * Kc);
        if (Gt <= Glo) {
            fails++;
            continue;
        }

        K = Kc;
        sample_group(Gt);
        if (GG < 2 || 2 * K * GG > MAXN || 2 * K * GG <= best_n) {
            fails++;
            continue;
        }

        random_cfg();
        long long cc = evaluate();
        int success = (cc == 0);
        for (long it = 0; it < L && !success; it++) {
            if ((it & 255) == 0 && now_s() > deadline) break;
            double T = T0 * pow(T1 / T0, (double)it / (double)L);
            int swap = (K >= 2 && rint_(10) < 2);
            int l = rint_(Dd), i = rint_(K), i2 = 0, old = 0, tmp;
            if (swap) {
                i2 = rint_(K - 1);
                if (i2 >= i) i2++;
                tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                old = S[l][i];
                S[l][i] = rint_(GG);
            }
            long long nc = evaluate();
            int acc = (nc <= cc) || (urand() < exp(-(double)(nc - cc) / T));
            if (acc) {
                cc = nc;
                if (cc == 0) success = 1;
            } else if (swap) {
                tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                S[l][i] = old;
            }
        }

        if (success) {
            best_n = 2 * K * GG;
            have = 1;
            bK = K;
            bGM = GM;
            bGK = GK;
            bR = GR;
            memcpy(bP, P, sizeof P);
            memcpy(bS, S, sizeof S);
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    K = bK;
    set_group(bGM, bGK, bR);
    memcpy(P, bP, sizeof P);
    memcpy(S, bS, sizeof S);
    int N = 2 * K * GG;
    long m = (long)Dd * K * GG;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                printf("%d %d\n", i * GG + g, (K + j) * GG + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the C search, always with a valid fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.9 * time_limit, time_limit - 4.0))

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2) and time.monotonic() < deadline:
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if D == 3 and pg is not None and lib.is_prime_power(d - 1):
            return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealing over bi-Cayley lifts, seeded with the best order found so far.
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
