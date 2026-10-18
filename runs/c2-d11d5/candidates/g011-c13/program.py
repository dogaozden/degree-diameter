"""Lift search with a C annealer over semidirect-product bi-Cayley graphs.

The C engine samples a group Z_m x| Z_k2 and a base size k, then anneals layer
permutations and voltages. Left multiplication by the group is an automorphism, so
the diameter condition reduces to 2k representative vertices: each vertex carries a
2k-bit mask of the representatives within distance D. One evaluation costs about
D*N*d word operations, far cheaper than the Python bigint or numpy version.

Every returned graph is checked with lib.is_valid. The fallback is K_{d,d}, or an
exact projective-plane / quadrangle / Araujo-Lopez construction when one applies.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 32768
#define MAXD 24
#define MAXK 8
#define MAXE ((MAXN / 2) * MAXD)
#define PEN 1000L

static int d, D;
static int K, K2, M, G, RR;
static int pw[64];
static int lay[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXN][MAXD];
static uint32_t RA[MAXN], RB[MAXN];
static int badv[MAXN];
static int bestE[2 * MAXE];
static int bestNv = 0, bestMv = 0;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmod_i(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group element (a, b) is coded a*K2 + b; (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long A = (a + (long)pw[b] * c) % M;
    int B = (b + e) % K2;
    return (int)(A * K2 + B);
}

/* Sample Z_M x| Z_K2 with M*K2 >= target. Sets K2, M, RR, G, pw. */
static const int K2_CHOICES[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(long target) {
    int nc = (int)(sizeof(K2_CHOICES) / sizeof(K2_CHOICES[0]));
    for (int tr = 0; tr < 200; tr++) {
        int k2 = K2_CHOICES[rndint(nc)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m > MAXN) return 0;
        int r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int t = 0; t < 80 && !found; t++) {
                long c = (t == 0) ? m - 1 : 1 + (long)(rnd64() % (uint64_t)(m - 1));
                if (gcd_i((int)c, (int)m) == 1 && powmod_i(c, k2, m) == 1 % m) {
                    r = (int)c;
                    found = 1;
                }
            }
            if (!found) continue;
        }
        K2 = k2;
        M = (int)m;
        RR = r;
        G = M * K2;
        pw[0] = 1 % M;
        for (int b = 1; b < K2; b++) pw[b] = (int)((long)pw[b - 1] * r % M);
        return 1;
    }
    return 0;
}

/* Layer l joins A-block i to B-block lay[l][i] with voltage S[l][i]:
 * A_{i,g} ~ B_{p,gmul(g,s)}. Writes both sides of that dart. */
static void set_dart(int l, int i) {
    int p = lay[l][i], s = S[l][i];
    int A0 = i * G, B0 = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        nbr[A0 + g][l] = B0 + h;
        nbr[B0 + h][l] = A0 + g;
    }
}

/* Total number of (vertex, representative) pairs at distance > D. Sets badv[]. */
static long unreached(int N) {
    uint32_t *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[v][l]];
            nxt[v] = x;
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int bad = 2 * K - __builtin_popcount(cur[v]);
        badv[v] = bad;
        tot += bad;
    }
    return tot;
}

/* Number of repeated (block, block, voltage) darts, which would create multi-edges. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l][i] == lay[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

static int search_lift(double deadline, long patience) {
    int N = 2 * K * G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);

    long cost = unreached(N) + PEN * dup_count();
    long bestc = cost, last = 0;
    double T0 = 2.0 + 0.02 * (double)cost;

    for (long t = 0;; t++) {
        if (cost == 0) return 1;
        if ((t & 63) == 0 && now() > deadline) return 0;
        if (t - last > patience) return 0;
        double temp = T0 * (1.0 - (double)(t - last) / (double)patience);
        if (temp < 0.3) temp = 0.3;

        long c2;
        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = t1;
            set_dart(l, i1);
            set_dart(l, i2);
            c2 = unreached(N) + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
            } else {
                t1 = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = t1;
                set_dart(l, i1);
                set_dart(l, i2);
                continue;
            }
        } else {
            int l = rndint(d), i = -1;
            if (rnd01() < 0.5) {
                /* Bias the move toward a vertex that still has unreached pairs. */
                int u = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int v = rndint(N);
                    if (badv[v] > 0) {
                        u = v;
                        break;
                    }
                }
                if (u >= 0) {
                    int blk = u / G;
                    if (blk < K) {
                        i = blk;
                    } else {
                        for (int ii = 0; ii < K; ii++)
                            if (lay[l][ii] == blk - K) {
                                i = ii;
                                break;
                            }
                    }
                }
            }
            if (i < 0) i = rndint(K);
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            c2 = unreached(N) + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
            } else {
                S[l][i] = old;
                set_dart(l, i);
                continue;
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = t;
        }
    }
}

static void store_best(void) {
    int A = K * G;
    int m = 0;
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++) {
            if (m >= MAXE) break;
            bestE[2 * m] = u;
            bestE[2 * m + 1] = nbr[u][l];
            m++;
        }
    bestNv = 2 * A;
    bestMv = m;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = atol(argv[5]);
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t_end = now() + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    long bestN = start_n;
    int found = 0;
    double goal = (double)start_n * 1.02 + 2.0;
    static const int KS[] = {1, 2, 3, 4, 6};
    int nks = 5;
    long trials[5] = {0, 0, 0, 0, 0}, wins[5] = {0, 0, 0, 0, 0};

    while (now() < t_end) {
        int bi;
        if (rnd01() < 0.2) {
            bi = rndint(nks);
        } else {
            double bestsc = -1.0;
            bi = 0;
            for (int j = 0; j < nks; j++) {
                double sc = (wins[j] + 1.0) / (trials[j] + 2.0) + 0.05 * rnd01();
                if (sc > bestsc) {
                    bestsc = sc;
                    bi = j;
                }
            }
        }
        K = KS[bi];
        long target = (long)ceil(goal / (2.0 * K)) + rndint(3);
        if (!sample_group(target)) {
            goal = fmax((double)bestN * 1.01, goal * 0.995);
            continue;
        }
        long Nl = 2L * K * G;
        if (Nl > MAXN) {
            goal = fmax((double)bestN * 1.01, goal * 0.99);
            continue;
        }
        if (Nl <= bestN) {
            goal = fmax(goal, (double)bestN * 1.02);
            continue;
        }
        trials[bi]++;
        double slice = now() + 6.0;
        if (slice > t_end) slice = t_end;
        if (search_lift(slice, 4000)) {
            wins[bi]++;
            store_best();
            bestN = Nl;
            found = 1;
            goal = (double)Nl * 1.03;
        } else {
            goal = fmax((double)bestN * 1.01, goal * 0.995);
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestNv, bestMv);
    for (int e = 0; e < bestMv; e++) printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: the C annealer over bi-Cayley lifts, seeded with the best order so far.
    remaining = final - time.monotonic() - 1.0
    if d >= 2 and D >= 2 and remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             timeout=remaining + 15)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
