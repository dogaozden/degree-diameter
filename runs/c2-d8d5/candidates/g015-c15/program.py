"""Bold variant: a C voltage search over semidirect groups Z_m x| Z_k2 with
   vertex-transitive cover checks (one BFS per block representative). Exact
   constructions (projective planes, Araujo-Lopez, W(q)) are the fallback. The
   C engine only reports graphs strictly larger than the best known order."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine. Graph: k base blocks per side, each block a copy of group G of order
# G = m*k2. Layer l pairs A-block i with B-block LAY[l][i] via voltage VO[l][i]:
# A_{i,g} ~ B_{j,g*s}. Left multiplication is an automorphism that is regular on
# each block, so the diameter is <= D iff every block representative reaches all
# vertices within D steps. Simulated annealing minimises unreached pairs plus a
# penalty for duplicate darts. Groups are sampled among orders just above the best.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley voltage search over semidirect groups Z_m x| Z_k2.
 * Usage: prog d D seed time_limit min_n
 * stdout: "n m" + edges of a valid graph with n > min_n, or "0 0" if none found.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 16
#define MAXK 8
#define MAXG 2048
#define MAXE (MAXN * MAXD / 2)
#define RESTART_ITERS 6000

static int d, D;
static long moore;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* Group state: element x = a*K2 + b, (a,b)(c,e) = (a + RP[b]*c mod MM, b+e mod K2). */
static int GG, KK, NN;
static int MM, K2, RR;
static int RP[MAXG];
static int MUL[MAXG * MAXG];
static int INV[MAXG];

static int LAY[MAXD][MAXK];
static int VO[MAXD][MAXK];
static int NB[MAXN][MAXD];
static int dist[MAXN];
static int queue_[MAXN];

static int OUT_N, NE;
static int EU[MAXE], EV[MAXE];

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return (int)((a + (long)RP[b] * c) % MM) * K2 + (b + e) % K2;
}

/* Pick a uniformly random semidirect group of order G and build its tables. */
static int pick_group(int G) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k2; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    if (cnt == 0) return 0;
    MM = bm;
    K2 = bk;
    RR = br;
    RP[0] = 1 % MM;
    for (int b = 1; b < K2; b++) RP[b] = (int)((long)RP[b - 1] * RR % MM);
    GG = G;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MUL[x * G + y] = gmul(x, y);
    for (int s = 0; s < G; s++)
        for (int x = 0; x < G; x++)
            if (MUL[s * G + x] == 0) { INV[s] = x; break; }
    return 1;
}

static void rebuild(void) {
    int K = KK, G = GG;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = LAY[l][i], s = VO[l][i], si = INV[s];
            for (int g = 0; g < G; g++) {
                NB[i * G + g][l] = (K + j) * G + MUL[g * G + s];
                NB[(K + j) * G + g][l] = i * G + MUL[g * G + si];
            }
        }
}

/* Sum over block representatives of the number of vertices NOT within distance D. */
static long cover_cost(void) {
    int K = KK, G = GG, N = NN;
    long cost = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        for (int v = 0; v < N; v++) dist[v] = -1;
        dist[src] = 0;
        int head = 0, tail = 0;
        queue_[tail++] = src;
        while (head < tail) {
            int v = queue_[head++];
            if (dist[v] >= D) continue;
            for (int l = 0; l < d; l++) {
                int u = NB[v][l];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    queue_[tail++] = u;
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

/* Duplicate darts: same A block, same B block, same voltage in two layers. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < KK; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (LAY[l][i] == LAY[l2][i] && VO[l][i] == VO[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    rebuild();
    return cover_cost() + (long)NN * dup_count();
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < KK; i++) LAY[l][i] = i;
        for (int i = KK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = LAY[l][i];
            LAY[l][i] = LAY[l][j];
            LAY[l][j] = t;
        }
        for (int i = 0; i < KK; i++) VO[l][i] = rndint(GG);
    }
}

/* Simulated annealing with restarts until a zero-cost state or the deadline. */
static int anneal(double dl) {
    while (now() < dl) {
        random_state();
        long cur = full_cost();
        if (cur == 0) return 1;
        double T0 = 1.0 + 0.05 * (double)cur;
        for (long t = 0; t < RESTART_ITERS; t++) {
            if ((t & 63) == 0 && now() > dl) return 0;
            double frac = 1.0 - (double)t / RESTART_ITERS;
            double T = 0.2 + T0 * frac;
            int l = rndint(d);
            if (KK >= 2 && rnd01() < 0.3) {
                int i1 = rndint(KK), i2 = rndint(KK - 1);
                if (i2 >= i1) i2++;
                int tmp = LAY[l][i1];
                LAY[l][i1] = LAY[l][i2];
                LAY[l][i2] = tmp;
                long nc = full_cost();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                    if (cur == 0) return 1;
                } else {
                    tmp = LAY[l][i1];
                    LAY[l][i1] = LAY[l][i2];
                    LAY[l][i2] = tmp;
                }
            } else {
                int i = rndint(KK);
                int old = VO[l][i];
                int nv = rndint(GG);
                if (nv == old) continue;
                VO[l][i] = nv;
                long nc = full_cost();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                    if (cur == 0) return 1;
                } else {
                    VO[l][i] = old;
                }
            }
        }
    }
    return 0;
}

static void save_graph(void) {
    rebuild();
    NE = 0;
    for (int v = 0; v < NN; v++)
        for (int l = 0; l < d; l++) {
            int u = NB[v][l];
            if (v < u && NE < MAXE) {
                EU[NE] = v;
                EV[NE] = u;
                NE++;
            }
        }
    OUT_N = NN;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit min_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int min_n = atoi(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    NE = 0;
    OUT_N = 0;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t_end = now() + limit * 0.9;
    moore = moore_bound();
    int best_n = min_n;

    while (now() < t_end) {
        if (best_n + 2 > moore) break;
        int k = 1 + rndint(6);
        long Gmin = best_n / (2L * k) + 1;
        if (Gmin < 2) Gmin = 2;
        long G = Gmin + rndint((int)(1 + Gmin / 40));
        if (G > MAXG || 2L * k * G > MAXN || 2L * k * G > moore) continue;
        if (!pick_group((int)G)) continue;
        KK = k;
        NN = 2 * k * (int)G;
        double dl = now() + 1.5;
        if (dl > t_end) dl = t_end;
        if (anneal(dl)) {
            save_graph();
            best_n = NN;
        }
    }

    if (NE == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", OUT_N, NE);
    for (int e = 0; e < NE; e++) printf("%d %d\n", EU[e], EV[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search (C): voltage lifts over semidirect groups, growing past best[0].
    if D >= 2 and time.monotonic() < end - 2.0:
        c_budget = end - time.monotonic() - 0.5
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best[0]],
                             timeout=c_budget + 8)
            n, e = lib.parse_graph_text(text)
            if n > 0:
                consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
