"""Bold change for d>=3, D>=3: single-group bi-Cayley graphs with exact word-coverage search.

Vertices A_g and B_h (g, h in G). A_g ~ B_h iff g^{-1} h in S, |S| = d, so the graph is a
bipartite double of Cayley(G, S). Left multiplication is an automorphism, so the diameter
is exact: with E = D//2 and O = (D-1)//2,
  A-A distances need (S S^-1)^E = G,
  B-B distances need (S^-1 S)^E = G,
  A-B distances need (S S^-1)^O S = G.
C searches over semidirect groups Z_m x| Z_k of growing order N (vertices 2N) and annealed
S, minimising the number of uncovered elements. Calibration constructions (projective
planes, Araujo-Pardo-Lopez, generalized quadrangle) are kept and returned early when exact.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
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
# C engine: bi-Cayley search over semidirect products Z_m x| Z_k.
# Output: "2N E" then the edges A_g=g -- B_{g s}=N+g*s for s in S.
# ----------------------------------------------------------------------------

C_CAYLEY = r'''
/* Bi-Cayley diameter search.
 * Usage: prog d D seed time_limit
 * Prints a bipartite graph (A_g=g, B_h=N+h, g~h iff g^-1 h in S) or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3000
#define MAXD 32
#define ATT_ITERS 15000

static int d, D, E, O;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

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

/* Group Z_gm x|_gr Z_gk, element a*gk+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gm, gk, gr, gN;
static int rp[MAXN];

static void set_group(int m, int k, int r) {
    gm = m; gk = k; gr = r; gN = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    int na = (int)((gm - ((long)rp[nb] * a) % gm) % gm);
    return na * gk + nb;
}

/* Random group of order N: cyclic, direct, or a random semidirect product. */
static int pick_group(int N) {
    int divs[256];
    int nd = 0;
    for (int k = 1; k <= N && nd < 256; k++)
        if (N % k == 0) divs[nd++] = k;
    for (int tries = 0; tries < 400; tries++) {
        int k = divs[rndint(nd)];
        int m = N / k;
        if (m <= 2 || k == 1 || rnd01() < 0.25) {
            set_group(m, k, 1 % m);
            return 1;
        }
        for (int t = 0; t < 60; t++) {
            int r = 2 + rndint(m - 2);
            if (gcd(r, m) == 1 && powmod(r, k, m) == 1 % m) {
                set_group(m, k, r);
                return 1;
            }
        }
    }
    return 0;
}

static int markv[MAXN];
static int stampc = 0;

/* out = { X_i * Y_j } as a set; returns its size. */
static int prod_set(const int *X, int nx, const int *Y, int ny, int *out) {
    stampc++;
    int c = 0;
    for (int i = 0; i < nx; i++)
        for (int j = 0; j < ny; j++) {
            int z = gmul(X[i], Y[j]);
            if (markv[z] != stampc) {
                markv[z] = stampc;
                out[c++] = z;
            }
        }
    return c;
}

static int tmpbuf[MAXN];

/* out = Y^e (set power, starting from {identity}); returns size. */
static int power_set(const int *Y, int ny, int e, int *out) {
    out[0] = 0;
    int nc = 1;
    for (int t = 0; t < e; t++) {
        int nn = prod_set(out, nc, Y, ny, tmpbuf);
        memcpy(out, tmpbuf, sizeof(int) * nn);
        nc = nn;
    }
    return nc;
}

static int bufT1[MAXD * MAXD], bufT1p[MAXD * MAXD];
static int bufA[MAXN], bufB[MAXN], bufL[MAXN], bufC[MAXN];

/* Number of uncovered elements over the three coverage conditions (0 = valid). */
static int cover(const int *S) {
    int Si[MAXD];
    for (int i = 0; i < d; i++) Si[i] = ginv(S[i]);
    int n1 = prod_set(S, d, Si, d, bufT1);
    int n1p = prod_set(Si, d, S, d, bufT1p);
    int ca = power_set(bufT1, n1, E, bufA);
    int cb = power_set(bufT1p, n1p, E, bufB);
    int co = power_set(bufT1, n1, O, bufL);
    int cc = prod_set(bufL, co, S, d, bufC);
    return (gN - ca) + (gN - cb) + (gN - cc);
}

static int S[MAXD];
static int bestS[MAXD], bestM, bestK, bestR, bestN = 0;

static int anneal(int iters) {
    for (int i = 0; i < d; i++) {
        int x, ok;
        do {
            x = rndint(gN);
            ok = 1;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { ok = 0; break; }
        } while (!ok);
        S[i] = x;
    }
    int cost = cover(S);
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && now() > t_end) return -1;
        int i = rndint(d), x = rndint(gN), ok = 1;
        for (int j = 0; j < d; j++)
            if (S[j] == x) { ok = 0; break; }
        if (!ok) continue;
        int old = S[i];
        S[i] = x;
        int nc = cover(S);
        double temp = 1.5 * (1.0 - (double)it / iters) + 0.05;
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp))
            cost = nc;
        else
            S[i] = old;
    }
    return cost == 0;
}

static void save_best(int N) {
    bestM = gm; bestK = gk; bestR = gr; bestN = N;
    memcpy(bestS, S, sizeof(int) * d);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    E = D / 2;
    O = (D - 1) / 2;

    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    long moore = 2 * s;
    long Nmax_l = moore / 2;
    int Nmax = Nmax_l < MAXN ? (int)Nmax_l : MAXN;

    int step = 8;
    while (now() < t_end) {
        int N = bestN == 0 ? d + 1 : bestN + step;
        if (N > Nmax) {
            if (bestN + 1 > Nmax) break;
            N = bestN + 1;
            step = 1;
        }
        int ok = 0;
        for (int att = 0; att < 3 && !ok && now() < t_end; att++) {
            if (!pick_group(N)) break;
            if (gN < d) break;
            int r = anneal(ATT_ITERS);
            if (r < 0) break;
            if (r == 1) {
                ok = 1;
                save_best(N);
            }
        }
        if (ok) {
            step = step * 2;
            if (step > 512) step = 512;
        } else {
            step /= 2;
            if (step < 1) step = 1;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestM, bestK, bestR);
    int N = gN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + gmul(g, bestS[i]));
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Exact constructions (calibration cases return here).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() - t0 < 0.5 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold path: bi-Cayley graphs over semidirect products, searched in C.
    if D >= 3:
        elapsed = time.monotonic() - t0
        budget = max(1.0, 0.8 * time_limit - 4.0 - elapsed)
        if budget > 1.0:
            try:
                text = lib.run_c(C_CAYLEY, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 10)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
