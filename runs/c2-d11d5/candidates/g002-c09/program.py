"""Bold revision: a bi-Cayley lift search in C over semidirect products Z_m x| Z_k2.

Each lift has 2k base blocks of size G. The group acts on the left, so the graph is vertex-transitive
within each block. Diameter is therefore checked exactly by one depth-D BFS from each of the 2k block
representatives. The C annealer adapts the target order, the base size k and the group. The fallback
chain is projective plane / Araujo-Lopez / K_{d,d}, and every returned graph goes through lib.is_valid.
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

/* Bi-Cayley lift annealer.
 * Usage: prog d D seed time_limit start_n
 * Base: K blocks A_0..A_{K-1}, K blocks B_0..B_{K-1}; block size G = M*K2 (group Z_M x| Z_K2).
 * Layer l pairs A_i with B_{sig[l][i]} through voltage sv[l][i]: A_{i,g} ~ B_{j, g*s}.
 * Left multiplication is an automorphism, so the diameter is checked from the 2K block representatives.
 * stdout: "n m" + edges of the best valid graph found, or "0 0".
 */

#define MAXK 6
#define MAXL 32
#define MAXK2 64
#define MAXV 24000
#define PEN 1000
#define NKS 5
#define NK2S 12

static const int KS[NKS] = {2, 3, 4, 5, 6};
static const int K2S[NK2S] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12};

static int d, D;
static int K, K2, M, R, G, N;
static int pw[MAXK2];
static int sig[MAXL][MAXK];
static int sv[MAXL][MAXK];
static int nbr[MAXV * MAXL];
static int bestnbr[MAXV * MAXL];
static int bestN = 0, bestK = 0;
static int mark[MAXV];
static int queue_[MAXV];
static int stampv = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rndu(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Semidirect product: (a,b)*(c,e) = (a + R^b c, b + e), element coded as a*K2 + b. */
static int mul_el(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long t = ((long)pw[b] * c) % M;
    int aa = (int)((a + t) % M);
    return aa * K2 + (b + e) % K2;
}

static void setup_group(void) {
    G = M * K2;
    N = 2 * K * G;
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long)pw[b - 1] * R % M);
}

static int find_R(void) {
    if (K2 == 1 || M < 3) return 1 % M;
    if (rndu() < 0.3) return 1 % M;
    for (int tries = 0; tries < 400; tries++) {
        int r = 2 + rndi(M - 2);
        if (gcd_i(r, M) != 1) continue;
        long p = 1 % M;
        for (int t = 0; t < K2; t++) p = p * r % M;
        if (p == 1 % M) return r;
    }
    return 1 % M;
}

static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = sig[l][i], s = sv[l][i];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + mul_el(g, s);
            nbr[a * d + l] = b;
            nbr[b * d + l] = a;
        }
    }
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) sig[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = sig[l][i];
            sig[l][i] = sig[l][j];
            sig[l][j] = t;
        }
        for (int i = 0; i < K; i++) sv[l][i] = rndi(G);
        rebuild_layer(l);
    }
}

/* Number of vertices not within distance D of src. */
static long unreached(int src) {
    stampv++;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    mark[src] = stampv;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = queue_[head++];
            const int *nb = nbr + (long)v * d;
            for (int l = 0; l < d; l++) {
                int u = nb[l];
                if (mark[u] != stampv) {
                    mark[u] = stampv;
                    queue_[tail++] = u;
                }
            }
        }
    }
    return (long)N - tail;
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (sig[l1][i] == sig[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static long total_cost(void) {
    long c = 0;
    for (int i = 0; i < 2 * K; i++) c += unreached(i * G);
    return c + (long)PEN * dupcount();
}

/* Simulated annealing on one fixed group. Returns 1 on a valid lift (state left in nbr). */
static int anneal(double t_end, double slice) {
    random_init();
    long cur = total_cost();
    double ts = now();
    const double T0 = 8.0, RATIO = 0.01;
    for (;;) {
        if (cur == 0) return 1;
        double tn = now();
        if (tn > t_end) return 0;
        double frac = (tn - ts) / slice;
        if (frac > 1.0) frac = 1.0;
        double T = T0 * pow(RATIO, frac);
        if (K >= 2 && rndu() < 0.3) {
            int l = rndi(d);
            int i1 = rndi(K), i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int t = sig[l][i1];
            sig[l][i1] = sig[l][i2];
            sig[l][i2] = t;
            rebuild_layer(l);
            long nc = total_cost();
            if (nc <= cur || rndu() < exp((double)(cur - nc) / T)) {
                cur = nc;
            } else {
                t = sig[l][i1];
                sig[l][i1] = sig[l][i2];
                sig[l][i2] = t;
                rebuild_layer(l);
            }
        } else {
            int l = rndi(d), i = rndi(K);
            int old = sv[l][i];
            int nv = rndi(G);
            if (nv == old) continue;
            sv[l][i] = nv;
            rebuild_layer(l);
            long nc = total_cost();
            if (nc <= cur || rndu() < exp((double)(cur - nc) / T)) {
                cur = nc;
            } else {
                sv[l][i] = old;
                rebuild_layer(l);
            }
        }
    }
}

static double moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2.0 * D;
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
    }
    return 2.0 * s;
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
    double start_n = atof(argv[5]);
    if (d < 3 || d > MAXL || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double deadline = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    double mb = moore_bound();
    double capn = mb < MAXV ? mb : MAXV;
    double tgt = start_n;
    if (tgt > capn * 0.97) tgt = capn * 0.97;

    for (;;) {
        double remaining = deadline - now();
        if (remaining < 1.0) break;
        if (bestN + 1 > capn) break;
        int Nt = (int)tgt;
        if (Nt < bestN + 1) Nt = bestN + 1;

        int Kc = KS[rndi(NKS)];
        int K2c = K2S[rndi(NK2S)];
        int Gmin = (Nt + 2 * Kc - 1) / (2 * Kc);
        int Mc = (Gmin + K2c - 1) / K2c + rndi(3);
        if (Mc < 2) Mc = 2;
        K = Kc;
        K2 = K2c;
        M = Mc;
        R = find_R();
        setup_group();
        if ((double)N > capn) continue;

        double slice = remaining * 0.15;
        if (slice < 2.0) slice = 2.0;
        if (slice > remaining) slice = remaining;
        int ok = anneal(now() + slice, slice);
        if (ok) {
            if (N > bestN) {
                bestN = N;
                bestK = K;
                memcpy(bestnbr, nbr, sizeof(int) * (size_t)N * d);
            }
            tgt = bestN * 1.01 + 1.0;
        } else {
            tgt *= 0.98;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    int half = bestN / 2;
    printf("%d %ld\n", bestN, (long)half * d);
    for (int v = 0; v < half; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, bestnbr[v * d + l]);
    (void)bestK;
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept from the previous program).
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

    final = t0 + max(1.0, 0.85 * time_limit - 2.0)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: bi-Cayley lift annealing in C, starting from a target below the record scale.
    if d >= 3 and D >= 2:
        remaining = final - time.monotonic() - 1.5
        if remaining > 3.0:
            moore = lib.moore_bound(d, D)
            start_n = max(best_n + 1, int(0.18 * moore))
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), start_n],
                                 timeout=remaining + 10)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
