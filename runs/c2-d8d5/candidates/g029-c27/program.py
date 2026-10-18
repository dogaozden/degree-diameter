"""Bi-Cayley voltage-lift search in C: semidirect groups Z_m x| Z_k, simulated annealing on reach masks, with exact fallbacks."""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift search for bipartite degree-diameter graphs.
 * Graph: k blocks A_i and k blocks B_j, each block a copy of a group G = Z_m x| Z_k2.
 * Layer l pairs A_i with B_{lay[l][i]} by voltage s = Sv[l][i]:
 *   A_{i,g} ~ B_{j,g*s}.   Left translations are automorphisms, so only the 2k block
 *   representatives need to be tracked when checking the diameter.
 * Usage: prog d D seed time_limit   (stdin ignored). Stdout: "n m" + edges.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define MAXG 4096
#define MAXNV 8192
#define ITERS 15000L
#define PATIENCE 4000L

static int d, D;
static double t_end;
static long moore;

static int K, GG;
static int lay[MAXD][MAXK];
static int Sv[MAXD][MAXK];
static int nbr[MAXD][MAXNV];
static uint64_t wa[MAXNV], wb[MAXNV];
static uint64_t ra[MAXNV], rb[MAXNV];
static int bestN;
static int bestAdj[MAXNV][MAXD];

typedef struct { int m, k2; int rp[MAXG]; } Grp;
static Grp GR;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcdi(int a, int b) {
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

/* Group element x = a*k2 + b, product (a,b)(c,e) = (a + r^b c mod m, b + e mod k2). */
static int gmul(int x, int y) {
    int k2 = GR.k2, m = GR.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long t = ((long)a + (long)GR.rp[b] * c) % m;
    return (int)t * k2 + (b + e) % k2;
}

static int ginv(int x) {
    int k2 = GR.k2, m = GR.m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long t = ((long)GR.rp[nb] * a) % m;
    int na = (int)((m - t) % m);
    return na * k2 + nb;
}

static void make_group(int G) {
    int divs[512], nd = 0;
    for (int t = 1; t <= G; t++)
        if (G % t == 0) divs[nd++] = t;
    int k2 = divs[rndint(nd)];
    int m = G / k2;
    int r = 1 % m;
    if (m > 2) {
        for (int tries = 0; tries < 200; tries++) {
            int c = 2 + rndint(m - 2);
            if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1) { r = c; break; }
        }
    }
    GR.m = m;
    GR.k2 = k2;
    GR.rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) GR.rp[b] = (int)((long)GR.rp[b - 1] * r % m);
}

/* Write the neighbours of layer l for block i (A side) and block lay[l][i] (B side). */
static void set_dart(int l, int i) {
    int j = lay[l][i], s = Sv[l][i], si = ginv(s);
    int G = GG, k = K;
    for (int g = 0; g < G; g++) {
        nbr[l][i * G + g] = (k + j) * G + gmul(g, s);
        nbr[l][(k + j) * G + g] = i * G + gmul(g, si);
    }
}

/* Returns the number of unreached (vertex, block-representative) pairs; fills out[v]. */
static long eval_unreached(uint64_t *out) {
    int N = 2 * K * GG;
    int nb = 2 * K;
    uint64_t *x = wa, *y = wb;
    for (int v = 0; v < N; v++) x[v] = 0;
    for (int b = 0; b < nb; b++) x[b * GG] |= 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t z = x[v];
            for (int l = 0; l < d; l++) z |= x[nbr[l][v]];
            y[v] = z;
            if (z != x[v]) changed = 1;
        }
        uint64_t *t = x;
        x = y;
        y = t;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        out[v] = x[v];
        bad += nb - __builtin_popcountll(x[v]);
    }
    return bad;
}

/* Number of repeated (block, layer-target, voltage) keys, which would create multi-edges. */
static long dups(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = 0; l2 < l1; l2++)
                if (lay[l1][i] == lay[l2][i] && Sv[l1][i] == Sv[l2][i]) c++;
    return c;
}

static int anneal(void) {
    const int N = 2 * K * GG;
    const uint64_t fm = (1ULL << (2 * K)) - 1;
    uint64_t *cur = ra, *cand = rb;

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) Sv[l][i] = rndint(GG);
        for (int i = 0; i < K; i++) set_dart(l, i);
    }

    long cost = eval_unreached(cur) + 1000L * dups();
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best_c = cost, last = 0;

    for (long it = 0; it < ITERS && cost > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) return 0;
        if (it - last > PATIENCE) break;
        double T = 0.01 * c0 * (1.0 - (double)it / (double)ITERS);
        if (T < 0.5) T = 0.5;

        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int t = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long nc = eval_unreached(cand) + 1000L * dups();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                uint64_t *tp = cur;
                cur = cand;
                cand = tp;
                if (cost < best_c) { best_c = cost; last = it; }
            } else {
                t = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d);
            int tgt = -1;
            for (int tr = 0; tr < 30; tr++) {
                int v = rndint(N);
                if (cur[v] != fm) { tgt = v; break; }
            }
            int i = -1;
            if (tgt >= 0 && rnd01() < 0.7) {
                int b = tgt / GG;
                if (b < K) {
                    i = b;
                } else {
                    int j = b - K;
                    for (int ii = 0; ii < K; ii++)
                        if (lay[l][ii] == j) { i = ii; break; }
                }
            }
            if (i < 0) i = rndint(K);
            int old = Sv[l][i];
            int nw = rndint(GG);
            if (nw == old) continue;
            Sv[l][i] = nw;
            set_dart(l, i);
            long nc = eval_unreached(cand) + 1000L * dups();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                uint64_t *tp = cur;
                cur = cand;
                cand = tp;
                if (cost < best_c) { best_c = cost; last = it; }
            } else {
                Sv[l][i] = old;
                set_dart(l, i);
            }
        }
    }

    if (cost != 0) return 0;
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++)
            bestAdj[v][l] = nbr[l][v];
    bestN = N;
    return 1;
}

static void print_best(void) {
    long m = 0;
    for (int u = 0; u < bestN; u++)
        for (int l = 0; l < d; l++)
            if (u < bestAdj[u][l]) m++;
    printf("%d %ld\n", bestN, m);
    for (int u = 0; u < bestN; u++)
        for (int l = 0; l < d; l++)
            if (u < bestAdj[u][l]) printf("%d %d\n", u, bestAdj[u][l]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.93 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 10000000L) break;
    }
    moore = 2 * s;

    /* Baseline K_{d,d}: diameter 2, always valid. */
    bestN = 2 * d;
    for (int u = 0; u < d; u++)
        for (int l = 0; l < d; l++) {
            bestAdj[u][l] = d + l;
            bestAdj[d + l][u] = u;
        }

    static const int KS[7] = {1, 1, 2, 2, 3, 4, 6};
    while (now() < t_end) {
        if (bestN >= moore) break;
        int k = KS[rndint(7)];
        long Gmin = bestN / (2L * k) + 1;
        long G = Gmin + rndint(3);
        long N = 2L * k * G;
        if (N > moore || N > MAXNV || G > MAXG) continue;
        K = k;
        GG = (int)G;
        make_group(GG);
        anneal();
    }
    print_best();
    return 0;
}
'''


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


def _cycle(n):
    """Cycle C_n (n even): max degree 2, diameter n/2, bipartite."""
    return n, [(i, (i + 1) % n) for i in range(n)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        return _cycle(2 * D)

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        """Replace the best graph if (n, e) is larger and valid."""
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

    # Bold search: C bi-Cayley voltage-lift annealing over semidirect groups.
    if d <= 16 and D >= 3:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
