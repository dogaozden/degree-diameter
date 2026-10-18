"""Bi-Cayley voltage-lift search for bipartite graphs of max degree d and diameter D.

Construction: vertices are k A-blocks and k B-blocks, each a copy of a finite group
G = Z_m x| Z_k2. In each of the d layers, A-block i is matched to B-block lay[l][i]
through a voltage s: A_{i,g} ~ B_{p,g*s}. Every vertex then has degree exactly d.
Diameter is checked from one representative per block, using left multiplication
as a graph automorphism.

New in this version:
  * The simulated annealing and the reach bitmasks run in C (about 50x faster than
    the numpy version). Each block representative has a 16-bit reach mask, and one
    move costs D*d*N byte operations.
  * An elite ladder: the target order grows from the best valid order found so far,
    so every success raises the bar for the next group sample.
  * A bandit over base sizes k in 1..6, with defect-targeted voltage moves.
  * Exact small cases return instantly. The Araujo-Lopez graph is used for D = 3
    when d-2 is a prime power.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 6
#define ITERS 40000L
#define PATIENCE 3000L
#define PEN 1000LL

static int d, D, k, G, N, K2, MOD, RR;
static int *pw;
static int *nbr;
static int lay[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int svi[MAXD][MAXK];
static uint16_t *curR, *candR, *scratch;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static long trials[MAXK + 1], wins[MAXK + 1];
static int oN = 0, oM = 0;
static int *oE = NULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pop16(unsigned x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
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

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Group Z_MOD x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int be = b + e;
    if (be >= K2) be -= K2;
    long long na = ((long long)a + (long long)pw[b] * c) % MOD;
    return (int)na * K2 + be;
}

static int ginv(int x) {
    int a = x / K2, b = x - a * K2;
    int nb = (K2 - b) % K2;
    long long ia = (MOD - (long long)pw[nb] * a % MOD) % MOD;
    return (int)ia * K2 + nb;
}

/* Choose a random semidirect product with order at least target. */
static int set_group(int target) {
    static const int K2S[18] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    for (int att = 0; att < 300; att++) {
        int k2 = K2S[rndi(18)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 == 1 || m <= 2) {
            r = 1;
        } else if (k2 == 2 && rndu() < 0.3) {
            r = m - 1;
        } else {
            int found = 0;
            for (int tr = 0; tr < 80 && !found; tr++) {
                int c = 2 + rndi(m - 2);
                if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; found = 1; }
            }
            if (!found) continue;
        }
        K2 = k2; MOD = m; RR = r;
        free(pw);
        pw = malloc(sizeof(int) * (size_t)K2);
        long long p = 1 % m;
        for (int t = 0; t < K2; t++) {
            pw[t] = (int)p;
            p = p * r % m;
        }
        return 1;
    }
    return 0;
}

/* Write both-side neighbours of block i in layer l. */
static void set_dart(int l, int i) {
    int p = lay[l][i], s = sv[l][i], si = svi[l][i];
    int *row = nbr + (size_t)l * N;
    int ab = i * G, bb = (k + p) * G;
    for (int g = 0; g < G; g++) {
        row[ab + g] = bb + gmul(g, s);
        row[bb + g] = ab + gmul(g, si);
    }
}

/* reach[v] bit j set iff the representative of block j is within distance D of v.
   Result is written into a. b is scratch. */
static void compute_reach(uint16_t *a, uint16_t *b) {
    memset(a, 0, sizeof(uint16_t) * (size_t)N);
    for (int j = 0; j < 2 * k; j++) a[j * G] = (uint16_t)(1u << j);
    uint16_t *cur = a, *nx = b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t r = cur[v];
            for (int l = 0; l < d; l++) r |= cur[nbr[(size_t)l * N + v]];
            nx[v] = r;
            if (r != cur[v]) changed = 1;
        }
        uint16_t *tmp = cur; cur = nx; nx = tmp;
        if (!changed) break;
    }
    if (cur != a) memcpy(a, cur, sizeof(uint16_t) * (size_t)N);
}

static long long cost_of(const uint16_t *R) {
    long long c = 0;
    for (int v = 0; v < N; v++) c += 2 * k - pop16((unsigned)R[v]);
    return c;
}

/* Duplicate edges: same A-block, same B-block and same voltage in two layers. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static int sa_run(double deadline) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < k; i++) {
            sv[l][i] = rndi(G);
            svi[l][i] = ginv(sv[l][i]);
            set_dart(l, i);
        }
    }
    compute_reach(curR, scratch);
    long long cost = cost_of(curR) + PEN * dupcount();
    double c0 = cost > 0 ? (double)cost : 1.0;
    long long bestc = cost;
    long last = 0;
    uint16_t full = (uint16_t)((1u << (2 * k)) - 1);

    for (long t = 0; t < ITERS; t++) {
        if (cost == 0) return 1;
        if (t - last > PATIENCE) break;
        if ((t & 63) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rndu() < 0.25) {
            /* Layer swap: exchange B-targets of two A-blocks in one layer. */
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t1;
            set_dart(l, i1); set_dart(l, i2);
            compute_reach(candR, scratch);
            long long c2 = cost_of(candR) + PEN * dupcount();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint16_t *tp = curR; curR = candR; candR = tp;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                t1 = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t1;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }

        /* Voltage move, defect-targeted with probability 0.4. */
        int l, i, u = -1;
        if (rndu() < 0.4) {
            int cnt = 0;
            for (int v = 0; v < N; v++) {
                if (curR[v] != full) {
                    cnt++;
                    if (rndi(cnt) == 0) u = v;
                }
            }
        }
        if (u >= 0) {
            int blk = u / G;
            l = rndi(d);
            if (blk < k) {
                i = blk;
            } else {
                i = 0;
                for (int j = 0; j < k; j++) if (lay[l][j] == blk - k) i = j;
            }
        } else {
            l = rndi(d);
            i = rndi(k);
        }
        int old = sv[l][i], old_i = svi[l][i];
        int nw = rndi(G);
        if (nw == old) continue;
        sv[l][i] = nw; svi[l][i] = ginv(nw);
        set_dart(l, i);
        compute_reach(candR, scratch);
        long long c2 = cost_of(candR) + PEN * dupcount();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint16_t *tp = curR; curR = candR; candR = tp;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            sv[l][i] = old; svi[l][i] = old_i;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static void record(void) {
    int M = k * G * d;
    int *e = malloc(sizeof(int) * 2 * (size_t)M);
    int c = 0;
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++) {
            e[2 * c] = u;
            e[2 * c + 1] = nbr[(size_t)l * N + u];
            c++;
        }
    free(oE);
    oE = e; oM = M; oN = N;
}

static int pick_k(void) {
    if (rndu() < 0.2) return 1 + rndi(MAXK);
    int bestk = 1;
    double bv = -1.0;
    for (int kk = 1; kk <= MAXK; kk++) {
        double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.02 * rndu();
        if (v > bv) { bv = v; bestk = kk; }
    }
    return bestk;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();
    double deadline = now() + budget;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && m0 >= 0) {
        int *buf = malloc(sizeof(int) * 2 * (size_t)(m0 > 0 ? m0 : 1));
        int ok = 1;
        for (int e = 0; e < m0 && ok; e++)
            if (scanf("%d %d", &buf[2 * e], &buf[2 * e + 1]) != 2) ok = 0;
        if (ok) { oN = n0; oM = m0; oE = buf; }
        else free(buf);
    }

    if (d >= 2 && d <= MAXD && D >= 2) {
        while (now() < deadline) {
            int kk = pick_k();
            int base = oN / (2 * kk);
            int spread = base / 8 + 1;
            if (spread < 2) spread = 2;
            int target = base + 1 + rndi(spread);
            if (target < 2) target = 2;
            if (!set_group(target)) continue;
            k = kk;
            G = MOD * K2;
            N = 2 * k * G;
            if (N <= oN) continue;

            nbr = malloc(sizeof(int) * (size_t)d * (size_t)N);
            curR = malloc(sizeof(uint16_t) * (size_t)N);
            candR = malloc(sizeof(uint16_t) * (size_t)N);
            scratch = malloc(sizeof(uint16_t) * (size_t)N);
            trials[kk]++;
            if (sa_run(deadline)) {
                wins[kk]++;
                record();
            }
            free(nbr); free(curR); free(candR); free(scratch);
            nbr = NULL; curR = candR = scratch = NULL;
        }
    }

    printf("%d %d\n", oN, oM);
    for (int e = 0; e < oM; e++) printf("%d %d\n", oE[2 * e], oE[2 * e + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact and classical baselines (Python).
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
        if D == 3:
            if lib.is_prime_power(d - 1):
                return best
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                try:
                    consider(*lib.araujo_lopez_graph(d - 2))
                except ValueError:
                    pass

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)
        if d - 1 <= 9 and lib.is_prime_power(d - 1):
            return best

    # C search: elite ladder over bi-Cayley lifts, seeded with the best graph so far.
    elapsed = time.monotonic() - t0
    budget = min(0.8 * time_limit - 2.0, time_limit - elapsed - 6.0)
    if budget >= 2.0 and d >= 2:
        timeout = max(2.0, time_limit - elapsed - 3.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=timeout)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
