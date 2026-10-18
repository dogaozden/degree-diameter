"""Bi-Cayley voltage-lift search, now run entirely in C.

New routine: a C annealer for bi-Cayley lifts over semidirect products Z_m x| Z_k2.
Each lift is K blocks per side, each a copy of the group H. Layer l pairs A_i with
B_{lay[l][i]} through a voltage s, giving A_{i,g} ~ B_{p,g*s}. Left multiplication by H is an
automorphism, so every pair is within distance D iff each of the 2K block representatives reaches
every vertex within D. Reach is a 2K-bit mask per vertex, so one cost evaluation is O(D*d*N).
Moves: voltage changes (biased toward unreached vertices) and layer-entry swaps. Groups are
sampled with the order ratcheted upward. The C engine returns the best valid graph it found.

Python keeps the exact constructions (projective planes, Araujo-Pardo-Lopez, generalized
quadrangle) and K_{d,d} as fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley voltage-lift annealer with bitset reach over block representatives.
 * Usage: prog d D seed time_limit   (stdin is ignored)
 * stdout: "n m" + edges of the best valid lift found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXN 40000
#define PEN 1000L
#define ITERS 60000L
#define PATIENCE 6000L

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static double deadline;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ---- group Z_m x| Z_k2, element code a*k2+b, (a,b)(c,e) = (a + r^b c, b + e) ---- */
static int gm, gk2, gr;
static long gpw[64];

static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    gr = r;
    gpw[0] = 1 % m;
    for (int b = 1; b < k2; b++) gpw[b] = gpw[b - 1] * r % m;
}

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long aa = (a + gpw[b] * c) % gm;
    return (int)(aa * gk2 + (b + e) % gk2);
}

/* ---- lift state ---- */
static int K, G, N;
static int lay[MAXD][MAXK];
static int vs[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t accR[MAXN], trialR[MAXN], scr1[MAXN], scr2[MAXN];

static void set_dart(int l, int i, int j, int s) {
    int A0 = i * G, B0 = (K + j) * G;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        nbr[l][A0 + g] = B0 + h;
        nbr[l][B0 + h] = A0 + g;
    }
}

static void set_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i, lay[l][i], vs[l][i]);
}

/* Writes reach masks into out; returns the number of unreached (rep, vertex) pairs. */
static long reach_eval(uint32_t *out) {
    uint32_t *cur = scr1, *nx = scr2;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(long)b * G] = 1u << b;
    for (int step = 0; step < D; step++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nx[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *t = cur;
        cur = nx;
        nx = t;
        if (!changed) break;
    }
    memcpy(out, cur, sizeof(uint32_t) * (size_t)N);
    long cnt = 0;
    for (int v = 0; v < N; v++) cnt += __builtin_popcount(out[v]);
    return 2L * K * N - cnt;
}

/* Number of repeated (block pair, voltage) darts, which would create parallel edges. */
static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && vs[l1][i] == vs[l2][i]) dup++;
    return dup;
}

static long total_cost(uint32_t *buf) {
    return reach_eval(buf) + PEN * (long)dupcount();
}

static int accept(long c2, long c, double temp) {
    if (c2 <= c) return 1;
    return rnd01() < exp(-(double)(c2 - c) / temp);
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) vs[l][i] = rndint(G);
    }
    set_all();
}

/* Simulated annealing on the current group and K. Returns final cost (0 = valid lift). */
static long anneal(long iters, long patience, double until) {
    long cost = total_cost(accR);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    uint32_t full = (1u << (2 * K)) - 1u;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > until) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters) + 0.3;
        long c2;
        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tmp;
            set_dart(l, i1, lay[l][i1], vs[l][i1]);
            set_dart(l, i2, lay[l][i2], vs[l][i2]);
            c2 = total_cost(trialR);
            if (accept(c2, cost, temp)) {
                cost = c2;
                memcpy(accR, trialR, sizeof(uint32_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tmp;
                set_dart(l, i1, lay[l][i1], vs[l][i1]);
                set_dart(l, i2, lay[l][i2], vs[l][i2]);
            }
        } else {
            int l = -1, i = -1;
            if (rnd01() < 0.4) {
                int u = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int v = rndint(N);
                    if (accR[v] != full) { u = v; break; }
                }
                if (u >= 0) {
                    int block = u / G;
                    l = rndint(d);
                    if (block < K) {
                        i = block;
                    } else {
                        for (int q = 0; q < K; q++)
                            if (lay[l][q] == block - K) { i = q; break; }
                    }
                }
            }
            if (i < 0) {
                l = rndint(d);
                i = rndint(K);
            }
            int old = vs[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            vs[l][i] = nw;
            set_dart(l, i, lay[l][i], nw);
            c2 = total_cost(trialR);
            if (accept(c2, cost, temp)) {
                cost = c2;
                memcpy(accR, trialR, sizeof(uint32_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                vs[l][i] = old;
                set_dart(l, i, lay[l][i], old);
            }
        }
    }
    return cost;
}

/* ---- group sampling ---- */
static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

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

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int sample_group(long target, int *om, int *ok2, int *orr) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2S[rndint(20)];
        long mm = (target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        int r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (mm <= 2) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            long rr = mm - 1;
            if (gcdl(rr, mm) == 1 && powmod(rr, 2, mm) == 1 % mm) r = (int)rr;
        } else {
            for (int c = 0; c < 60; c++) {
                long cc = 2 + rndint((int)(mm - 2));
                if (gcdl(cc, mm) == 1 && powmod(cc, k2, mm) == 1 % mm) { r = (int)cc; break; }
            }
        }
        if (r < 0) continue;
        *om = (int)mm;
        *ok2 = k2;
        *orr = r;
        return 1;
    }
    return 0;
}

/* ---- bandit over base sizes ---- */
static const int KS[6] = {1, 2, 3, 4, 5, 6};
static long trials[MAXK + 1], wins[MAXK + 1];

static int pick_k(void) {
    if (rnd01() < 0.2) return KS[rndint(6)];
    int bk = KS[0];
    double bv = -1.0;
    for (int i = 0; i < 6; i++) {
        int k = KS[i];
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* ---- best result ---- */
static int bestN = 0;
static int bK, bG, bm, bk2, br;
static int bl[MAXD][MAXK], bs[MAXD][MAXK];

static void print_best(void) {
    K = bK;
    G = bG;
    set_group(bm, bk2, br);
    N = 2 * K * G;
    memcpy(lay, bl, sizeof lay);
    memcpy(vs, bs, sizeof vs);
    set_all();
    printf("%d %ld\n", N, (long)K * G * d);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, nbr[l][v]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    deadline = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    long goal = 2L * d;

    while (now() < deadline) {
        if (goal > cap) goal = cap;
        int k = pick_k();
        long target = goal / (2L * k) + rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) {
            goal = goal * 99 / 100 + 1;
            continue;
        }
        long Nl = 2L * k * m * k2;
        if (Nl > cap) continue;
        if (Nl <= bestN) {
            long g2 = (long)bestN * 102 / 100 + 1;
            if (g2 > goal) goal = g2;
            continue;
        }
        set_group(m, k2, r);
        K = k;
        G = m * k2;
        N = (int)Nl;
        trials[k]++;
        random_init();
        long c = anneal(ITERS, PATIENCE, deadline);
        if (c == 0) {
            wins[k]++;
            bestN = N;
            bK = K;
            bG = G;
            bm = m;
            bk2 = k2;
            br = r;
            memcpy(bl, lay, sizeof lay);
            memcpy(bs, vs, sizeof vs);
            long g2 = (long)N * 104 / 100 + 1;
            if (g2 > goal) goal = g2;
        } else {
            long g2 = (long)bestN * 102 / 100 + 1;
            long g3 = goal * 99 / 100;
            goal = g2 > g3 ? g2 : g3;
        }
    }

    if (bestN == 0) printf("0 0\n");
    else print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent program).
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

    # K_{d,d} has diameter 2 and is the safe fallback for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions.
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

    # C bi-Cayley lift annealer uses the remaining time.
    total = max(1.0, 0.8 * time_limit - 4.0)
    left = total - (time.monotonic() - t0)
    if left >= 1.0:
        budget = round(left, 2)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], timeout=budget + 30.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
