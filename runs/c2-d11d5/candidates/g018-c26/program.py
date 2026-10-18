"""Bi-Cayley voltage-lift search in C (simulated annealing over permutations and voltages of
semidirect products Z_m x| Z_k2), with exact PG(2,q) / Araujo-Lopez / W(q) constructions as
starting candidates. Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift search.
 * Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h.
 * Layer l: A_{i,g} ~ B_{sig[l][i], g*S[l][i]}, with sig[l] a permutation. Every vertex has
 * degree d (duplicate edges are merged on output, which never changes distances).
 * Left translation is an automorphism, so the graph has diameter <= D iff every block
 * representative reaches all vertices within D. The cost counts missing (vertex, rep) pairs.
 * Usage: prog d D seed time_limit   (stdin is ignored)
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 12
#define MAXK2 64
#define MAXN 40000
#define PATIENCE 4000L
#define KMIN 2
#define KMAX 8

static int d, D;
static uint64_t rs = 88172645463325252ULL;

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

/* ---- group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e) ---- */
static int gm, gk2, gG;
static long gpw[MAXK2];

static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    gG = m * k2;
    gpw[0] = 1 % m;
    for (int b = 1; b < k2; b++) gpw[b] = gpw[b - 1] * r % m;
}

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    return (int)(((a + gpw[b] * c) % gm) * gk2 + (b + e) % gk2);
}

static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long c = (gm - (gpw[nb] * a) % gm) % gm;
    return (int)(c * gk2 + nb);
}

static long pmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int sample_group(int Gt, int *om, int *ok2, int *or_) {
    static const int k2s[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    int nk = (int)(sizeof k2s / sizeof k2s[0]);
    for (int att = 0; att < 200; att++) {
        int k2 = k2s[rndint(nk)];
        int m = (Gt + k2 - 1) / k2;
        if (m < 3) m = 3;
        int r = 1;
        if (k2 > 1 && rnd01() >= 0.25) {
            int found = 0;
            for (int tr = 0; tr < 80 && !found; tr++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) == 1 && pmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                }
            }
            if (!found) continue;
        }
        *om = m;
        *ok2 = k2;
        *or_ = r;
        return 1;
    }
    return 0;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* ---- lift state ---- */
static int K, G;
static int sig[MAXD][MAXK], sinv[MAXD][MAXK], S[MAXD][MAXK];
static int nbr[MAXN * MAXD];
static uint64_t bufA[MAXN], bufB[MAXN];
static uint64_t *fin;

static int bm, bk2, br, bK;
static int bsig[MAXD][MAXK], bS[MAXD][MAXK];
static long bestN = 0;

static void set_perm_inv(int l) {
    for (int i = 0; i < K; i++) sinv[l][sig[l][i]] = i;
}

static void swap_sig(int l, int i1, int i2) {
    int t = sig[l][i1];
    sig[l][i1] = sig[l][i2];
    sig[l][i2] = t;
    sinv[l][sig[l][i1]] = i1;
    sinv[l][sig[l][i2]] = i2;
}

static void recompute_layer(int l) {
    for (int i = 0; i < K; i++) {
        int s = S[l][i], tgt = K + sig[l][i];
        for (int g = 0; g < G; g++) nbr[(i * G + g) * d + l] = tgt * G + gmul(g, s);
    }
    for (int j = 0; j < K; j++) {
        int i = sinv[l][j], s = S[l][i], si = ginv(s);
        for (int h = 0; h < G; h++) nbr[((K + j) * G + h) * d + l] = i * G + gmul(h, si);
    }
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < K; i++) sig[l][i] = p[i];
        set_perm_inv(l);
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        recompute_layer(l);
    }
}

/* Number of missing (vertex, representative) pairs; 0 means the lift is valid. */
static int evaluate(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    int NN = 2 * K * G;
    for (int v = 0; v < NN; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] |= 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            uint64_t x = cur[v];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nb[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long miss = 0;
    for (int v = 0; v < NN; v++) miss += 2 * K - __builtin_popcountll(cur[v]);
    fin = cur;
    return (int)miss;
}

static int pick_bad(void) {
    int NN = 2 * K * G;
    for (int tries = 0; tries < 40; tries++) {
        int v = rndint(NN);
        if (__builtin_popcountll(fin[v]) < 2 * K) return v;
    }
    return -1;
}

static int sa_chain(double deadline) {
    random_init();
    int cost = evaluate();
    if (cost == 0) return 1;
    int best = cost;
    long last = 0;
    for (long t = 0;; t++) {
        if ((t & 31) == 0 && now() > deadline) return 0;
        if (t - last > PATIENCE) return 0;
        double base = best > 0 ? best : 1.0;
        double T = 0.3 + 0.2 * base * exp(-(double)(t - last) / 500.0);
        int l = rndint(d);
        int kind = 0, i1 = 0, i2 = 0, oldS = 0;
        if (K >= 2 && rnd01() < 0.25) {
            kind = 1;
            i1 = rndint(K);
            i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_sig(l, i1, i2);
        } else {
            int v = pick_bad();
            if (v >= 0 && rnd01() < 0.5) {
                int blk = v / G;
                i1 = (blk < K) ? blk : sinv[l][blk - K];
            } else {
                i1 = rndint(K);
            }
            oldS = S[l][i1];
            int ns = rndint(G);
            if (ns == oldS) continue;
            S[l][i1] = ns;
        }
        recompute_layer(l);
        int c2 = evaluate();
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                last = t;
            }
            if (cost == 0) return 1;
        } else {
            if (kind == 1) swap_sig(l, i1, i2);
            else S[l][i1] = oldS;
            recompute_layer(l);
        }
    }
}

static int sa_run(double deadline) {
    while (now() < deadline)
        if (sa_chain(deadline)) return 1;
    return 0;
}

static void emit_best(void) {
    set_group(bm, bk2, br);
    K = bK;
    G = gG;
    memcpy(sig, bsig, sizeof sig);
    memcpy(S, bS, sizeof S);
    for (int l = 0; l < d; l++) {
        set_perm_inv(l);
        recompute_layer(l);
    }
    if (evaluate() != 0) {
        printf("0 0\n");
        return;
    }
    int half = K * G;
    long m = 0;
    for (int v = 0; v < half; v++)
        for (int l = 0; l < d; l++) {
            int w = nbr[v * d + l], dup = 0;
            for (int l2 = 0; l2 < l && !dup; l2++)
                if (nbr[v * d + l2] == w) dup = 1;
            if (!dup) m++;
        }
    printf("%d %ld\n", 2 * half, m);
    for (int v = 0; v < half; v++)
        for (int l = 0; l < d; l++) {
            int w = nbr[v * d + l], dup = 0;
            for (int l2 = 0; l2 < l && !dup; l2++)
                if (nbr[v * d + l2] == w) dup = 1;
            if (!dup) printf("%d %d\n", v, w);
        }
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
    double t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;

    int trials[KMAX + 1], wins[KMAX + 1];
    for (int k = 0; k <= KMAX; k++) {
        trials[k] = 0;
        wins[k] = 0;
    }
    double floor_n = 4.0 * d;
    double target = floor_n;

    while (now() < t_end && bestN < cap) {
        if (target > (double)cap) target = (double)cap;
        int Kc = KMIN;
        if (rnd01() < 0.2) {
            Kc = KMIN + rndint(KMAX - KMIN + 1);
        } else {
            double bv = -1.0;
            for (int k = KMIN; k <= KMAX; k++) {
                double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.05 * rnd01();
                if (v > bv) {
                    bv = v;
                    Kc = k;
                }
            }
        }
        int Gt = (int)ceil(target / (2.0 * Kc)) + rndint(3);
        int m, k2, r;
        if (!sample_group(Gt, &m, &k2, &r)) continue;
        long Gg = (long)m * k2;
        long N = 2L * Kc * Gg;
        if (N > cap) {
            target -= 2.0 * Kc;
            if (target < floor_n) target = floor_n;
            continue;
        }
        if (N <= bestN) {
            target = bestN * 1.01 + 1.0;
            continue;
        }
        trials[Kc]++;
        double remain = t_end - now();
        double slice = remain * 0.2;
        if (slice < 1.5) slice = 1.5;
        if (slice > 8.0) slice = 8.0;
        double dl = now() + slice;
        if (dl > t_end) dl = t_end;
        set_group(m, k2, r);
        K = Kc;
        G = gG;
        if (sa_run(dl)) {
            wins[Kc]++;
            bestN = N;
            bm = m;
            bk2 = k2;
            br = r;
            bK = Kc;
            memcpy(bsig, sig, sizeof sig);
            memcpy(bS, S, sizeof S);
            target = (double)N * 1.02 + 1.0;
        } else {
            double lo = bestN * 1.01 + 1.0;
            if (lo < floor_n) lo = floor_n;
            target *= 0.995;
            if (target < lo) target = lo;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    emit_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (used as candidates and as calibration shortcuts).
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions first.
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

    # Main search: bi-Cayley lift annealing in C, using most of the time budget.
    budget = 0.88 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget >= 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 15.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
