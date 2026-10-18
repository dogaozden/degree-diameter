"""Bi-Cayley lift search with a symmetry-reduced C annealer, plus exact small constructions.

New in this version: the whole lift search (group sampling, voltage/permutation annealing and
the distance check) runs in C. The check uses left-translation symmetry of semidirect-product
bi-Cayley graphs: vertex (block i, g) is mapped to (block i, e) by left multiplication, so
diameter <= D only needs distances from the 2k block representatives. Each vertex carries a
bitmask of which representatives it reaches within D steps, which makes one evaluation
O(D * d * N) with tiny constants.

Every returned graph is checked with lib.is_valid. A projective plane, Araujo-Pardo-Lopez or
K_{d,d} fallback is always kept.
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

#define MAXD 32
#define MAXK 4
#define MAXG 8192
#define MAXN 16384
#define MAXP 32
#define PEN 1000L
#define ITERS 3000000L
#define PATIENCE 5000L

/* Usage: prog d D seed time_limit [goal]
 * Output: "n m" + edges of the best valid bi-Cayley lift found, or "0 0".
 */

static int d, D;
static double t_end;
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
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Current group Z_M x| Z_K2 (element a*K2+b), with pw[b] = r^b mod M. */
static int M, K2, G, pw[MAXP];
/* Current lift: k A-blocks and k B-blocks of size G. */
static int k, N;
static int lay[MAXD][MAXK], invlay[MAXD][MAXK], S[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static unsigned char R[MAXN], RA[MAXN], RB[MAXN];
static int bestN = 0;
static int bestnbr[MAXD][MAXN];

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int t = (int)(((long)pw[b] * c + a) % M);
    return t * K2 + (b + e) % K2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long t = (long)pw[nb] * a % M;
    int c = (int)((M - t) % M);
    return c * K2 + nb;
}

/* A-block i (vertices i*G+g) joins B-block p ((k+p)*G+h) with voltage s: g ~ g*s. */
static void set_dart(int l, int i, int p, int s) {
    int sinv = ginv(s);
    int ba = i * G, bb = (k + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ba + g] = bb + gmul(g, s);
        nbr[l][bb + g] = ba + gmul(g, sinv);
    }
}

/* Swap the B-partners of A-blocks i1 and i2 in layer l (applying it twice reverts it). */
static void do_swap(int l, int i1, int i2) {
    int p1 = lay[l][i1], p2 = lay[l][i2];
    lay[l][i1] = p2;
    lay[l][i2] = p1;
    invlay[l][p1] = i2;
    invlay[l][p2] = i1;
    set_dart(l, i1, p2, S[l][i1]);
    set_dart(l, i2, p1, S[l][i2]);
}

/* Symmetry-reduced check: left translations are automorphisms, so it is enough that every
 * block representative reaches every vertex within D steps. Returns the number of missing
 * (vertex, representative) pairs and fills R[v] with the reached-representative bitmask. */
static int reach_cost(void) {
    unsigned char *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[b * G] = (unsigned char)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            unsigned char x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        unsigned char *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    int unr = 0;
    for (int v = 0; v < N; v++) {
        R[v] = cur[v];
        unr += 2 * k - __builtin_popcount(cur[v]);
    }
    return unr;
}

/* Number of darts repeating an earlier (block, partner, voltage) key. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < k; i++)
        for (int l = 1; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l2][i] == lay[l][i] && S[l2][i] == S[l][i]) {
                    c++;
                    break;
                }
    return c;
}

static long evalc(void) {
    return (long)reach_cost() + PEN * (long)dupcount();
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            lay[l][i] = perm[i];
            invlay[l][perm[i]] = i;
        }
        for (int i = 0; i < k; i++) S[l][i] = rndint(G);
        for (int i = 0; i < k; i++) set_dart(l, i, lay[l][i], S[l][i]);
    }
}

/* Simulated annealing on voltages and layer permutations. Returns 1 on a valid lift. */
static int anneal(void) {
    long cost = evalc();
    long best = cost, last = 0;
    int full = (1 << (2 * k)) - 1;
    for (long t = 0; t < ITERS; t++) {
        if (cost == 0) return 1;
        if ((t & 31) == 0 && now() > t_end) break;
        if (t - last > PATIENCE) break;
        double temp = 0.3 + 0.02 * (double)cost;
        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            do_swap(l, i1, i2);
            long c2 = evalc();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                do_swap(l, i1, i2);
            }
            continue;
        }
        int l = rndint(d);
        int i = rndint(k);
        if (rnd01() < 0.4) {
            for (int tries = 0; tries < 30; tries++) {
                int w = rndint(N);
                if (R[w] == full) continue;
                int blk = w / G;
                i = (blk < k) ? blk : invlay[l][blk - k];
                break;
            }
        }
        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i, lay[l][i], nw);
        long c2 = evalc();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i, lay[l][i], old);
        }
    }
    return cost == 0;
}

static void save_best(void) {
    bestN = N;
    for (int l = 0; l < d; l++) memcpy(bestnbr[l], nbr[l], sizeof(int) * (size_t)N);
}

static void print_best(void) {
    if (bestN <= 0) {
        printf("0 0\n");
        return;
    }
    long m = 0;
    for (int v = 0; v < bestN; v++)
        for (int l = 0; l < d; l++) {
            int u = bestnbr[l][v];
            if (u <= v) continue;
            int dup = 0;
            for (int l2 = 0; l2 < l && !dup; l2++)
                if (bestnbr[l2][v] == u) dup = 1;
            if (!dup) m++;
        }
    printf("%d %ld\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        for (int l = 0; l < d; l++) {
            int u = bestnbr[l][v];
            if (u <= v) continue;
            int dup = 0;
            for (int l2 = 0; l2 < l && !dup; l2++)
                if (bestnbr[l2][v] == u) dup = 1;
            if (!dup) printf("%d %d\n", v, u);
        }
}

static const int K2_CHOICES[] = {1, 1, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12, 16};
#define NK2 14

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Pick Z_m x| Z_k2 with m*k2 >= target (r^k2 = 1 mod m, gcd(r, m) = 1). */
static int sample_group(long target) {
    for (int tries = 0; tries < 100; tries++) {
        int k2 = K2_CHOICES[rndint(NK2)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > MAXG) continue;
        long r = 1;
        if (k2 > 1 && m > 2 && rnd01() < 0.85) {
            for (int t = 0; t < 80; t++) {
                long c = 1 + rndint((int)(m - 1));
                if (gcdl(c, m) == 1 && powmodl(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }
        M = (int)m;
        K2 = k2;
        G = M * K2;
        for (int b = 0; b < K2; b++) pw[b] = (int)powmodl(r, b, m);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long goal0 = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.97 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    double goal = goal0 > 2 ? (double)goal0 : 2.0 * d;
    long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < t_end) {
        if (goal > (double)cap) goal = (double)cap;
        int kk;
        if (rnd01() < 0.2) {
            kk = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            kk = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    kk = c;
                }
            }
        }
        long target = (long)(goal / (2.0 * kk)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target)) continue;
        k = kk;
        N = 2 * k * G;
        if (N > cap) {
            goal *= 0.995;
            continue;
        }
        if (N <= bestN) continue;

        trials[kk]++;
        random_lift();
        if (anneal()) {
            wins[kk]++;
            save_best();
            goal = N * 1.04 + 1.0;
        } else {
            double f = bestN * 1.02;
            double g2 = goal * 0.99;
            goal = g2 > f ? g2 : f;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
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

    # Main search: the C engine runs the bi-Cayley lift search for the remaining budget.
    budget = final - time.monotonic() - 1.0
    if d >= 2 and budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                             stdin_graph=None, timeout=budget + 15.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
