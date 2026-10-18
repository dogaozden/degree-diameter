"""Program: bi-Cayley voltage-lift annealing in C over semidirect products Z_m x| Z_k2,
with base sizes k = 1..8 and d layers. Each candidate is scored by the number of unreached
(vertex, base-block) pairs, computed with 64-bit bitsets. Exact constructions (projective
planes, Araujo-Pardo-Lopez, generalized quadrangle) are used where they apply. The full
K_{d,d} is the fallback, and every result is checked with lib.is_valid before return.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Voltage-lift annealer over semidirect groups.
 * Usage: prog d D seed time_limit goal < /dev/null
 * Output: "n m" then m edges of the best valid d-regular bipartite lift found, or "0 0".
 *
 * Vertices: A-block i (0..k-1) occupies i*G..i*G+G-1, B-block j occupies (k+j)*G..
 * Group elements x = a*k2+b with (a,b)*(c,e) = ((a + r^b c) mod m, (b+e) mod k2).
 * Layer l pairs A-block i with B-block perm[l][i] through voltage S[l][i]:
 *   A(i,g) ~ B(perm,g*s).
 * Left multiplication by G is an automorphism, so the diameter is <= D iff every vertex
 * reaches every block representative (identity element) within D steps.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXL 32
#define MAXK 8
#define MAXK2 16
#define MAXV 20480
#define ANNEAL_ITERS 3000

static int d, D;
static uint64_t rs = 88172645463325252ULL;

typedef struct {
    int k, k2, m, r, G, N;
    int pw[MAXK2];
    int perm[MAXL][MAXK];
    int S[MAXL][MAXK];
} Cfg;

static int nbr[MAXL][MAXV];
static uint64_t bufA[MAXV], bufB[MAXV];

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, int e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gmul(const Cfg *c, int x, int y) {
    int a = x / c->k2, b = x % c->k2;
    int e = y / c->k2, f = y % c->k2;
    int aa = (int)(((long)c->pw[b] * e + a) % c->m);
    return aa * c->k2 + (b + f) % c->k2;
}

static void build_layer(const Cfg *c, int l) {
    int k = c->k, G = c->G;
    for (int i = 0; i < k; i++) {
        int j = c->perm[l][i], s = c->S[l][i];
        int bA = i * G, bB = (k + j) * G;
        for (int g = 0; g < G; g++) {
            int h = gmul(c, g, s);
            nbr[l][bA + g] = bB + h;
            nbr[l][bB + h] = bA + g;
        }
    }
}

/* Cost = unreached (vertex, representative) pairs + 1000 * duplicate darts. Zero means valid. */
static long evaluate(const Cfg *c) {
    int k = c->k, N = c->N, G = c->G;
    for (int l = 0; l < d; l++) build_layer(c, l);
    long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (c->perm[l][i] == c->perm[l2][i] && c->S[l][i] == c->S[l2][i]) dups++;

    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * k - __builtin_popcountll(cur[v]);
    return unr + 1000L * dups;
}

static void random_cfg(Cfg *c, int k, int Gt) {
    static const int K2[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    int k2 = K2[rndint(11)];
    int m = (Gt + k2 - 1) / k2;
    if (m < 2) m = 2;
    c->k = k;
    c->k2 = k2;
    c->m = m;
    c->G = m * k2;
    c->N = 2 * k * c->G;
    c->r = 1;
    if (k2 > 1 && m > 2) {
        for (int t = 0; t < 300; t++) {
            int cc = 2 + rndint(m - 2);
            if (gcd_i(cc, m) == 1 && powmod(cc, k2, m) == 1 % m) {
                c->r = cc;
                break;
            }
        }
    }
    c->pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) c->pw[b] = (int)((long)c->pw[b - 1] * c->r % m);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) c->perm[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = c->perm[l][i];
            c->perm[l][i] = c->perm[l][j];
            c->perm[l][j] = t;
        }
        for (int i = 0; i < k; i++) c->S[l][i] = rndint(c->G);
    }
}

static void swap_int(int *a, int *b) {
    int t = *a;
    *a = *b;
    *b = t;
}

static long anneal(Cfg *c, int iters, double deadline) {
    long cost = evaluate(c);
    double T0 = 1.0 + 0.02 * (double)cost, T1 = 0.3;
    int k = c->k, G = c->G;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (now() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / iters);
        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i) i2++;
            swap_int(&c->perm[l][i], &c->perm[l][i2]);
            long nc = evaluate(c);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                swap_int(&c->perm[l][i], &c->perm[l][i2]);
            }
        } else {
            int l = rndint(d), i = rndint(k);
            int old = c->S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            c->S[l][i] = nw;
            long nc = evaluate(c);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                c->S[l][i] = old;
            }
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit goal\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double goal = atof(argv[5]);
    if (d < 2 || d > MAXL || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t_end = now() + limit;
    if (goal < 2.0 * d) goal = 2.0 * d;
    int bestN = 0, bestE = 0;
    int *bu = NULL, *bv = NULL;

    while (now() < t_end) {
        int k = 1 + rndint(MAXK);
        int Gt = (int)ceil(goal / (2.0 * k)) + rndint(4);
        if (Gt < 2) Gt = 2;
        if (2 * k * Gt > MAXV - 400) Gt = (MAXV - 400) / (2 * k);
        Cfg c;
        random_cfg(&c, k, Gt);
        if (c.N > MAXV) continue;
        if (c.N <= bestN) {
            if (goal < bestN * 1.01) goal = bestN * 1.01;
            continue;
        }
        long cost = anneal(&c, ANNEAL_ITERS, t_end);
        if (cost == 0) {
            if (c.N > bestN) {
                evaluate(&c);
                int kg = c.k * c.G;
                int E = kg * d;
                int *nu = malloc(sizeof(int) * (size_t)E);
                int *nv = malloc(sizeof(int) * (size_t)E);
                if (nu && nv) {
                    int e = 0;
                    for (int u = 0; u < kg; u++)
                        for (int l = 0; l < d; l++) {
                            nu[e] = u;
                            nv[e] = nbr[l][u];
                            e++;
                        }
                    free(bu);
                    free(bv);
                    bu = nu;
                    bv = nv;
                    bestN = c.N;
                    bestE = E;
                } else {
                    free(nu);
                    free(nv);
                }
            }
            goal = bestN * 1.01;
        } else {
            double lo = bestN > 0 ? bestN * 1.002 : 0.0;
            double g2 = goal * 0.98;
            goal = g2 > lo ? g2 : lo;
            if (goal < 2.0 * d) goal = 2.0 * d;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestE);
    for (int e = 0; e < bestE; e++) printf("%d %d\n", bu[e], bv[e]);
    free(bu);
    free(bv);
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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best[0]
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

    # Main search: C voltage-lift annealing over semidirect groups.
    total = max(1.0, 0.88 * time_limit - 2.0)
    remaining = t0 + total - time.monotonic()
    if remaining > 2.0:
        goal0 = int(0.2 * lib.moore_bound(d, D))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), goal0],
                             timeout=remaining + 15)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        best[0] = lib.haar_graph(d, range(d))
    return best[0]
