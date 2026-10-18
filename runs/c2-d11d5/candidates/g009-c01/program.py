"""Bi-Cayley lift search in C over semidirect groups Z_m x| Z_k2 with base sizes k <= 6.

The C engine samples a base size k and a group, anneals layer permutations and voltages on a
bitset distance cost, and ratchets the target order up after each success. Left multiplication
by the group is an automorphism, so it is enough to check the distance from one representative
per block. Every returned graph is checked with lib.is_valid. K_{d,d} or an exact
construction is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 6
#define MAXD 16
#define MAXN 40000
#define PATIENCE 4000

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

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

/* Current lift: group Z_M x| Z_K2 (element a*K2+b), base sizes K per side, G = M*K2. */
static int K, M, K2, G, N;
static int pw[64];
static int *nbr = NULL, *lay = NULL, *sv = NULL;
static uint32_t *cur = NULL, *nxt = NULL;

/* (a,b)*(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a1 = x / K2, b1 = x % K2, a2 = y / K2, b2 = y % K2;
    long t = (long)pw[b1] * a2 % M;
    int a = (int)((a1 + t) % M);
    int b = (b1 + b2) % K2;
    return a * K2 + b;
}

/* Vertices: A block i -> i*G+g, B block p -> (K+p)*G+h. Dart (l,i): A_{i,g} ~ B_{p,g*s}. */
static void set_dart(int l, int i) {
    int p = lay[l * K + i], s = sv[l * K + i];
    int A0 = i * G, B0 = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        int A = A0 + g, B = B0 + h;
        nbr[(size_t)A * d + l] = B;
        nbr[(size_t)B * d + l] = A;
    }
}

/* Sum over all vertices v of the number of block representatives at distance > D from v. */
static long eval_cost(void) {
    int full = 2 * K;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < full; b++) cur[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nb[l]];
            nxt[v] = x;
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long c = 0;
    for (int v = 0; v < N; v++) c += full - __builtin_popcount(cur[v]);
    return c;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l * K + i];
            lay[l * K + i] = lay[l * K + j];
            lay[l * K + j] = t;
        }
        for (int i = 0; i < K; i++) sv[l * K + i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static int bestN = 0, bestK = 0;
static int *bestNbr = NULL;

static void record_best(void) {
    if (N <= bestN) return;
    free(bestNbr);
    bestNbr = malloc(sizeof(int) * (size_t)N * d);
    memcpy(bestNbr, nbr, sizeof(int) * (size_t)N * d);
    bestN = N;
    bestK = K;
}

static void print_best(void) {
    if (bestN <= 0 || !bestNbr) {
        printf("0 0\n");
        return;
    }
    int half = bestN / 2;
    int *eu = malloc(sizeof(int) * (size_t)half * d);
    int *ev = malloc(sizeof(int) * (size_t)half * d);
    int cnt = 0;
    for (int v = 0; v < half; v++) {
        for (int l = 0; l < d; l++) {
            int u = bestNbr[(size_t)v * d + l];
            int dup = 0;
            for (int l2 = 0; l2 < l; l2++)
                if (bestNbr[(size_t)v * d + l2] == u) { dup = 1; break; }
            if (!dup) {
                eu[cnt] = v;
                ev[cnt] = u;
                cnt++;
            }
        }
    }
    printf("%d %d\n", bestN, cnt);
    for (int k = 0; k < cnt; k++) printf("%d %d\n", eu[k], ev[k]);
    free(eu);
    free(ev);
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

/* Anneal the current group until cost 0 (returns 1) or the deadline passes (returns 0). */
static int search_group(double until) {
    N = 2 * K * G;
    if (N > MAXN) return 0;
    nbr = malloc(sizeof(int) * (size_t)N * d);
    lay = malloc(sizeof(int) * K * d);
    sv = malloc(sizeof(int) * K * d);
    cur = malloc(sizeof(uint32_t) * N);
    nxt = malloc(sizeof(uint32_t) * N);
    int found = 0;
    random_state();
    long cost = eval_cost();
    long bestc = cost, last = 0;
    for (long it = 1;; it++) {
        if (cost == 0) { found = 1; break; }
        if ((it & 31) == 0 && now() > until) break;
        if (it - last > PATIENCE) {
            random_state();
            cost = eval_cost();
            bestc = cost;
            last = it;
            continue;
        }
        double T = 0.2 + 0.01 * (double)cost;
        if (K >= 2 && rndint(100) < 30) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int *a = &lay[l * K + i1], *b = &lay[l * K + i2];
            int t = *a; *a = *b; *b = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = eval_cost();
            if (accept(c2 - cost, T)) {
                cost = c2;
            } else {
                t = *a; *a = *b; *b = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int idx = l * K + i;
            int old = sv[idx];
            int nw = rndint(G);
            if (nw == old) continue;
            sv[idx] = nw;
            set_dart(l, i);
            long c2 = eval_cost();
            if (accept(c2 - cost, T)) {
                cost = c2;
            } else {
                sv[idx] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = it; }
    }
    if (found) record_best();
    free(nbr); free(lay); free(sv); free(cur); free(nxt);
    nbr = lay = sv = NULL;
    cur = nxt = NULL;
    return found;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal0]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double goal0 = argc > 5 ? atof(argv[5]) : 100.0;
    double deadline = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    static const int K2s[17] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    double goal = goal0;
    while (now() < deadline - 0.3) {
        K = 1 + rndint(MAXK);
        K2 = K2s[rndint(17)];
        int Mb = (int)ceil(goal / (2.0 * K * K2));
        M = Mb + rndint(3);
        if (M < 2) M = 2;
        G = M * K2;
        N = 2 * K * G;
        if (N > MAXN) {
            goal *= 0.9;
            continue;
        }
        int r = 1;
        if (K2 > 1 && M > 2 && rnd01() < 0.5) {
            for (int t = 0; t < 300; t++) {
                int c = 2 + rndint(M - 2);
                if (gcdl(c, M) == 1 && powmodl(c, K2, M) == 1 % M) {
                    r = c;
                    break;
                }
            }
        }
        pw[0] = 1 % M;
        for (int t = 1; t < K2; t++) pw[t] = (int)((long)pw[t - 1] * r % M);

        double remain = deadline - now();
        double slice = remain / 5.0;
        if (slice < 2.5) slice = 2.5;
        if (slice > remain) slice = remain;
        if (search_group(now() + slice)) {
            goal = N * 1.02 + 1.0;
        } else {
            double g2 = goal * 0.99;
            goal = g2 > goal0 ? g2 : goal0;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept from the parent program).
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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main phase: C bi-Cayley lift search, using most of the budget.
    budget = 0.8 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget >= 3.0 and d <= 16:
        try:
            goal0 = float(max(best_n + 2, 20))
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), goal0],
                             timeout=budget + 20.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
