"""Bi-Cayley voltage-lift search in C over semidirect groups Z_m x| Z_k2.

Each candidate has 2k base vertices (k per side) and d layers, each a perfect matching between
the blocks, so every vertex has degree d. Vertices are block*G + g. The group acts by left
multiplication, so checking reachability from block representatives is enough for diameter D.
A C simulated annealer minimises unreached (vertex, representative) pairs. Exact constructions
(projective planes, Araujo-Pardo-Lopez, generalized quadrangle) are used when they apply, and
K_{d,d} is the fallback. Every result is checked with lib.is_valid.
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
#define MAXN 40000

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

/* Group Z_M x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int M, K2, GO, RR;
static int powr[64];
static int invT[MAXN];

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int a2 = (int)((a + (long long)powr[b] * c) % M);
    return a2 * K2 + (b + e) % K2;
}
static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int a2 = (int)((M - (long long)powr[nb] * a % M) % M);
    return a2 * K2 + nb;
}
static void setup_group(int m, int k2, int r) {
    M = m; K2 = k2; RR = r; GO = m * k2;
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    for (int x = 0; x < GO; x++) invT[x] = ginv(x);
}

static int try_group(long target, int *om, int *ok2, int *orr) {
    static const int K2s[20] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};
    for (int att = 0; att < 300; att++) {
        int k2 = K2s[rndint(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long r = 1;
        if (k2 > 1 && m > 2) {
            int ok = 0;
            for (int t = 0; t < 200 && !ok; t++) {
                r = 1 + rndint((int)(m - 1));
                if (gcdl(r, m) == 1 && powmod(r, k2, m) == 1 % m) ok = 1;
            }
            if (!ok) continue;
        }
        *om = (int)m; *ok2 = k2; *orr = (int)r;
        return 1;
    }
    return 0;
}

/* Lift state. Block i < K is an A-block, block K + p is a B-block. */
static int K, NV;
static int perm[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nb[MAXD][MAXN];
static uint64_t RA[MAXN], RB[MAXN];
static uint64_t full_mask;

static void set_pair(int l, int i) {
    int p = perm[l][i], s = S[l][i], si = invT[s];
    int ba = i * GO, bb = (K + p) * GO;
    for (int g = 0; g < GO; g++) {
        nb[l][ba + g] = bb + gmul(g, s);
        nb[l][bb + g] = ba + gmul(g, si);
    }
}
static void swap_perm(int l, int i1, int i2) {
    int t = perm[l][i1];
    perm[l][i1] = perm[l][i2];
    perm[l][i2] = t;
}

/* Unreached (vertex, representative) pairs plus a penalty for duplicate edges. */
static long eval_cost(void) {
    int N = NV;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * GO] |= 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nb[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long unset = 0;
    for (int v = 0; v < N; v++)
        unset += __builtin_popcountll(full_mask & ~cur[v]);
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (perm[l][i] == perm[l2][i] && S[l][i] == S[l2][i]) dup++;
    return unset + 4L * dup;
}

static long anneal(double dl, long patience) {
    long c = eval_cost();
    long best = c, last = 0, t = 0;
    double ts = now(), span = dl - ts;
    if (span < 1e-3) span = 1e-3;
    double temp = 1.0;
    while (c > 0) {
        if ((t & 31) == 0) {
            double nw = now();
            if (nw > dl) break;
            double frac = (nw - ts) / span;
            temp = 0.15 + 0.6 * (1.0 - frac);
        }
        if (t - last > patience) break;
        t++;
        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            swap_perm(l, i1, i2);
            set_pair(l, i1); set_pair(l, i2);
            long c2 = eval_cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / temp)) {
                c = c2;
                if (c < best) { best = c; last = t; }
            } else {
                swap_perm(l, i1, i2);
                set_pair(l, i1); set_pair(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i], cand = rndint(GO);
            if (cand == old) continue;
            S[l][i] = cand;
            set_pair(l, i);
            long c2 = eval_cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / temp)) {
                c = c2;
                if (c < best) { best = c; last = t; }
            } else {
                S[l][i] = old;
                set_pair(l, i);
            }
        }
    }
    return c;
}

static int pick_k(const int *wins, const int *trials) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    double bs = -1.0;
    int bk = 1;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.05 * rnd01();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

/* Best saved state. */
static long best_n = 0;
static int bK, bM, bK2, bR;
static int bperm[MAXD][MAXK], bS[MAXD][MAXK];

static void save_best(int m, int k2, int r) {
    best_n = NV;
    bK = K; bM = m; bK2 = k2; bR = r;
    memcpy(bperm, perm, sizeof(perm));
    memcpy(bS, S, sizeof(S));
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
    double tend = t0 + limit * 0.9 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    double goal = 2.0 * d + 1.0;
    int wins[MAXK + 1] = {0}, trials[MAXK + 1] = {0};

    while (now() < tend) {
        double rem = tend - now();
        int k = pick_k(wins, trials);
        long target = (long)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!try_group(target, &m, &k2, &r)) {
            goal = fmax(best_n * 1.01, goal * 0.99);
            continue;
        }
        setup_group(m, k2, r);
        K = k;
        NV = 2 * K * GO;
        if (NV > MAXN) {
            goal = fmax(best_n * 1.01, goal * 0.97);
            continue;
        }
        if (NV <= best_n) {
            goal = best_n * 1.02;
            continue;
        }
        trials[k]++;
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < K; i++) perm[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = t;
            }
            for (int i = 0; i < K; i++) S[l][i] = rndint(GO);
        }
        full_mask = (1ULL << (2 * K)) - 1;
        for (int l = 0; l < d; l++)
            for (int i = 0; i < K; i++) set_pair(l, i);
        double slice = rem < 6.0 ? rem : 6.0;
        long c = anneal(now() + slice, 3000);
        if (c == 0) {
            wins[k]++;
            save_best(m, k2, r);
            goal = NV * 1.06;
        } else {
            goal = fmax(best_n * 1.01, goal * 0.995);
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }

    setup_group(bM, bK2, bR);
    K = bK;
    NV = 2 * K * GO;
    memcpy(perm, bperm, sizeof(perm));
    memcpy(S, bS, sizeof(S));
    full_mask = (1ULL << (2 * K)) - 1;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_pair(l, i);
    if (eval_cost() != 0 || NV != best_n) { printf("0 0\n"); return 0; }

    int A = K * GO;
    long cnt = 0;
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++) {
            int w = nb[l][v], dup = 0;
            for (int l2 = 0; l2 < l; l2++) if (nb[l2][v] == w) { dup = 1; break; }
            if (!dup) cnt++;
        }
    printf("%d %ld\n", NV, cnt);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++) {
            int w = nb[l][v], dup = 0;
            for (int l2 = 0; l2 < l; l2++) if (nb[l2][v] == w) { dup = 1; break; }
            if (!dup) printf("%d %d\n", v, w);
        }
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

    # Bi-Cayley annealing in C. Leave room for compile time and Python validation.
    remaining = 0.75 * time_limit - 1.0 - (time.monotonic() - t0)
    if remaining > 1.0:
        c_limit = round(remaining, 2)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, c_limit],
                             stdin_graph=None, timeout=c_limit + 5.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
