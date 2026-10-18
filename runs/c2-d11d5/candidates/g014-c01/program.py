"""Bi-Cayley lift search in C, with a short exact-construction prelude.

Exact constructions (projective planes, Araujo-Pardo-Lopez, generalized quadrangle) run first
in Python. The main search then runs in one C engine. It samples semidirect groups
Z_m x| Z_k2, builds degree-d bi-Cayley lifts with k base vertices per side, and anneals layer
permutations and voltages until every vertex reaches every block representative within D steps.
Each success is verified on the explicit graph with bitsets before it is recorded.
K_{d,d} is the fallback, and every returned graph is checked with lib.is_valid.
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

#define MAXK 8
#define MAXN 12000
#define MAXD 16
#define MAXE 200000
#define PEN 1000L

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Current group Z_M x| Z_K2 with r-power table, base blocks K, group order G. */
static int K, G, M, K2;
static int pw[32];

static int pi_[MAXD][MAXK];      /* layer l: A block i -> B block pi_[l][i] */
static int sv[MAXD][MAXK];       /* voltage of (l, i) */
static int nb[MAXN * MAXD];      /* nb[v*d + l] = neighbour of v in layer l */
static uint64_t bufA[MAXN], bufB[MAXN];
static uint64_t *rcur;
static int ea[MAXE], eb[MAXE];
static long be = 0;
static int bestN = 0;

static int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int t = (a + (int)((long)pw[b] * c % M)) % M;
    int f = b + e;
    if (f >= K2) f -= K2;
    return t * K2 + f;
}

/* Rewrite all neighbours of layer l for A block i (and the B block it points to). */
static void set_dart(int l, int i) {
    int j = pi_[l][i], s = sv[l][i];
    int Ai = i * G, Bj = (K + j) * G;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        int a = Ai + g, b = Bj + h;
        nb[a * d + l] = b;
        nb[b * d + l] = a;
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (pi_[l][i] == pi_[l2][i] && sv[l][i] == sv[l2][i]) c++;
    return c;
}

/* Cost = unreached (vertex, block-representative) pairs + penalty * duplicate darts. */
static long evaluate(void) {
    int N = 2 * K * G;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(long)b * G] = 1ULL << b;
    for (int s = 0; s < D; s++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            const int *p = nb + (long)v * d;
            for (int l = 0; l < d; l++) x |= cur[p[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    rcur = cur;
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += 2 * K - __builtin_popcountll(cur[v]);
    return unreached + PEN * (long)dupcount();
}

static void random_start(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            pi_[l][i] = perm[i];
            sv[l][i] = rndint(G);
            set_dart(l, i);
        }
    }
}

/* Choose a random semidirect group with order about target and 2*K*G <= MAXN. */
static int setup_group(int target) {
    static const int K2s[] = {1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 8, 10, 12};
    for (int att = 0; att < 60; att++) {
        int k2 = K2s[rndint(13)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = -1;
        if (k2 == 1) {
            r = 1 % m;
        } else {
            if (rndint(3) == 0) {
                int c = m - 1;
                if (c >= 1 && gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) r = c;
            }
            for (int t = 0; t < 300 && r < 0; t++) {
                int c = 1 + rndint(m - 1);
                if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) r = c;
            }
        }
        if (r < 0) continue;
        if (2 * K * (m * k2) > MAXN) continue;
        M = m;
        K2 = k2;
        G = m * k2;
        pw[0] = 1 % m;
        for (int t = 1; t < K2; t++) pw[t] = (int)((long)pw[t - 1] * r % m);
        return 1;
    }
    return 0;
}

/* Simulated annealing on permutations and voltages. Returns final cost (0 = success). */
static long anneal(double deadline, int maxit, int patience) {
    random_start();
    long cost = evaluate();
    long best = cost;
    int last = 0;
    double c0 = cost > 0 ? (double)cost : 1.0;
    int N = 2 * K * G;
    uint64_t full = (1ULL << (2 * K)) - 1;
    for (int it = 0; it < maxit && cost > 0; it++) {
        if ((it & 31) == 0 && now() > deadline) break;
        if (it - last > patience) break;
        double frac = 1.0 - (double)it / maxit;
        double temp = 0.02 * c0 * frac + 0.3;
        if (K >= 2 && rndint(10) < 2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = pi_[l][i1];
            pi_[l][i1] = pi_[l][i2];
            pi_[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = evaluate();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = it; }
            } else {
                t = pi_[l][i1];
                pi_[l][i1] = pi_[l][i2];
                pi_[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            for (int tr = 0; tr < 16; tr++) {
                int v = rndint(N);
                if (rcur[v] != full) {
                    int b = v / G;
                    if (b < K) {
                        i = b;
                    } else {
                        for (int q = 0; q < K; q++)
                            if (pi_[l][q] == b - K) { i = q; break; }
                    }
                    break;
                }
            }
            int old = sv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            set_dart(l, i);
            long c2 = evaluate();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = it; }
            } else {
                sv[l][i] = old;
                set_dart(l, i);
            }
        }
    }
    return cost;
}

/* Independent check on the explicit graph: degrees, simple, bipartite, diameter <= D. */
static int verify_explicit(void) {
    int KG = K * G;
    int N = 2 * KG;
    for (int v = 0; v < N; v++) {
        const int *p = nb + (long)v * d;
        for (int l = 0; l < d; l++) {
            int u = p[l];
            if (u < 0 || u >= N || u == v) return 0;
            if ((v < KG) == (u < KG)) return 0;
            for (int q = 0; q < l; q++)
                if (p[q] == u) return 0;
            int found = 0;
            const int *pu = nb + (long)u * d;
            for (int q = 0; q < d; q++)
                if (pu[q] == v) { found = 1; break; }
            if (!found) return 0;
        }
    }
    int W = (N + 63) / 64;
    size_t sz = (size_t)N * (size_t)W;
    uint64_t *cur = calloc(sz, sizeof(uint64_t));
    uint64_t *nxt = calloc(sz, sizeof(uint64_t));
    if (!cur || !nxt) {
        free(cur);
        free(nxt);
        return 0;
    }
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            const int *p = nb + (long)v * d;
            for (int l = 0; l < d; l++) {
                const uint64_t *s = cur + (size_t)p[l] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++)
            total += __builtin_popcountll(cur[(size_t)v * W + w]);
    free(cur);
    free(nxt);
    return total == (long)N * (long)N;
}

static void record_best(int N) {
    be = 0;
    int KG = K * G;
    for (int v = 0; v < KG; v++)
        for (int l = 0; l < d; l++) {
            if (be >= MAXE) return;
            ea[be] = v;
            eb[be] = nb[v * d + l];
            be++;
        }
    bestN = N;
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
    double t_end = t0 + limit * 0.93 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long trials[MAXK + 1], wins[MAXK + 1];
    for (int c = 0; c <= MAXK; c++) { trials[c] = 0; wins[c] = 0; }
    double goal = 4000.0;

    while (now() < t_end) {
        int kk;
        if (rndint(5) == 0) {
            kk = 1 + rndint(6);
        } else {
            double bs = -1.0;
            kk = 1;
            for (int c = 1; c <= 6; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; kk = c; }
            }
        }
        K = kk;
        int target = (int)(goal / (2.0 * K)) + rndint(3);
        if (target < 2) target = 2;
        if (!setup_group(target)) continue;
        int N = 2 * K * G;
        if (N <= bestN) {
            goal = bestN * 1.02 + 2.0;
            continue;
        }
        trials[K]++;
        long c = anneal(t_end, 30000, 5000);
        if (c == 0 && verify_explicit()) {
            wins[K]++;
            record_best(N);
            goal = N * 1.04 + 2.0;
        } else {
            double floor_goal = bestN * 1.01 + 2.0;
            double dec = goal * 0.99;
            goal = dec > floor_goal ? dec : floor_goal;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", bestN, be);
    for (long e = 0; e < be; e++) printf("%d %d\n", ea[e], eb[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept as valid fallbacks and for D = 3, 4 targets).
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

    # Exact constructions (calibration cases return immediately).
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

    # Main search: one C engine for bi-Cayley lifts over semidirect groups.
    if d >= 3:
        remaining = 0.80 * time_limit - 2.5 - (time.monotonic() - t0)
        if remaining > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                 stdin_graph=None, timeout=remaining + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
