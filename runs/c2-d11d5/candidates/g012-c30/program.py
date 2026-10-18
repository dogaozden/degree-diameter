"""Bi-Cayley lift search in C (large base sizes, many voltage evaluations), with exact
constructions as fallback. Every returned graph is checked with lib.is_valid.

The C engine works on the lift of a base multigraph with k blocks per side over a
semidirect product Z_m x| Z_k2. Left translations are automorphisms of such a lift,
so diameter is checked with k-independent BFS from the 2k block representatives only.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealing.
 * Usage: prog d D seed time_limit [start_n]
 * Base: d perfect matchings (layers) between k A-blocks and k B-blocks, each dart carrying a
 * voltage s in G = Z_m x| Z_k2. Vertices A_{i,g} = i*G+g, B_{p,x} = (k+p)*G+x, with
 * A_{i,g} ~ B_{p, g*s}. Left translations are automorphisms, so it suffices that every block
 * representative reaches all vertices within D. Cost = unreached pairs + duplicate-dart penalty.
 * Output: "n m" + edges of the best valid lift found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12000
#define MAXD 32
#define MAXK 12
#define MAXG 6000
#define PW_MAX 64

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static double t_deadline;

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

/* current shape and state */
static int K, G, M, K2, R, N;
static int pw[PW_MAX];
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static int vis[MAXN];
static int qbuf[MAXN];
static int stampv = 0;

/* best found */
static int have_graph = 0;
static int ratchet_n = 0;
static int bK, bG, bM, bK2, bR, bNN;
static int bLayers[MAXD][MAXK], bS[MAXD][MAXK];

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void recompute_pw(void) {
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long)pw[b - 1] * R % M);
}

/* (a,b)*(c,d) = (a + r^b c, b + d) in Z_m x| Z_k2, element coded as a*k2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int aa = (a + (pw[b] * c) % M) % M;
    return aa * K2 + (b + e) % K2;
}

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    for (int g = 0; g < G; g++) {
        int x = gmul(g, s);
        int A = i * G + g;
        int B = (K + p) * G + x;
        nbr[l][A] = B;
        nbr[l][B] = A;
    }
}

static int bfs_unreached(int src) {
    if (++stampv == 0x7fffffff) {
        memset(vis, 0, sizeof vis);
        stampv = 1;
    }
    int head = 0, tail = 0;
    vis[src] = stampv;
    qbuf[tail++] = src;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            for (int l = 0; l < d; l++) {
                int u = nbr[l][v];
                if (vis[u] != stampv) {
                    vis[u] = stampv;
                    qbuf[tail++] = u;
                }
            }
        }
    }
    return N - tail;
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    long unr = 0;
    for (int b = 0; b < 2 * K; b++) unr += bfs_unreached(b * G);
    return unr + 40L * dup_count();
}

static const int K2_CHOICES[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24};

static int choose_shape(int k, int Gmin) {
    int k2 = K2_CHOICES[rndint((int)(sizeof K2_CHOICES / sizeof K2_CHOICES[0]))];
    int m = (Gmin + k2 - 1) / k2;
    if (m < 2) m = 2;
    if (k2 * m > MAXG) return 0;
    int r = 1;
    if (k2 >= 2 && m >= 3 && rnd01() < 0.7) {
        for (int t = 0; t < 60; t++) {
            int c = 2 + rndint(m - 2);
            if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    K = k;
    K2 = k2;
    M = m;
    R = r;
    G = m * k2;
    N = 2 * K * G;
    if (N > MAXN) return 0;
    recompute_pw();
    return 1;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layers[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Returns 0 when a valid lift was found, otherwise the final cost. */
static long anneal(long iters, double tlimit) {
    random_init();
    long cost = full_cost();
    double T0 = 2.0 + 0.02 * (double)cost;
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 15) == 0 && now() > tlimit) break;
        double T = 0.3 + T0 * (1.0 - (double)it / (double)iters);
        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long nc = full_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            long nc = full_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
    }
    return cost;
}

static void save_best(void) {
    bK = K;
    bG = G;
    bM = M;
    bK2 = K2;
    bR = R;
    bNN = N;
    memcpy(bLayers, layers, sizeof layers);
    memcpy(bS, S, sizeof S);
    have_graph = 1;
    ratchet_n = N;
}

static void print_best(void) {
    K = bK;
    G = bG;
    M = bM;
    K2 = bK2;
    R = bR;
    N = bNN;
    recompute_pw();
    memcpy(layers, bLayers, sizeof layers);
    memcpy(S, bS, sizeof S);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
    printf("%d %d\n", N, K * G * d);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, nbr[l][v]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = argc >= 6 ? atol(argv[5]) : 0;
    double t0 = now();
    t_deadline = t0 + limit - 1.0 - 0.03 * limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    if (start_n < 0) start_n = 0;
    if (start_n > MAXN / 2) start_n = MAXN / 2;
    ratchet_n = (int)start_n;

    double wins[MAXK + 1], tries[MAXK + 1];
    for (int c = 0; c <= MAXK; c++) {
        wins[c] = 0.0;
        tries[c] = 0.0;
    }

    while (now() < t_deadline) {
        double left = t_deadline - now();
        if (left < 0.5) break;
        int k;
        if (rnd01() < 0.25) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (tries[c] + 2.0) + 0.05 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    k = c;
                }
            }
        }
        int Gmin = ratchet_n / (2 * k) + 1 + rndint(3) + rndint(1 + ratchet_n / (100 * k));
        if (Gmin < 2) Gmin = 2;
        if (!choose_shape(k, Gmin)) continue;
        tries[k] += 1.0;
        double slice = left * 0.3;
        if (slice < 3.0) slice = 3.0;
        if (slice > left) slice = left;
        long c = anneal(6000, now() + slice);
        if (c == 0) {
            wins[k] += 1.0;
            save_best();
        }
    }

    if (!have_graph) {
        printf("0 0\n");
        return 0;
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

    # Main search: C bi-Cayley lift annealing with the remaining budget.
    budget = 0.85 * time_limit - 2.5
    if budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), int(best_n)],
                             stdin_graph=None, timeout=time_limit * 0.95 - 1.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
