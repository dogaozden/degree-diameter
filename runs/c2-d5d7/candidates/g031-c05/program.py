"""Bi-Cayley lift search with tabu voltage moves for the d=5, D=7 target.

This version replaces the parent's annealed voltage climb with a tabu search and a different
order sweep. It keeps the same algebraic starts, so every case returns a valid graph.

Construction: for a semidirect product G = Z_m x|_r Z_k of order N, the bi-Cayley graph has
vertices a_x and b_x (x in G) and edges a_x -- b_{x g_t} for t = 0..d-1, with g_0 = e and distinct
g_t. Left multiplication is an automorphism that is transitive on each side, so a diameter check
needs only BFS from a_e and b_e. The bi-Cayley graph is bipartite and d-regular, so no separate
validity check is needed in C.

Search: for each candidate order N, a tabu search moves one voltage at a time. Each step samples
TABU_K moves, takes the best non-tabu move (with aspiration), and forbids returning the old voltage
for a few steps. Orders are drawn from a window just above the incumbent, biased low. The C program
prints the largest success, or "0 0". Python keeps the algebraic start whenever C fails and checks
the result with lib.is_valid.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search with tabu voltage moves.
 * Usage: prog d D seed time_limit Nstart     (stdin ignored)
 * Output: "n m" and m edge lines for the best bi-Cayley graph found (order 2N > 2*Nstart),
 *         or "0 0" if nothing was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 6000
#define MAXV (2 * MAXN)
#define MAXD 16
#define TBL_MAX 3000
#define TABU_K 24

static int d, D;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
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

/* Group Z_m x|_r Z_k, element a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static Grp G, BG;
static int N;
static int use_tbl;
static uint16_t TBL[TBL_MAX * TBL_MAX];

static int gmul_raw(int x, int y) {
    int k = G.k;
    int a = x / k, b = x - a * k, c = y / k, e = y - c * k;
    long s = a + (long)G.rp[b] * c;
    int bb = b + e;
    if (bb >= k) bb -= k;
    return (int)(s % G.m) * k + bb;
}

static void setup_table(void) {
    use_tbl = N <= TBL_MAX;
    if (!use_tbl) return;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            TBL[(size_t)x * N + y] = (uint16_t)gmul_raw(x, y);
}

static inline int gmul(int x, int y) {
    return use_tbl ? (int)TBL[(size_t)x * N + y] : gmul_raw(x, y);
}

/* (a,b)^{-1} = (-r^{-b} a, -b). */
static int ginv(int x) {
    int k = G.k, m = G.m;
    int a = x / k, b = x - a * k;
    int nb = (k - b) % k;
    long c = (-(long)G.rp[nb] * a) % m;
    if (c < 0) c += m;
    return (int)c * k + nb;
}

/* Uniform admissible semidirect product of order n (reservoir sampling). */
static int random_group(int n) {
    long count = 0;
    int found = 0;
    int bm = 1, bk = n, br = 1;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; found = 1; }
        }
    }
    if (!found) return 0;
    G.m = bm;
    G.k = bk;
    G.r = br;
    G.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G.rp[b] = (int)((long)G.rp[b - 1] * br % bm);
    N = n;
    return 1;
}

static int distv[MAXV], seenv[MAXV], qv[MAXV];
static int stamp_v = 0;
static int gi[MAXD];

/* Number of (source, vertex) pairs at distance > D, sources a_e and b_e. */
static long eval_bad(const int *g) {
    for (int t = 0; t < d; t++) gi[t] = ginv(g[t]);
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_v++;
        seenv[src] = stamp_v;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int t = 0; t < d; t++) {
                    int u = N + gmul(v, g[t]);
                    if (seenv[u] != stamp_v) {
                        seenv[u] = stamp_v;
                        distv[u] = dv + 1;
                        qv[tail++] = u;
                    }
                }
            } else {
                int z = v - N;
                for (int t = 0; t < d; t++) {
                    int u = gmul(z, gi[t]);
                    if (seenv[u] != stamp_v) {
                        seenv[u] = stamp_v;
                        distv[u] = dv + 1;
                        qv[tail++] = u;
                    }
                }
            }
        }
        total += 2L * N - tail;
    }
    return total;
}

static int tabu_until[MAXD][MAXN];

static int used_in(const int *g, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (g[i] == v) return 1;
    return 0;
}

/* Tabu search over voltages g[1..d-1] (g[0] = 0 fixed). Returns 0 with g holding a valid
 * voltage set, or the best objective seen (g then holds that best set). */
static long tabu_search(int *g, double until) {
    memset(tabu_until, 0, sizeof(tabu_until));
    long cur = eval_bad(g);
    long best = cur;
    int bestg[MAXD];
    memcpy(bestg, g, sizeof(int) * d);
    for (long it = 1; cur > 0; it++) {
        if ((it & 3) == 0 && now() > until) break;
        long bm = -1;
        int bt = -1, bv = -1;
        for (int k = 0; k < TABU_K; k++) {
            int t = 1 + rndint(d - 1);
            int v;
            do { v = rndint(N); } while (used_in(g, d, v));
            int old = g[t];
            g[t] = v;
            long nb = eval_bad(g);
            g[t] = old;
            int tb = tabu_until[t][v] > (int)it;
            if (tb && nb >= best) continue;
            if (bm < 0 || nb < bm || (nb == bm && rndint(2))) {
                bm = nb;
                bt = t;
                bv = v;
            }
        }
        if (bt < 0) continue;
        tabu_until[bt][g[bt]] = (int)it + 4 + rndint(8);
        g[bt] = bv;
        cur = bm;
        if (cur < best) {
            best = cur;
            memcpy(bestg, g, sizeof(int) * d);
        }
    }
    if (cur == 0) return 0;
    memcpy(g, bestg, sizeof(int) * d);
    return best;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit Nstart\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long Nstart = atol(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double tend = t0 + limit * 0.92;
    long Nmax = moore_bound() / 2;
    if (Nmax > MAXN) Nmax = MAXN;

    if (d < 3 || d > MAXD || D < 2 || Nmax <= d) {
        printf("0 0\n");
        return 0;
    }

    int best_N = 0;
    int bestg[MAXD];
    long lo = Nstart;
    if (lo < d + 1) lo = d + 1;

    while (now() < tend && lo <= Nmax) {
        double left = tend - now();
        double slice = left / 4.0;
        if (slice < 3.0) slice = left;
        long span = Nmax - lo + 1;
        if (span > 80) span = 80;
        double u = rnd01();
        long Nt = lo + (long)(u * u * span);
        if (Nt > Nmax) Nt = Nmax;

        /* Prefer a non-abelian semidirect product when one is sampled quickly. */
        int ok = 0;
        for (int tries = 0; tries < 6 && !ok; tries++) {
            if (!random_group((int)Nt)) break;
            ok = 1;
            if (G.m > 1 && G.k > 1 && G.r != 1) break;
        }
        if (!ok) { lo = Nt + 1; continue; }
        setup_table();

        int g[MAXD];
        g[0] = 0;
        for (int t = 1; t < d; t++) {
            int v;
            do { v = rndint((int)Nt); } while (used_in(g, t, v));
            g[t] = v;
        }
        long r = tabu_search(g, now() + slice);
        if (r == 0) {
            BG = G;
            best_N = (int)Nt;
            memcpy(bestg, g, sizeof(int) * d);
            lo = Nt + 1;
        }
    }

    if (best_N == 0) {
        printf("0 0\n");
        return 0;
    }
    G = BG;
    N = best_N;
    setup_table();
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", x, N + gmul(x, bestg[t]));
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 1.0:
        return best
    n_start = best[0] // 2 + 1
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, n_start],
                         stdin_graph=None, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
