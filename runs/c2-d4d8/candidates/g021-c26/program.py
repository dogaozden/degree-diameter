"""Voltage lift of a generalized quadrangle with a metacyclic group, plus an annealed diameter search.

Construction: take a small bipartite base graph that already meets the diameter (W(q) for
d = q+1, D = 4; it also satisfies D = 8). Lift it over a metacyclic group Z_m x| Z_k of order N.
Each base edge gets a voltage, and the lift has 80*N vertices (for W(3)) with the same degree.
The lift's diameter is checked exactly: left multiplication is a regular automorphism on each
fibre, so one BFS per base vertex suffices. Voltages are annealed to remove all pairs at distance
greater than D. The C program climbs the group order N while successes continue. Python keeps the
best valid graph and always returns a valid fallback.
"""
import itertools
import time

import lib

C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 512
#define MAXE 4096
#define MAXDEG 8
#define MAXL 16384

static int D;
static int nb, ne;
static int bu[MAXE], bv[MAXE], bdeg[MAXB], bside[MAXB];
static int volt[MAXE], best_volt[MAXE];
static int gm, gk, gr;
static int rp[MAXL];
static int N;
static int best_N, best_m, best_k, best_r;
static int nbr[MAXL][MAXDEG];
static int ndeg[MAXL];
static int dist_[MAXL], que[MAXL];
static double tend;
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

/* Metacyclic group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_group(int m, int k, int r) {
    gm = m; gk = k; gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

/* Uniformly random metacyclic group of order n (reservoir over all (m, r)). */
static int pick_group(int n, int *om, int *ok, int *orr) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    *om = bm; *ok = bk; *orr = br;
    return 1;
}

static int read_base(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXB || m < 0 || m > MAXE) return 0;
    nb = n; ne = m;
    for (int v = 0; v < n; v++) { bdeg[v] = 0; bside[v] = -1; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        bu[e] = u; bv[e] = v;
        bdeg[u]++; bdeg[v]++;
    }
    for (int v = 0; v < n; v++)
        if (bdeg[v] == 0 || bdeg[v] > MAXDEG) return 0;
    /* 2-colour the base by repeated edge scans (base is small). */
    static int queue[MAXB];
    for (int s = 0; s < n; s++) {
        if (bside[s] >= 0) continue;
        int h = 0, t = 0;
        bside[s] = 0;
        queue[t++] = s;
        while (h < t) {
            int v = queue[h++];
            for (int e = 0; e < m; e++) {
                int w = -1;
                if (bu[e] == v) w = bv[e];
                else if (bv[e] == v) w = bu[e];
                if (w < 0) continue;
                if (bside[w] < 0) { bside[w] = 1 - bside[v]; queue[t++] = w; }
            }
        }
    }
    for (int e = 0; e < m; e++)
        if (bside[bu[e]] == bside[bv[e]]) return 0;
    return 1;
}

static void build_adj(void) {
    int L = nb * N;
    for (int v = 0; v < L; v++) ndeg[v] = 0;
    for (int e = 0; e < ne; e++) {
        for (int x = 0; x < N; x++) {
            int a = bu[e] * N + x;
            int b = bv[e] * N + gmul(x, volt[e]);
            nbr[a][ndeg[a]++] = b;
            nbr[b][ndeg[b]++] = a;
        }
    }
}

/* Left multiplication is a regular automorphism on each fibre, so BFS from (u, identity)
 * for each base vertex u decides the diameter. Returns the number of pairs at distance > D. */
static long eval_bad(void) {
    int L = nb * N;
    long bad = 0;
    build_adj();
    for (int u = 0; u < nb; u++) {
        int src = u * N;
        for (int v = 0; v < L; v++) dist_[v] = -1;
        int h = 0, t = 0;
        dist_[src] = 0;
        que[t++] = src;
        while (h < t) {
            int v = que[h++];
            if (dist_[v] >= D) continue;
            for (int i = 0; i < ndeg[v]; i++) {
                int w = nbr[v][i];
                if (dist_[w] < 0) {
                    dist_[w] = dist_[v] + 1;
                    que[t++] = w;
                }
            }
        }
        bad += L - t;
    }
    return bad;
}

static long anneal(int iters) {
    for (int e = 0; e < ne; e++) volt[e] = rndint(N);
    long bad = eval_bad();
    double T = 1.0;
    for (int it = 0; it < iters && bad > 0; it++) {
        if ((it & 15) == 0 && now() > tend) break;
        int e = rndint(ne);
        int old = volt[e];
        int g = rndint(N);
        if (g == old) continue;
        volt[e] = g;
        long nbd = eval_bad();
        if (nbd <= bad || rnd01() < exp((double)(bad - nbd) / T)) {
            bad = nbd;
        } else {
            volt[e] = old;
        }
        T *= 0.999;
        if (T < 0.05) T = 1.0;
    }
    return bad;
}

static void print_best(void) {
    if (best_N <= 0) { printf("0 0\n"); return; }
    set_group(best_m, best_k, best_r);
    N = best_N;
    printf("%d %d\n", nb * N, ne * N);
    for (int e = 0; e < ne; e++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", bu[e] * N + x, bv[e] * N + gmul(x, best_volt[e]));
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit nmin nmax < base\n", argv[0]);
        return 2;
    }
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int nmin = atoi(argv[5]), nmax = atoi(argv[6]);
    double t0 = now();
    tend = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D < 1 || !read_base()) { printf("0 0\n"); return 0; }
    if (nmin < 1) nmin = 1;
    if (nmax > MAXL / nb) nmax = MAXL / nb;

    best_N = 0;
    int cur = nmin;
    while (cur <= nmax && now() < tend) {
        int m, k, r;
        if (!pick_group(cur, &m, &k, &r)) { cur++; continue; }
        set_group(m, k, r);
        N = cur;
        long bad = anneal(8000);
        if (bad == 0) {
            best_N = cur;
            best_m = m; best_k = k; best_r = r;
            memcpy(best_volt, volt, sizeof(int) * (size_t)ne);
            cur++;
        }
    }
    print_best();
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


MAX_BASE = 512
MAX_LIFT = 16384
MAX_BASE_DEG = 8


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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    n0, e0 = best
    if n0 > MAX_BASE or lib.max_degree(n0, e0) > MAX_BASE_DEG:
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 3.0:
        return best

    nmax = min(lib.moore_bound(d, D) // n0, MAX_LIFT // n0)
    if nmax < 2:
        return best

    try:
        text = lib.run_c(C_LIFT, [d, D, seed, budget, 2, nmax],
                         stdin_graph=best, timeout=budget + 10)
        n1, e1 = lib.parse_graph_text(text)
        if n1 > n0 and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)
    except Exception:
        pass
    return best
