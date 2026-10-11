"""Bi-Cayley search program (bold change from the voltage-lift parent).

Builds bipartite graphs G = (A, B) with A = B = group G of order N, edges x -- x*s for a connection
set S of d distinct elements. Each such graph is d-regular and bipartite. Because left
multiplication is an automorphism that acts transitively on each side, the diameter test needs only
two BFS runs, from the identity of A and the identity of B. The C engine anneals S over every
semidirect group Z_m x|_r Z_k of order N, for N from the start size upward. Python falls back to
K_{d,d} or the algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez) whenever the C search returns
nothing valid, and every returned graph is checked with lib.is_valid.
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

#define MAXN 160
#define MAXDEG 32
#define MAXOPT 4096

static int d, D, N;
static int mt[MAXN][MAXN];
static int inv_[MAXN];
static int S[MAXDEG];
static int dist_[2 * MAXN], qu[2 * MAXN];
static double t_stop;

static int bN = 0, bm = 0, bk = 0, br = 0;
static int bS[MAXDEG];

static int optm[MAXOPT], optk[MAXOPT], optr[MAXOPT];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) {
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
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Semidirect group Z_m x|_r Z_k with N = m*k; element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void build_group(int m, int k, int r) {
    int rp[MAXN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int a2 = y / k, b2 = y % k;
            mt[x][y] = (int)((a1 + (long)rp[b1] * a2) % m) * k + (b1 + b2) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x][y] == 0) { inv_[x] = y; break; }
}

static int list_groups(int c) {
    int cnt = 0;
    for (int m = 1; m <= c; m++) {
        if (c % m) continue;
        int k = c / m;
        if (m == 1) {
            if (cnt < MAXOPT) { optm[cnt] = 1; optk[cnt] = k; optr[cnt] = 0; cnt++; }
            continue;
        }
        if (k == 1) continue; /* cyclic, already covered by m = 1 */
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXOPT) { optm[cnt] = m; optk[cnt] = k; optr[cnt] = r; cnt++; }
        }
    }
    for (int i = cnt - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t;
        t = optm[i]; optm[i] = optm[j]; optm[j] = t;
        t = optk[i]; optk[i] = optk[j]; optk[j] = t;
        t = optr[i]; optr[i] = optr[j]; optr[j] = t;
    }
    return cnt;
}

/* Number of vertices NOT within distance D of src in the bi-Cayley graph. */
static int unreached(int src) {
    int nv = 2 * N;
    for (int i = 0; i < nv; i++) dist_[i] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (dist_[v] >= D) continue;
        int nd = dist_[v] + 1;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + mt[v][S[i]];
                if (dist_[u] < 0) { dist_[u] = nd; qu[t++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = mt[y][inv_[S[i]]];
                if (dist_[u] < 0) { dist_[u] = nd; qu[t++] = u; }
            }
        }
    }
    return nv - t;
}

/* Anneal the connection set S over the current group. Returns 1 if the diameter is <= D. */
static int anneal(long steps, double until) {
    static int used[MAXN];
    memset(used, 0, sizeof(int) * N);
    for (int i = 0; i < d; i++) {
        int s;
        do { s = rndint(N); } while (used[s]);
        used[s] = 1;
        S[i] = s;
    }
    int f = unreached(0) + unreached(N);
    double T = 1.0;
    for (long it = 0; it < steps && f > 0; it++) {
        if ((it & 127) == 0 && now() > until) break;
        int i = rndint(d);
        int old = S[i], s;
        do { s = rndint(N); } while (used[s]);
        S[i] = s;
        int nf = unreached(0) + unreached(N);
        if (nf <= f || rnd01() < exp((double)(f - nf) / T)) {
            used[old] = 0;
            used[s] = 1;
            f = nf;
        } else {
            S[i] = old;
        }
        T *= 0.998;
        if (T < 0.05) T = 1.0;
    }
    return f == 0;
}

/* Try to realise a bi-Cayley graph of order 2c. Splits the slice across all groups of order c. */
static int try_order(int c, double slice) {
    if (c <= d) return 0;
    int cnt = list_groups(c);
    if (cnt == 0) return 0;
    double end = now() + slice;
    if (end > t_stop) end = t_stop;
    for (int g = 0; g < cnt && now() < end; g++) {
        N = c;
        build_group(optm[g], optk[g], optr[g]);
        double until = now() + (end - now()) / (cnt - g);
        if (anneal(1000000000L, until)) {
            bN = c;
            bm = optm[g];
            bk = optk[g];
            br = optr[g];
            memcpy(bS, S, sizeof(int) * d);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit nlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int nlo = atoi(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_stop = t0 + limit * 0.9;

    if (d < 3 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }
    long mb = moore_bound();
    int nhi = (int)(mb / 2);
    if (nhi > MAXN - 1) nhi = MAXN - 1;
    if (nlo < d + 1) nlo = d + 1;

    double slice = 0.4;
    while (now() < t_stop) {
        int start = (bN + 1 > nlo) ? bN + 1 : nlo;
        if (start > nhi) break;
        for (int c = start; c <= nhi && now() < t_stop; c++) {
            try_order(c, slice);
        }
        slice *= 2;
    }

    if (bN == 0) { printf("0 0\n"); return 0; }
    N = bN;
    build_group(bm, bk, br);
    for (int i = 0; i < d; i++) S[i] = bS[i];
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + mt[x][S[i]]);
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

    if D < 2 or d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 1.0:
        return best
    nlo = best[0] // 2 + 1
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         timeout=budget + 4)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
