"""Bi-Cayley (Haar-type) search over semidirect groups, with algebraic starts as the fallback.

Bold change: instead of voltage hill-climbing from a start graph, the C engine enumerates
bipartite graphs a_x ~ b_{x s} (s in S, |S| = d, 0 in S WLOG) over every semidirect group
Z_m x|_r Z_k of order N, for N = n_in/2 + 1 upward. Left multiplication is an automorphism
acting transitively on each side, so diameter <= D holds iff BFS from a_e and b_e reaches all
2N vertices within D steps. Large connection-set spaces are sampled at random.

Python keeps the algebraic starts (PG(2,q), Araujo-Pardo-Lopez, W(q), K_{d,d}) as the fallback
and accepts the C output only if lib.is_valid confirms it."""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bi-Cayley search over semidirect groups Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit n_in
 * Graph on 2N vertices: a_x ~ b_{x*s} for s in S, |S| = d, S contains identity.
 * Diameter <= D iff BFS from a_e and from b_e reaches all 2N vertices within D steps.
 * Prints the largest graph found with more than n_in vertices, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXV 1024
#define MAXK 8
#define MAXEDGE (MAXG * MAXK)
#define MAXGROUPS 8192

static int d, D;
static double t_end;
static long n_in;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static double ncomb(int n, int k) {
    double r = 1.0;
    if (k < 0 || n < k) return 0.0;
    for (int i = 1; i <= k; i++) r = r * (double)(n - k + i) / (double)i;
    return r;
}

/* ---- group tables ---- */
static int G_N;
static int mulT[MAXG][MAXG];
static int invT[MAXG];

/* Element a*k + b of Z_m x|_r Z_k, product (a,b)(c,e) = (a + r^b c, b + e). */
static void build_group(int m, int k, int r) {
    int rp[MAXG];
    int N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mulT[x][y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mulT[x][y] == 0) { invT[x] = y; break; }
}

static int gM[MAXGROUPS], gK[MAXGROUPS], gR[MAXGROUPS];

static int collect_groups(int N) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < MAXGROUPS) { gM[cnt] = 1; gK[cnt] = k; gR[cnt] = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            if (cnt >= MAXGROUPS) return cnt;
            gM[cnt] = m; gK[cnt] = k; gR[cnt] = r; cnt++;
        }
    }
    return cnt;
}

/* ---- connection set and diameter check ---- */
static int S_[MAXK];
static int invS[MAXK];
static int dist_[MAXV], queue_[MAXV];

static int haar_ok(void) {
    int N = G_N, V = 2 * N;
    for (int i = 0; i < d; i++) invS[i] = invT[S_[i]];
    for (int src = 0; src < 2; src++) {
        int start = src ? N : 0;
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[start] = 0;
        queue_[tail++] = start;
        while (head < tail) {
            int v = queue_[head++];
            if (dist_[v] >= D) continue;
            int nd = dist_[v] + 1;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + mulT[v][S_[i]];
                    if (dist_[u] < 0) { dist_[u] = nd; queue_[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = mulT[y][invS[i]];
                    if (dist_[u] < 0) { dist_[u] = nd; queue_[tail++] = u; }
                }
            }
        }
        if (tail < V) return 0;
    }
    return 1;
}

/* ---- output buffer for the best graph found so far ---- */
static int out_n = 0, out_m = 0;
static int out_u[MAXEDGE], out_v[MAXEDGE];

static void record(void) {
    int N = G_N;
    out_m = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            out_u[out_m] = x;
            out_v[out_m] = N + mulT[x][S_[i]];
            out_m++;
        }
    out_n = 2 * N;
}

static long iter_ctr = 0;

/* Exhaustive enumeration of S = {0} + (d-1)-subsets of {1..N-1}, in lexicographic order. */
static int enum_group(void) {
    int N = G_N, k = d - 1;
    if (k > N - 1) return 0;
    int c[MAXK];
    S_[0] = 0;
    for (int i = 0; i < k; i++) c[i] = i + 1;
    for (;;) {
        if ((++iter_ctr & 511) == 0 && now() > t_end) return 0;
        for (int i = 0; i < k; i++) S_[i + 1] = c[i];
        if (haar_ok()) return 1;
        int i = k - 1;
        while (i >= 0 && c[i] == N - 1 - (k - 1 - i)) i--;
        if (i < 0) break;
        c[i]++;
        for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
    }
    return 0;
}

/* Random sampling of connection sets for large search spaces. */
static int rand_group(long samples) {
    int N = G_N, k = d - 1;
    if (k > N - 1) return 0;
    S_[0] = 0;
    for (long s = 0; s < samples; s++) {
        if ((s & 511) == 0 && now() > t_end) return 0;
        for (int i = 0; i < k; i++) {
            int x, dup;
            do {
                x = 1 + rndint(N - 1);
                dup = 0;
                for (int j = 0; j < i; j++)
                    if (S_[j + 1] == x) { dup = 1; break; }
            } while (dup);
            S_[i + 1] = x;
        }
        if (haar_ok()) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit n_in\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    n_in = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d >= 2 && d <= MAXK && D >= 2) {
        long s = 0, p = 1;
        for (int i = 0; i < D; i++) {
            s += p;
            p *= (d - 1);
            if (s > 100000) break;
        }
        long Nhi = s;               /* 2N <= Moore bound 2s */
        if (Nhi > MAXG) Nhi = MAXG;
        long Nlo = n_in / 2 + 1;
        for (long N = Nlo; N <= Nhi && now() < t_end; N++) {
            int cnt = collect_groups((int)N);
            for (int i = cnt - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t;
                t = gM[i]; gM[i] = gM[j]; gM[j] = t;
                t = gK[i]; gK[i] = gK[j]; gK[j] = t;
                t = gR[i]; gR[i] = gR[j]; gR[j] = t;
            }
            int ok = 0;
            for (int gi = 0; gi < cnt && !ok && now() < t_end; gi++) {
                G_N = (int)N;
                build_group(gM[gi], gK[gi], gR[gi]);
                if (ncomb((int)N - 1, d - 1) <= 400000.0)
                    ok = enum_group();
                else
                    ok = rand_group(300000);
                if (ok) record();
            }
        }
    }

    if (out_n > n_in) {
        printf("%d %d\n", out_n, out_m);
        for (int e = 0; e < out_m; e++) printf("%d %d\n", out_u[e], out_v[e]);
    } else {
        printf("0 0\n");
    }
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 8 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
