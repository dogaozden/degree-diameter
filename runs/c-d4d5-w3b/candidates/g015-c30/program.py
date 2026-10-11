"""Bold variant: bipartite Cayley-type lifts over semidirect groups replace the voltage search.

Vertices are a_x and b_y for x, y in a group G of order N, with a_x adjacent to b_{x s} for
each s in a connection set S of size d. Left multiplication is an automorphism, so the
diameter check only needs BFS from a_e and b_e (two searches). C does a random-restart
local search over (group, S) and climbs N upward from the algebraic start. Python keeps the
algebraic starts (PG(2,q), Araujo-Pardo-Lopez, W(q), K_{d,d}) as the fallback and validates
every output with lib.is_valid.
"""
import itertools
import time

import lib

MAXG = 256

C_SOURCE = r'''
/* Random search for bipartite Cayley lifts over Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit nlo nhi     (stdin ignored)
 * Vertices: a_x = x, b_y = N + y. Edge a_x -- b_{x s} for s in S (|S| = d).
 * Diameter <= D iff BFS from a_e and from b_e reaches all 2N vertices within D.
 * Prints the largest valid order found as "n m" plus edges, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 256
#define MAXD 16
#define MAXGROUPS 4096

static int d, D, N;
static double t_end;

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

/* Group Z_m x|_r Z_k with N = m*k; element a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGROUPS];
static int ngroups;
static int mt[MAXG][MAXG];
static int invv[MAXG];

static void list_groups(void) {
    ngroups = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ngroups < MAXGROUPS) {
                groups[ngroups].m = 1; groups[ngroups].k = k; groups[ngroups].r = 0;
                ngroups++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXGROUPS) {
                groups[ngroups].m = m; groups[ngroups].k = k; groups[ngroups].r = r;
                ngroups++;
            }
        }
    }
}

static void build_group(Grp g) {
    int rp[MAXG];
    rp[0] = 1 % g.m;
    for (int b = 1; b < g.k; b++) rp[b] = (int)((long)rp[b - 1] * g.r % g.m);
    for (int x = 0; x < N; x++) {
        int a = x / g.k, b = x % g.k;
        for (int y = 0; y < N; y++) {
            int c = y / g.k, e = y % g.k;
            mt[x][y] = (int)(((a + (long)rp[b] * c) % g.m) * g.k + (b + e) % g.k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x][y] == 0) { invv[x] = y; break; }
}

static int S[MAXD], Sinv[MAXD];

static void sync_inv(void) {
    for (int i = 0; i < d; i++) Sinv[i] = invv[S[i]];
}

static int distv[2 * MAXG], qu[2 * MAXG];

/* BFS from a_0 (from_b = 0) or b_0 (from_b = 1) up to depth D; returns vertices reached. */
static int reach_count(int from_b) {
    for (int v = 0; v < 2 * N; v++) distv[v] = -1;
    int head = 0, tail = 0;
    int s0 = from_b ? N : 0;
    distv[s0] = 0;
    qu[tail++] = s0;
    while (head < tail) {
        int v = qu[head++];
        if (distv[v] >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + mt[v][S[i]];
                if (distv[u] < 0) { distv[u] = distv[v] + 1; qu[tail++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = mt[y][Sinv[i]];
                if (distv[u] < 0) { distv[u] = distv[v] + 1; qu[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Zero exactly when the Cayley lift has diameter <= D. */
static int bad_count(void) {
    return (2 * N - reach_count(0)) + (2 * N - reach_count(1));
}

static void random_S(void) {
    for (int i = 0; i < d; i++) {
        for (;;) {
            int g = rndint(N), ok = 1;
            for (int j = 0; j < i; j++)
                if (S[j] == g) { ok = 0; break; }
            if (ok) { S[i] = g; break; }
        }
    }
    sync_inv();
}

/* Random restarts with hill climbing on S. Returns 1 with a valid S (group in mt) or 0. */
static int search_N(double until) {
    list_groups();
    if (ngroups == 0) return 0;
    int moves = N > d ? 300 : 0;
    while (now() < until) {
        build_group(groups[rndint(ngroups)]);
        random_S();
        int bad = bad_count();
        for (int s = 0; s < moves && bad > 0; s++) {
            int i = rndint(d), old = S[i], cand;
            for (;;) {
                cand = rndint(N);
                int dup = 0;
                for (int j = 0; j < d; j++)
                    if (S[j] == cand) { dup = 1; break; }
                if (!dup) break;
            }
            S[i] = cand;
            sync_inv();
            int nb = bad_count();
            if (nb <= bad || rnd01() < 0.02) {
                bad = nb;
            } else {
                S[i] = old;
                sync_inv();
            }
        }
        if (bad == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit nlo nhi\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int nlo = atoi(argv[5]), nhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    if (nhi > MAXG) nhi = MAXG;
    if (nlo < d) nlo = d;

    static int bu[MAXG * MAXD], bv[MAXG * MAXD];
    int bm = 0, bestN = 0;
    int cur = nlo;
    double slice = 1.0;
    while (cur <= nhi && now() < t_end) {
        N = cur;
        double left = t_end - now();
        double until = now() + (slice < left ? slice : left);
        if (search_N(until)) {
            bestN = N;
            bm = 0;
            for (int x = 0; x < N; x++)
                for (int i = 0; i < d; i++) {
                    bu[bm] = x;
                    bv[bm] = N + mt[x][S[i]];
                    bm++;
                }
            cur++;
            slice = 1.0;
        } else {
            slice *= 1.5;
        }
    }
    printf("%d %d\n", 2 * bestN, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", bu[e], bv[e]);
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

    moore = lib.moore_bound(d, D)
    if d > 16 or best[0] >= moore:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    # A Cayley lift on a group of order N gives 2N vertices, so only N > best/2 can improve.
    nlo = best[0] // 2 + 1
    nhi = min(moore // 2, MAXG)
    if nlo > nhi:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, nlo, nhi],
                         stdin_graph=None, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
