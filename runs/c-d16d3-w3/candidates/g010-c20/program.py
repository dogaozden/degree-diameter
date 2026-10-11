"""Diameter-3 search by bi-Cayley lifts, plus structured fallbacks.

Main construction (D = 3): pick a group G of order m and a set S of d elements. Build the bipartite
graph on A = G and B = G with a_x adjacent to b_{x s} for s in S. It is d-regular with 2m vertices.
Its diameter is at most 3 exactly when S S^{-1} = G and S^{-1} S = G:
  - same-side pairs need a common neighbour, which is the covering S S^{-1} = G (or S^{-1} S = G on B);
  - cross pairs are then within distance 3, since G S = G.
Covering needs m - 1 <= d(d-1), so m <= d^2 - d + 1, giving 2m <= 2(d^2 - d + 1) = the Moore-type
ceiling 482 for d = 16. The C engine searches groups Z_a x|_r Z_b (a*b = m, including abelian and cyclic
ones) for m = mlo, mlo+1, ..., by simulated annealing on the number of uncovered elements. It climbs while
it keeps succeeding. Every result is re-checked with lib.is_valid.

Fallbacks: the Araujo-Pardo/Lopez or projective-plane start when it applies, the conic blow-up of PG(2,q)
(order 394 for d = 16), and K_{d,d}. Every case returns a valid graph, and the best valid one is kept.
For D != 3, only the structured starts are used.
"""
import time

import lib

C_BICAYLEY = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 256
#define MAXD 40
#define MAXC 4096

static int d, M;
static int mul_t[MAXM][MAXM];
static int inv_t[MAXM];
static int cnt1[MAXM], cnt2[MAXM];
static int Z;
static int S[MAXD];
static int inS[MAXM];
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

typedef struct { int a, b, r; } Grp;
static Grp cands[MAXC];
static int ncand;

/* Groups Z_a x|_r Z_b of order m: element (x, y) coded as x*b + y,
   (x1,y1)(x2,y2) = (x1 + r^{y1} x2 mod a, y1 + y2 mod b), needs r^b = 1 mod a, gcd(r,a)=1. */
static void enum_groups(int m) {
    ncand = 0;
    for (int a = 1; a <= m; a++) {
        if (m % a) continue;
        int b = m / a;
        if (a == 1) {
            if (ncand < MAXC) { cands[ncand].a = 1; cands[ncand].b = b; cands[ncand].r = 0; ncand++; }
            continue;
        }
        for (int r = 1; r < a; r++) {
            if (gcd(r, a) != 1) continue;
            if (powmod(r, b, a) != 1 % a) continue;
            if (ncand < MAXC) { cands[ncand].a = a; cands[ncand].b = b; cands[ncand].r = r; ncand++; }
        }
    }
}

static void build_group(Grp g) {
    int rp[MAXM];
    rp[0] = 1 % g.a;
    for (int k = 1; k < g.b; k++) rp[k] = (int)((long)rp[k - 1] * g.r % g.a);
    M = g.a * g.b;
    for (int x = 0; x < M; x++) {
        int a1 = x / g.b, b1 = x % g.b;
        for (int y = 0; y < M; y++) {
            int a2 = y / g.b, b2 = y % g.b;
            int c = (int)(((long)a1 + (long)rp[b1] * a2) % g.a);
            int e = (b1 + b2) % g.b;
            mul_t[x][y] = c * g.b + e;
        }
    }
    for (int x = 0; x < M; x++)
        for (int y = 0; y < M; y++)
            if (mul_t[x][y] == 0) { inv_t[x] = y; break; }
}

/* cnt1 counts ordered pairs (s,t) of S by s t^{-1}; cnt2 counts them by s^{-1} t.
   Z = number of zero entries over both arrays; the goal is Z == 0. */
static inline void inc1(int g) { if (cnt1[g]++ == 0) Z--; }
static inline void dec1(int g) { if (--cnt1[g] == 0) Z++; }
static inline void inc2(int g) { if (cnt2[g]++ == 0) Z--; }
static inline void dec2(int g) { if (--cnt2[g] == 0) Z++; }

static inline void pair_in(int s, int t) {
    inc1(mul_t[s][inv_t[t]]);
    inc2(mul_t[inv_t[s]][t]);
}
static inline void pair_out(int s, int t) {
    dec1(mul_t[s][inv_t[t]]);
    dec2(mul_t[inv_t[s]][t]);
}

static void drop(int i) {
    int a = S[i];
    for (int j = 0; j < d; j++)
        if (j != i) { pair_out(a, S[j]); pair_out(S[j], a); }
    pair_out(a, a);
}

static void put(int i, int x) {
    S[i] = x;
    for (int j = 0; j < d; j++)
        if (j != i) { pair_in(x, S[j]); pair_in(S[j], x); }
    pair_in(x, x);
}

static void full_build(void) {
    memset(cnt1, 0, sizeof cnt1);
    memset(cnt2, 0, sizeof cnt2);
    Z = 2 * M;
    for (int i = 0; i < d; i++) {
        pair_in(S[i], S[i]);
        for (int j = 0; j < i; j++) {
            pair_in(S[i], S[j]);
            pair_in(S[j], S[i]);
        }
    }
}

static void random_set(void) {
    memset(inS, 0, sizeof inS);
    for (int i = 0; i < d; i++) {
        int x;
        do x = rndint(M); while (inS[x]);
        inS[x] = 1;
        S[i] = x;
    }
}

/* One annealing run on the current group. Returns 1 if S S^{-1} = G = S^{-1} S. */
static int search_cycle(long L) {
    random_set();
    full_build();
    const double T0 = 1.0, T1 = 0.06;
    for (long it = 0; it < L; it++) {
        if (Z == 0) return 1;
        if ((it & 4095) == 0 && now() > t_end) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)L);
        int i = rndint(d);
        int x;
        do x = rndint(M); while (inS[x]);
        int old = S[i];
        int Zold = Z;
        drop(i);
        put(i, x);
        int dz = Z - Zold;
        if (dz <= 0 || rnd01() < exp(-(double)dz / T)) {
            inS[old] = 0;
            inS[x] = 1;
        } else {
            drop(i);
            put(i, old);
        }
    }
    return Z == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    int mlo = atoi(argv[3]);
    double budget = atof(argv[4]);
    if (d < 3 || d > MAXD) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    t_end = now() + budget;

    int mhi = d * (d - 1) + 1;          /* covering bound: m - 1 <= d(d-1) */
    if (mhi > MAXM - 1) mhi = MAXM - 1;
    if (mlo < d + 1) mlo = d + 1;

    int bestm = 0;
    Grp bestg = {0, 0, 0};
    int bestS[MAXD];
    for (int m = mlo; m <= mhi && now() < t_end; m++) {
        enum_groups(m);
        if (ncand == 0) continue;
        Grp g = {0, 0, 0};
        int ok = 0;
        while (now() < t_end) {
            g = cands[rndint(ncand)];
            build_group(g);
            if (search_cycle(400000L)) { ok = 1; break; }
        }
        if (!ok) break;
        bestm = m;
        bestg = g;
        memcpy(bestS, S, sizeof(int) * (size_t)d);
    }
    if (bestm == 0) { printf("0 0\n"); return 0; }

    build_group(bestg);
    printf("%d %ld\n", 2 * bestm, (long)bestm * d);
    for (int x = 0; x < bestm; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, bestm + mul_t[x][bestS[k]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (fallbacks).
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Moore graph or Araujo-Pardo/Lopez graph for D = 3, when they apply."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def starts(d, D):
    out = []
    for fn in (known_start, conic_blowup):
        try:
            g = fn(d, D)
        except Exception:
            g = None
        if g is not None:
            out.append(g)
    return out


# ----------------------------------------------------------------------------
# C driver.
# ----------------------------------------------------------------------------

def _run_bicayley(d, seed, mlo, budget):
    text = lib.run_c(C_BICAYLEY, [d, seed, mlo, f"{budget:.2f}"],
                     stdin_graph=None, timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    for g in starts(d, D):
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass
    try:
        if lib.is_valid(fallback[0], fallback[1], d, D):
            cands.append(fallback)
    except Exception:
        pass
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    # Main search: bi-Cayley lifts over groups of order m, climbing from the current best.
    if D == 3 and d >= 3 and d * (d - 1) + 1 >= best[0] // 2 + 1:
        remaining = hard_end - time.monotonic()
        if remaining > 3.0:
            try:
                n1, e1 = _run_bicayley(d, seed * 131 + 5, best[0] // 2 + 1, remaining - 1.5)
                if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                    best = (n1, e1)
            except Exception:
                pass

    try:
        if not lib.is_valid(best[0], best[1], d, D):
            best = fallback
    except Exception:
        best = fallback
    return best
