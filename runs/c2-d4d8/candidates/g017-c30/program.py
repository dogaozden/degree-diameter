"""Haar-type bi-Cayley search over metacyclic groups with annealed connection sets.

Construction: for a group G of order N and a set S of d distinct elements, the Haar graph
H(G, S) has parts A = {A_g} and B = {B_x}, with A_g adjacent to B_{gs} for s in S. Left
multiplication by G is an automorphism with two orbits (A and B), so the diameter is at most D
iff BFS from A_1 and from B_1 reaches every vertex within D steps. Each evaluation is therefore
two BFS runs on an implicit graph. The C engine climbs N from the start graph's half-order,
anneals S for each candidate group (random metacyclic Z_m x| Z_k), and verifies any success with a
full all-sources check before accepting it.

This replaces the earlier multi-fibre voltage-lift search with a single-orbit bi-Cayley search.
Python keeps the algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez, K_{d,d}) as fallbacks and
accepts the C output only if lib.is_valid confirms it and it is strictly larger.
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

#define MAXN 4096
#define MAXV (2 * MAXN)
#define MAXD 16
#define MAXT 65536

typedef struct { int m, k, r; } Tri;

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int d, D;
static long MOORE;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

/* Metacyclic group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */
static Grp G;
static int N;
static int S[MAXD], Si[MAXD];
static int dist[MAXV], qb[MAXV];
static Tri tris[MAXT];
static int ntris;

static void set_group(const Tri *t) {
    G.m = t->m; G.k = t->k; G.r = t->r;
    G.rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) G.rp[b] = (int)((long)G.rp[b - 1] * G.r % G.m);
}

static int gmul(int x, int y) {
    int a = x / G.k, b = x % G.k, c = y / G.k, e = y % G.k;
    return (int)((a + (long)G.rp[b] * c) % G.m) * G.k + (b + e) % G.k;
}

/* Inverse of (a,b) is (-a r^(-b), -b). */
static int ginv(int x) {
    int a = x / G.k, b = x % G.k;
    int nb = (G.k - b) % G.k;
    long t = ((long)a * G.rp[nb]) % G.m;
    int c = (int)((G.m - t) % G.m);
    return c * G.k + nb;
}

static void enum_groups(int n) {
    ntris = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ntris < MAXT) { tris[ntris].m = 1; tris[ntris].k = k; tris[ntris].r = 0; ntris++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            if (ntris < MAXT) { tris[ntris].m = m; tris[ntris].k = k; tris[ntris].r = r; ntris++; }
        }
    }
}

/* Vertices: A_g = g, B_x = N + x. Returns the number of vertices not within D of src. */
static long bfs_bad(int src) {
    int nv = 2 * N;
    for (int v = 0; v < nv; v++) dist[v] = -1;
    int head = 0, tail = 0;
    dist[src] = 0;
    qb[tail++] = src;
    while (head < tail) {
        int v = qb[head++];
        if (dist[v] >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + gmul(v, S[i]);
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qb[tail++] = u; }
            }
        } else {
            int x = v - N;
            for (int i = 0; i < d; i++) {
                int u = gmul(x, Si[i]);
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qb[tail++] = u; }
            }
        }
    }
    return nv - tail;
}

static long eval_bad(void) {
    return bfs_bad(0) + bfs_bad(N);
}

static int full_ok(void) {
    for (int s = 0; s < 2 * N; s++)
        if (bfs_bad(s) != 0) return 0;
    return 1;
}

/* Anneal the d connection elements. Returns the lowest defect count seen; outS holds that set. */
static long anneal(int iters, double until, int *outS) {
    for (int i = 0; i < d; i++) {
        int x, dup;
        do {
            x = rndint(N);
            dup = 0;
            for (int j = 0; j < i; j++) if (S[j] == x) dup = 1;
        } while (dup);
        S[i] = x;
    }
    for (int i = 0; i < d; i++) Si[i] = ginv(S[i]);
    long bad = eval_bad(), bestb = bad;
    memcpy(outS, S, sizeof(int) * d);
    double T = 2.0;
    for (int it = 0; it < iters && bestb > 0; it++) {
        if ((it & 255) == 0 && now() > until) break;
        int i = rndint(d), x = rndint(N);
        int dup = 0;
        for (int j = 0; j < d; j++) if (S[j] == x) { dup = 1; break; }
        if (dup) continue;
        int old = S[i], oldi = Si[i];
        S[i] = x;
        Si[i] = ginv(x);
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) { bestb = bad; memcpy(outS, S, sizeof(int) * d); }
        } else {
            S[i] = old;
            Si[i] = oldi;
        }
        T *= 0.999;
        if (T < 0.05) T = 2.0;
    }
    return bestb;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    MOORE = moore_bound();

    int have = 0, bestN = 0;
    Tri bestT = {1, 1, 0};
    int bestS[MAXD];
    static int outS[MAXD];
    int cur = (int)(start_n / 2);
    if (cur < d - 1) cur = d - 1;   /* cur = largest N known to give 2N <= current best */
    int step = 1, cur_N = -1;

    while (now() < t_end) {
        long cand = (long)cur + step;
        if (2 * cand > MOORE || cand > MAXN) {
            if (step > 1) { step = 1; continue; }
            break;
        }
        int c = (int)cand;
        if (c != cur_N) { enum_groups(c); cur_N = c; }
        N = c;
        Tri t = tris[rndint(ntris)];
        set_group(&t);

        double left = t_end - now();
        double slice = left / 8;
        if (slice > 2.0) slice = 2.0;
        if (slice < 0.2) slice = 0.2;
        if (slice > left) slice = left;

        long bad = anneal(3000, now() + slice, outS);
        int ok = 0;
        if (bad == 0) {
            memcpy(S, outS, sizeof(int) * d);
            for (int i = 0; i < d; i++) Si[i] = ginv(S[i]);
            if (full_ok()) ok = 1;
        }
        if (ok) {
            have = 1;
            bestN = c;
            bestT = t;
            memcpy(bestS, outS, sizeof(int) * d);
            cur = c;
            if (step < 64) step *= 2;
        } else if (step > 1) {
            step /= 2;
        }
    }

    if (!have) { printf("0 0\n"); return 0; }
    N = bestN;
    set_group(&bestT);
    for (int i = 0; i < d; i++) {
        S[i] = bestS[i];
        Si[i] = ginv(S[i]);
    }
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + gmul(g, S[i]));
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
    """Algebraic candidates that may be valid for diameter D (may be empty)."""
    out = []
    try:
        if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
            out.append(lib.projective_plane_incidence(d - 1))
    except Exception:
        pass
    try:
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            out.append(lib.araujo_lopez_graph(d - 2))
    except Exception:
        pass
    try:
        if D >= 4:
            q = _largest_prime_power_le(min(d - 1, 9))
            if q is not None and q >= 2:
                out.append(_gq_w(q))
    except Exception:
        pass
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
