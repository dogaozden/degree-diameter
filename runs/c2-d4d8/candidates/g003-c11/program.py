"""Base-lift search for d-regular bipartite graphs with diameter at most D.

Construction: pick a small d-regular bipartite multigraph B with h vertices per side (a projective
plane incidence graph, a generalized quadrangle W(d-1) incidence graph, or a random multigraph).
Lift it over a metacyclic group G = Z_m x| Z_t of order n. The lift has 2h*n vertices. Base edge
(a, b) with voltage g joins A(a,x) to B(b, x*g) for every x. Left multiplication by G is an
automorphism, so the lift has diameter at most D iff BFS from each of the 2h base vertices reaches
everything within D. Simulated annealing on the voltages minimises unreachable pairs plus a
duplicate-edge penalty. The target order grows after each success.

Safe fallback: the best algebraic start (projective plane, Araujo-Pardo-Lopez, or W(q)), or
K_{d,d}, which is checked with lib.is_valid before it is returned.
"""
import itertools
import random
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

#define MAXN 1100
#define MAXH 128
#define MAXD 8
#define MAXE (MAXH * MAXD)
#define MAXV (2 * MAXH * MAXN)
#define DUPW 40

static int d, D, h, E;
static int EA[MAXE], EB[MAXE], VG[MAXE];
static int incA[MAXH][MAXD], incB[MAXH][MAXD];
static int GN;
static int rp[MAXN];
static int INV[MAXN];
static uint16_t MT[MAXN * MAXN];
static int bd[MAXV], bq[MAXV];
static double t_end;
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

static long pw(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Group Z_m x|_r Z_t, element a*t+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is code 0. */
static void build_group(int m, int t, int r) {
    GN = m * t;
    rp[0] = 1 % m;
    for (int b = 1; b < t; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < GN; x++) {
        int a1 = x / t, b1 = x % t;
        for (int y = 0; y < GN; y++) {
            int a2 = y / t, b2 = y % t;
            int na = (int)(((long)a1 + (long)rp[b1] * a2) % m);
            int nb = (b1 + b2) % t;
            MT[x * GN + y] = (uint16_t)(na * t + nb);
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (MT[x * GN + y] == 0) { INV[x] = y; break; }
}

static void pick_group(int n, int *pm, int *pt, int *pr) {
    int divs[64];
    int nd = 0;
    for (int t = 1; t <= n && nd < 64; t++)
        if (n % t == 0) divs[nd++] = t;
    int t = divs[rndint(nd)];
    int m = n / t;
    int r = (m > 1) ? 1 : 0;
    if (m > 1) {
        for (int tr = 0; tr < 300; tr++) {
            int cand = 1 + rndint(m - 1);
            if (gcd_i(cand, m) == 1 && pw(cand, t, m) == 1) { r = cand; break; }
        }
    }
    *pm = m;
    *pt = t;
    *pr = r;
}

/* Cost = unreachable pairs from the 2h base sources + duplicate-dart penalty. */
static long cost_eval(void) {
    long dup = 0;
    for (int e = 0; e < E; e++)
        for (int f = e + 1; f < E; f++)
            if (EA[e] == EA[f] && EB[e] == EB[f] && VG[e] == VG[f]) dup++;
    int V = 2 * h * GN;
    long total = 0;
    for (int s = 0; s < 2 * h; s++) {
        for (int v = 0; v < V; v++) bd[v] = -1;
        int head = 0, tail = 0;
        int src = s * GN;
        bd[src] = 0;
        bq[tail++] = src;
        while (head < tail) {
            int v = bq[head++];
            int dv = bd[v];
            if (dv >= D) continue;
            int b = v / GN;
            int x = v - b * GN;
            if (b < h) {
                for (int t = 0; t < d; t++) {
                    int e = incA[b][t];
                    int u = (h + EB[e]) * GN + MT[x * GN + VG[e]];
                    if (bd[u] < 0) { bd[u] = dv + 1; bq[tail++] = u; }
                }
            } else {
                int j = b - h;
                for (int t = 0; t < d; t++) {
                    int e = incB[j][t];
                    int u = EA[e] * GN + MT[x * GN + INV[VG[e]]];
                    if (bd[u] < 0) { bd[u] = dv + 1; bq[tail++] = u; }
                }
            }
        }
        total += V - tail;
    }
    return total + dup * DUPW;
}

static const double T0 = 4.0, T1 = 0.2;

static int anneal(double until) {
    for (int e = 0; e < E; e++) VG[e] = rndint(GN);
    long cur = cost_eval();
    double start = now();
    double span = until - start;
    if (span <= 0) return cur == 0;
    double T = T0;
    for (long it = 0;; it++) {
        if (cur == 0) return 1;
        if ((it & 7) == 0) {
            double tn = now();
            if (tn >= until) return 0;
            double frac = (tn - start) / span;
            T = T0 * pow(T1 / T0, frac);
        }
        int e = rndint(E);
        int old = VG[e];
        int ng = rndint(GN);
        if (ng == old) continue;
        VG[e] = ng;
        long nc = cost_eval();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) cur = nc;
        else VG[e] = old;
    }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit n_start n_cap\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long n_start = atol(argv[5]);
    long n_cap = atol(argv[6]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.93;
    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    long nn, mm;
    if (scanf("%ld %ld", &nn, &mm) != 2 || nn < 2 || (nn & 1)) { printf("0 0\n"); return 0; }
    h = (int)(nn / 2);
    if (h > MAXH || mm != (long)h * d || mm > MAXE) { printf("0 0\n"); return 0; }
    E = (int)mm;
    int cntA[MAXH], cntB[MAXH];
    memset(cntA, 0, sizeof cntA);
    memset(cntB, 0, sizeof cntB);
    for (int e = 0; e < E; e++) {
        long u, v;
        if (scanf("%ld %ld", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= h || v < h || v >= 2 * h) { printf("0 0\n"); return 0; }
        int a = (int)u, b = (int)(v - h);
        if (cntA[a] >= d || cntB[b] >= d) { printf("0 0\n"); return 0; }
        EA[e] = a;
        EB[e] = b;
        incA[a][cntA[a]++] = e;
        incB[b][cntB[b]++] = e;
    }

    if (n_cap > MAXN) n_cap = MAXN;
    double attempt = limit * 0.06;
    if (attempt < 1.0) attempt = 1.0;
    if (attempt > 5.0) attempt = 5.0;
    long lo_n = n_start < 3 ? 3 : n_start;
    long best_n = 0;
    int have = 0, bm = 0, bt = 1, br = 0;
    static int bVG[MAXE];

    while (now() < t_end) {
        long lo = have ? best_n + 1 : lo_n;
        if (lo > n_cap) break;
        long n = lo + rndint(4);
        if (n > n_cap) n = n_cap;
        int m, t, r;
        pick_group((int)n, &m, &t, &r);
        build_group(m, t, r);
        double until = now() + attempt;
        if (until > t_end) until = t_end;
        if (anneal(until)) {
            have = 1;
            best_n = n;
            bm = m; bt = t; br = r;
            memcpy(bVG, VG, sizeof(int) * E);
        }
    }

    if (!have) { printf("0 0\n"); return 0; }
    build_group(bm, bt, br);
    memcpy(VG, bVG, sizeof(int) * E);
    int V = 2 * h * GN;
    long cnt = (long)E * GN;
    printf("%d %ld\n", V, cnt);
    for (int e = 0; e < E; e++)
        for (int x = 0; x < GN; x++) {
            int a = EA[e] * GN + x;
            int b = (h + EB[e]) * GN + MT[x * GN + VG[e]];
            printf("%d %d\n", a, b);
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


def _pg_base(d, D):
    """Base (h, edges) from PG(2, d-1) incidence: h points, h lines, d-regular."""
    if D < 3 or d - 1 < 2 or not lib.is_prime_power(d - 1):
        return None
    n, edges = lib.projective_plane_incidence(d - 1)
    h = n // 2
    return h, [(u, v - h) for u, v in edges]


def _gq_base(d, D):
    """Base (h, edges) from the W(d-1) point-line incidence graph, d-regular."""
    if D < 4 or d - 1 < 2 or not lib.is_prime_power(d - 1):
        return None
    n, edges = _gq_w(d - 1)
    h = n // 2
    return h, [(u, v - h) for u, v in edges]


def _random_base(d, h, rng):
    """Random d-regular bipartite multigraph with h vertices per side, as (a, b) pairs."""
    A = [i for i in range(h) for _ in range(d)]
    B = A[:]
    rng.shuffle(B)
    return [(A[k], B[k]) for k in range(len(A))]


def _base_ok(h, base, d):
    """True if base has h*d edges with indices in range and every vertex of degree d."""
    if h < 1 or len(base) != h * d:
        return False
    deg = [0] * (2 * h)
    for a, b in base:
        if not (0 <= a < h and 0 <= b < h):
            return False
        deg[a] += 1
        deg[h + b] += 1
    return all(x == d for x in deg)


def _keep_better(text, d, D, best):
    """Return the parsed graph from C text if it is valid and larger than best, else best."""
    try:
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            return (n, e)
    except Exception:
        pass
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} or the best algebraic start.
    best = lib.haar_graph(d, range(d))
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 8 or best[0] >= lib.moore_bound(d, D):
        return best

    deadline = t0 + 0.85 * time_limit - 1.0
    budget = deadline - time.monotonic()
    if budget < 3.0:
        return best

    # Bases in priority order: (weight, h, edges).
    bases = []
    pg = _pg_base(d, D)
    if pg is not None:
        bases.append((3.0, pg[0], pg[1]))
    gq = _gq_base(d, D)
    if gq is not None:
        bases.append((2.5, gq[0], gq[1]))
    rng = random.Random(1000003 * (seed + 1) + 97 * d + D)
    for h in (2, 2, 3, 4, 6):
        bases.append((1.0, h, _random_base(d, h, rng)))
    total_w = sum(w for w, _, _ in bases)

    moore = lib.moore_bound(d, D)
    for w, h, base in bases:
        if not _base_ok(h, base, d):
            continue
        n_cap = min(moore // (2 * h), 1100)
        n_start = max(3, best[0] // (2 * h) + 1)
        if n_start > n_cap:
            continue
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        share = min(remaining, budget * w / total_w)
        if share < 2.0:
            continue
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(share, 2), n_start, n_cap],
                             stdin_graph=(2 * h, [(a, h + b) for a, b in base]),
                             timeout=share + 10)
            best = _keep_better(text, d, D, best)
        except Exception:
            pass
    return best
