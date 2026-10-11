import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over voltage lifts of Z_m x| Z_k2 with k base vertices
# per side. The cost (unreached pairs within distance D from one representative
# per base class) is evaluated in C, which is far faster than the Python version.
# Moves: change one dart voltage, or swap the B-targets of two darts in one layer.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGCOST 1000000000LL
#define MAXD 64

static uint64_t rs = 1;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d, D, k, m, k2, G, N, nd;
static long long iters_per;
static int pw[4096];
static int *di, *dj, *ds, *perm, *nb, *cnt, *stamp, *queue;
static int ptmp[256];
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2, b = x - a * k2;
    int c = y / k2, e = y - c * k2;
    long long ra = ((long long)a + (long long)pw[b] * c) % m;
    int rb = (b + e) % k2;
    return (int)ra * k2 + rb;
}

static void fill_perm(int t) {
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, ds[t]);
}

static long long cost_of(void) {
    for (int t = 0; t < nd; t++)
        for (int u = t + 1; u < nd; u++)
            if (di[t] == di[u] && dj[t] == dj[u] && ds[t] == ds[u]) return BIGCOST;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < nd; t++) {
        int i = di[t], j = dj[t];
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + pm[g];
            if (cnt[a] >= d || cnt[b] >= d) return BIGCOST;
            nb[(size_t)a * d + cnt[a]++] = b;
            nb[(size_t)b * d + cnt[b]++] = a;
        }
    }
    for (int v = 0; v < N; v++)
        if (cnt[v] != d) return BIGCOST;
    long long total = 0;
    for (int r = 0; r < 2 * k; r++) {
        int src = r * G;
        curstamp++;
        int head = 0, tail = 0;
        queue[tail++] = src;
        stamp[src] = curstamp;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = queue[head++];
                const int *nu = nb + (size_t)u * d;
                for (int e = 0; e < d; e++) {
                    int v = nu[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        queue[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void init_state(void) {
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < k; i++) ptmp[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int x = ptmp[i]; ptmp[i] = ptmp[j]; ptmp[j] = x;
        }
        for (int i = 0; i < k; i++) {
            int t = L * k + i;
            di[t] = i;
            dj[t] = ptmp[i];
            ds[t] = rint_(G);
            fill_perm(t);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    long long rr = atoll(argv[8]);
    iters_per = atoll(argv[9]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > 64 || m < 2 || k2 < 1 || k2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    long long Gl = (long long)m * k2;
    if (Gl > 200000) { printf("0 0\n"); return 0; }
    G = (int)Gl;
    long long Nl = 2LL * k * G;
    if (Nl > 200000 || (long long)d * k * G > 4000000LL) { printf("0 0\n"); return 0; }
    N = (int)Nl;
    nd = d * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * rr % m);
    if (((long long)pw[k2 - 1] * rr) % m != 1 % m) { printf("0 0\n"); return 0; }

    di = malloc(sizeof(int) * nd);
    dj = malloc(sizeof(int) * nd);
    ds = malloc(sizeof(int) * nd);
    perm = malloc(sizeof(int) * (size_t)nd * G);
    nb = malloc(sizeof(int) * (size_t)N * d);
    cnt = malloc(sizeof(int) * N);
    stamp = calloc(N, sizeof(int));
    queue = malloc(sizeof(int) * N);
    if (!di || !dj || !ds || !perm || !nb || !cnt || !stamp || !queue) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x12345678ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    while (!found) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        init_state();
        long long cur = cost_of();
        for (long long it = 0; it < iters_per && cur != 0; it++) {
            if ((it & 255) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC >= budget) break;
            double frac = (double)it / (double)iters_per;
            double T = 3.0 * (1.0 - frac) + 0.05;
            if (k >= 2 && rnd01() < 0.2) {
                int L = rint_(d);
                int i1 = rint_(k);
                int i2 = rint_(k - 1);
                if (i2 >= i1) i2++;
                int t1 = L * k + i1, t2 = L * k + i2;
                int tmp = dj[t1]; dj[t1] = dj[t2]; dj[t2] = tmp;
                long long c2 = cost_of();
                if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                    cur = c2;
                } else {
                    tmp = dj[t1]; dj[t1] = dj[t2]; dj[t2] = tmp;
                }
            } else {
                int t = rint_(nd);
                int old = ds[t];
                ds[t] = rint_(G);
                fill_perm(t);
                long long c2 = cost_of();
                if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                    cur = c2;
                } else {
                    ds[t] = old;
                    fill_perm(t);
                }
            }
        }
        if (cur == 0) found = 1;
    }

    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %lld\n", N, (long long)nd * G);
    for (int t = 0; t < nd; t++) {
        for (int g = 0; g < G; g++) {
            int a = di[t] * G + g;
            int b = (k + dj[t]) * G + perm[(size_t)t * G + g];
            printf("%d %d\n", a, b);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python glue: group sampling and calls into the C annealer.
# ----------------------------------------------------------------------------

_ITERS = 20000


def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 == G for a semidirect product Z_m x| Z_k2, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        return m, k2, r
    return None


def _c_search(d, D, seed, budget, timeout, k, m, k2, r, iters):
    """Run the C annealer; return (n, edges) with diameter <= D, or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), k, m, k2, r, iters],
                        timeout=timeout)
        n, edges = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n <= 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + time_limit - 3.0
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: C-side annealing of voltage lifts with 1-3 base vertices per side.
    # Target group orders just above the current best, with a little spread.
    while best_n < lib.moore_bound(d, D):
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        m, k2, r = g
        budget = min(remaining, 6.0)
        timeout = max(1.0, hard - time.monotonic())
        res = _c_search(d, D, rng.randrange(1, 2 ** 31), budget, timeout,
                        k, m, k2, r, _ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
