import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

/* Group-voltage lift search.
 * Group: Z_m x| Z_k2, element (a,b) coded a*k2+b, (a,b)*(c,e) = (a + r^b c, b+e).
 * Base: k A-vertices, k B-vertices, d layers. Layer L is a permutation J[L][.] of B-indices,
 * with voltage S[L][i]. Lift: A_{i,g} ~ B_{j, g*s}.  Vertex ids: A_{i,g} = i*G+g,
 * B_{j,h} = (k+j)*G+h.  Left multiplication is an automorphism, so it suffices to BFS from
 * one representative per base vertex. cost = total number of unreached (rep, vertex) pairs.
 * Simulated annealing over voltages and layer permutations; restarts when stuck.
 * Args: d D seed time_limit k m k2 r.  Prints "n m" + edges on success, else "0 0".
 */

#define BIG 1000000000LL

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d, D, k, m, k2, r, G, N;
static int *mt;
static int *J, *S;
static int *adj, *deg, *stamp, *qa, *qb;
static int curstamp = 0;
static clock_t t_start;
static double tlim;

static double elapsed(void) { return (double)(clock() - t_start) / CLOCKS_PER_SEC; }

static void build_group(void) {
    int *powr = malloc(sizeof(int) * (size_t)k2);
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)(((long long)powr[b - 1] * r) % m);
    G = m * k2;
    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++) {
        int ax = x / k2, bx = x % k2;
        for (int y = 0; y < G; y++) {
            int cy = y / k2, dy = y % k2;
            int a = (int)(((long long)ax + (long long)powr[bx] * cy) % m);
            int b = (bx + dy) % k2;
            mt[x * G + y] = a * k2 + b;
        }
    }
    free(powr);
}

static long long evaluate(void) {
    /* Duplicate darts (same i, same j, same s) would give duplicate edges. */
    for (int i = 0; i < k; i++)
        for (int L1 = 0; L1 < d; L1++)
            for (int L2 = L1 + 1; L2 < d; L2++) {
                int t1 = L1 * k + i, t2 = L2 * k + i;
                if (J[t1] == J[t2] && S[t1] == S[t2]) return BIG;
            }
    memset(deg, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < d * k; t++) {
        int i = t % k, j = J[t], s = S[t];
        int base_b = (k + j) * G;
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = base_b + mt[g * G + s];
            adj[(size_t)a * d + deg[a]++] = b;
            adj[(size_t)b * d + deg[b]++] = a;
        }
    }
    long long total = 0;
    int nreps = 2 * k;
    for (int rep = 0; rep < nreps; rep++) {
        int src = (rep < k) ? rep * G : (k + (rep - k)) * G;
        curstamp++;
        int *cur = qa, *nx = qb;
        int fn = 1;
        cur[0] = src;
        stamp[src] = curstamp;
        int count = 1;
        for (int lev = 0; lev < D && fn > 0; lev++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * d;
                for (int e = 0; e < d; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        nx[nn++] = v;
                    }
                }
            }
            count += nn;
            int *tmp = cur;
            cur = nx;
            nx = tmp;
            fn = nn;
        }
        total += N - count;
    }
    return total;
}

static void output_graph(void) {
    printf("%d %d\n", N, d * k * G);
    for (int t = 0; t < d * k; t++) {
        int i = t % k, j = J[t], s = S[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + mt[g * G + s];
            printf("%d %d\n", a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D seed time k m k2 r\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    tlim = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    r = atoi(argv[8]);
    if (d < 1 || D < 1 || k < 1 || m < 1 || k2 < 1) {
        printf("0 0\n");
        return 0;
    }
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();

    build_group();
    if ((long long)G * G > 20000000LL) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * k * G;
    J = malloc(sizeof(int) * (size_t)(d * k));
    S = malloc(sizeof(int) * (size_t)(d * k));
    adj = malloc(sizeof(int) * (size_t)N * (size_t)d);
    deg = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    qa = malloc(sizeof(int) * (size_t)N);
    qb = malloc(sizeof(int) * (size_t)N);

    t_start = clock();
    const int restart_len = 30000;

    for (;;) {
        /* Random start: each layer is a random permutation of the B-indices. */
        for (int L = 0; L < d; L++) {
            for (int i = 0; i < k; i++) J[L * k + i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int tmp = J[L * k + i];
                J[L * k + i] = J[L * k + j];
                J[L * k + j] = tmp;
            }
        }
        for (int t = 0; t < d * k; t++) S[t] = rnd_int(G);
        long long cost = evaluate();
        if (cost == 0) goto ok;

        for (int it = 0; it < restart_len; it++) {
            if ((it & 127) == 0 && elapsed() > tlim) goto fail;
            double T = 0.5 * (1.0 - (double)it / restart_len) + 0.03;
            int t = rnd_int(d * k);
            int L = t / k, i = t % k;
            int mode = (k > 1 && rnd_int(2)) ? 1 : 0;
            int oldS = 0, t2 = -1;
            if (mode == 0) {
                oldS = S[t];
                S[t] = rnd_int(G);
            } else {
                int i2 = rnd_int(k - 1);
                if (i2 >= i) i2++;
                t2 = L * k + i2;
                int tmp = J[t];
                J[t] = J[t2];
                J[t2] = tmp;
            }
            long long c2 = evaluate();
            int accept = 0;
            if (c2 <= cost) accept = 1;
            else if (c2 < BIG && rnd_unit() < exp(-(double)(c2 - cost) / T)) accept = 1;
            if (accept) {
                cost = c2;
                if (cost == 0) goto ok;
            } else {
                if (mode == 0) {
                    S[t] = oldS;
                } else {
                    int tmp = J[t];
                    J[t] = J[t2];
                    J[t2] = tmp;
                }
            }
        }
    }

ok:
    output_graph();
    return 0;
fail:
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Algebraic baselines (unchanged from the parent).
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
# Group parameters for the C engine.
# ----------------------------------------------------------------------------

def _sample_params(G, rng):
    """Return (m, k2, r) with m * k2 = G giving a semidirect product Z_m x| Z_k2, or None."""
    divs = [t for t in range(1, G + 1) if G % t == 0 and G // t >= 2]
    rng.shuffle(divs)
    for k2 in divs[:8]:
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is the safe fallback for D >= 2.
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

    # Main search: C simulated annealing over group voltage lifts.
    # Each call targets a group order just above the current best, and a success
    # raises the target for the next call.
    if D >= 3 and d >= 2 and best_n < lib.moore_bound(d, D):
        failures = 0
        while failures < 3:
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                break
            k = rng.choice([1, 1, 2, 2, 3])
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            G = min(G, 2000)
            params = _sample_params(G, rng)
            if params is None:
                continue
            m, k2, r = params
            slice_t = min(remaining - 0.5, 6.0)
            if slice_t < 0.5:
                break
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, rng.randrange(1, 1 << 31), round(slice_t, 2), k, m, k2, r],
                    timeout=slice_t + 5.0,
                )
                n, e = lib.parse_graph_text(out)
            except (RuntimeError, ValueError):
                failures += 1
                continue
            if n > 0:
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
