import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over voltages of a lift by the
# semidirect product Z_m x| Z_k2 (element (a,b) coded as a*k2+b, product as in
# lib.semidirect_group). Base graph: k A-vertices and k B-vertices, with d
# layers of permutations, so each vertex has degree exactly d.
# Output: the first valid graph found (cost 0), as "n m" plus edges, else "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXM 1024
#define MAXK 16
#define MAXK2 64

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int d, D, k, m, k2, G, N, M;
static int pw[MAXK2];
/* dart index idx = layer*k + i; its A-end is i = idx % k, its B-end is dj[idx]. */
static int dj[MAXM], ds[MAXM];
static int sj[MAXM], ss[MAXM];
static int *adj, *cnt, *seen, *queue;
static int stamp = 0;

static inline int gmul(int x, int y) {
    int a = x / k2, b = x % k2;
    int c = y / k2, e = y % k2;
    long long t = (long long)pw[b] * c + a;
    return (int)(t % m) * k2 + (b + e) % k2;
}

static void build_adj(void) {
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int idx = 0; idx < M; idx++) {
        int i = idx % k, j = dj[idx], s = ds[idx];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + gmul(g, s);
            if (cnt[a] < d) adj[a * d + cnt[a]++] = b;
            if (cnt[b] < d) adj[b * d + cnt[b]++] = a;
        }
    }
}

/* Number of (representative, vertex) pairs at distance > D, summed over the 2k representatives. */
static long long eval_cost(void) {
    build_adj();
    long long total = 0;
    for (int r = 0; r < 2 * k; r++) {
        int src = r * G;
        stamp++;
        int qh = 0, qt = 0;
        seen[src] = stamp;
        queue[qt++] = src;
        for (int lev = 0; lev < D && qh < qt; lev++) {
            int end = qt;
            while (qh < end) {
                int u = queue[qh++];
                for (int t = 0; t < d; t++) {
                    int v = adj[u * d + t];
                    if (seen[v] != stamp) {
                        seen[v] = stamp;
                        queue[qt++] = v;
                    }
                }
            }
        }
        total += N - qt;
    }
    return total;
}

static int has_dup(void) {
    for (int a = 0; a < M; a++)
        for (int b = 0; b < a; b++)
            if (a % k == b % k && dj[a] == dj[b] && ds[a] == ds[b]) return 1;
    return 0;
}

static void print_graph(void) {
    printf("%d %d\n", N, M * G);
    for (int idx = 0; idx < M; idx++) {
        int i = idx % k, j = dj[idx], s = ds[idx];
        for (int g = 0; g < G; g++)
            printf("%d %d\n", i * G + g, (k + j) * G + gmul(g, s));
    }
}

static int init_state(void) {
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int t = rndint(i + 1), tmp = perm[i];
            perm[i] = perm[t];
            perm[t] = tmp;
        }
        for (int i = 0; i < k; i++) {
            dj[l * k + i] = perm[i];
            ds[l * k + i] = rndint(G);
        }
    }
    int tries = 0;
    while (has_dup()) {
        if (++tries > 200000) return 0;
        ds[rndint(M)] = rndint(G);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    long long rr = atoll(argv[8]);
    if (d < 1 || D < 1 || k < 1 || k > MAXK || m < 1 || k2 < 1 || k2 >= MAXK2
        || d * k > MAXM || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    N = 2 * k * G;
    M = d * k;
    if ((long long)N * d > 50000000LL) {
        printf("0 0\n");
        return 0;
    }
    rr %= m;
    if (rr < 0) rr += m;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * rr % m);

    adj = malloc(sizeof(int) * (size_t)N * d);
    cnt = malloc(sizeof(int) * (size_t)N);
    seen = calloc((size_t)N, sizeof(int));
    queue = malloc(sizeof(int) * (size_t)N);
    if (!adj || !cnt || !seen || !queue) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    clock_t t0 = clock();
    if (!init_state()) {
        printf("0 0\n");
        return 0;
    }
    long long cost = eval_cost();
    if (cost == 0) {
        print_graph();
        return 0;
    }

    long long t = 0;
    double T = 3.0;
    while (1) {
        if ((t & 255) == 0) {
            double frac = (double)(clock() - t0) / CLOCKS_PER_SEC / tl;
            if (frac >= 1.0) break;
            T = 3.0 * (1.0 - frac) + 0.05;
        }
        t++;
        memcpy(sj, dj, sizeof(int) * (size_t)M);
        memcpy(ss, ds, sizeof(int) * (size_t)M);
        if (k > 1 && rnd01() < 0.5) {
            int l = rndint(d), i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int a = l * k + i1, b = l * k + i2;
            int tmp = dj[a];
            dj[a] = dj[b];
            dj[b] = tmp;
        } else {
            ds[rndint(M)] = rndint(G);
        }
        if (has_dup()) {
            memcpy(dj, sj, sizeof(int) * (size_t)M);
            memcpy(ds, ss, sizeof(int) * (size_t)M);
            continue;
        }
        long long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) {
                print_graph();
                return 0;
            }
        } else {
            memcpy(dj, sj, sizeof(int) * (size_t)M);
            memcpy(ds, ss, sizeof(int) * (size_t)M);
        }
    }
    printf("0 0\n");
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
# Group choice and C search driver.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (m, k2, r) describing Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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


def _search_c(d, D, k, m, k2, r, seed, budget):
    """Run the C annealer for one group; return (n, edges) if a valid lift was found, else None.

    May raise RuntimeError if the C program fails; the caller handles that.
    """
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), k, m, k2, r],
                    timeout=budget + 15.0)
    try:
        n, edges = lib.parse_graph_text(out)
    except ValueError:
        return None
    if n < 2 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
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

    # Already at the Moore bound: nothing can be larger, so return at once.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: C annealing over group voltage lifts, 1-3 base vertices per side.
    # Target group orders just above the current best, with a little spread.
    errors = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        m, k2, r = grp
        budget = min(remaining, rng.uniform(1.5, 4.0))
        try:
            res = _search_c(d, D, k, m, k2, r, rng.randrange(1, 2 ** 31), budget)
        except RuntimeError:
            errors += 1
            if errors >= 3:
                break
            continue
        errors = 0
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
