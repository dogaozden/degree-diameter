import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an explicitly given finite group.
#
# Python passes the multiplication table of one group G (identity = element 0)
# on stdin, in the graph text format: "G G*G", then for x, y in order the line
# "x mul(x,y)". The table can be any group, including non-metabelian ones such
# as Heisenberg groups and affine groups, which the earlier semidirect-only
# engine could not express.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer l uses K darts whose j-values form a
# permutation, so every vertex has degree DEG. Left multiplication is an
# automorphism, so diameter <= DIAM iff a BFS of depth DIAM from each of the
# 2K block representatives covers all vertices.
#
# Search: simulated annealing on the number of uncovered (source, vertex) pairs.
# The first zero-cost configuration is printed as the graph and the run ends.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 30000
#define MAXK 8

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static void fail(void) {
    printf("0 0\n");
    exit(0);
}

static int DEG, DIAM, K, G, T, N, IDN;
static int *tab, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = tab[g * G + s];
}

static void random_init(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

/* Number of uncovered (source, vertex) pairs over the 2K block representatives. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (t1 % K == t2 % K && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = (t % K) * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G + IDN;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        total += N - count;
    }
    return total;
}

static void emit_and_exit(void) {
    printf("%d %d\n", N, T * G);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", (t % K) * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
    fflush(stdout);
    exit(0);
}

static void anneal_loop(void) {
    while (elapsed() < DEADLINE) {
        random_init();
        long long cost = eval_cost();
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 127) == 0 && elapsed() > DEADLINE) break;
            double temp = 3.0 * (1.0 - (double)it / ITERS) + 0.05;
            if (K > 1 && rnd_unit() < 0.25) {
                int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                long long c2 = eval_cost();
                if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                } else {
                    tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
                }
            } else {
                int t = rnd_int(T);
                int olds = dS[t];
                int news = rnd_int(G);
                if (news == olds) continue;
                dS[t] = news;
                build_perm(t);
                long long c2 = eval_cost();
                if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                } else {
                    dS[t] = olds;
                    build_perm(t);
                }
            }
        }
        if (cost == 0) emit_and_exit();
    }
    printf("0 0\n");
}

int main(int argc, char **argv) {
    timespec_get(&T0, TIME_UTC);
    if (argc < 6) fail();
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) fail();
    G = n;
    if (DEG < 1 || DIAM < 1 || K < 1 || K > MAXK || G < 2) fail();
    if ((long long)m != (long long)G * G) fail();
    tab = malloc(sizeof(int) * (size_t)m);
    for (int k = 0; k < m; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) fail();
        if (v < 0 || v >= G) fail();
        tab[k] = v;
    }

    IDN = -1;
    for (int e = 0; e < G && IDN < 0; e++) {
        int ok = 1;
        for (int x = 0; x < G && ok; x++)
            if (tab[e * G + x] != x || tab[x * G + e] != x) ok = 0;
        if (ok) IDN = e;
    }
    if (IDN < 0) fail();

    N = 2 * K * G;
    T = DEG * K;
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    anneal_loop();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

GMAX = 420        # largest group order tried (keeps the stdin table manageable)
MAX_CANDS = 60    # group candidates tried per call


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
# Group construction: multiplication tables for several non-cyclic families.
# ----------------------------------------------------------------------------

def _is_prime(n):
    return n >= 2 and all(n % i for i in range(2, int(n ** 0.5) + 1))


def _table(elems, mul, ident):
    """Multiplication table with the identity relabelled to index 0. Returns (G, flat table)."""
    rest = [x for x in elems if x != ident]
    order = [ident] + rest
    idx = {x: i for i, x in enumerate(order)}
    G = len(order)
    tab = [idx[mul(x, y)] for x in order for y in order]
    return G, tab


def _spec_table(spec):
    kind = spec[0]
    if kind == "sd":
        _, m, k, r = spec
        order, mul, _ = lib.semidirect_group(m, k, r)
        return _table(range(order), mul, 0)
    if kind == "heis":
        p = spec[1]

        def mul(x, y):
            return ((x[0] + y[0]) % p, (x[1] + y[1]) % p, (x[2] + y[2] + x[0] * y[1]) % p)

        return _table(list(itertools.product(range(p), repeat=3)), mul, (0, 0, 0))
    if kind == "agl":
        q = spec[1]

        def mul(x, y):
            return (x[0] * y[0] % q, (x[0] * y[1] + x[1]) % q)

        return _table([(a, b) for a in range(1, q) for b in range(q)], mul, (1, 0))
    raise ValueError(f"unknown group spec {spec}")


def _specs_of_order(G, rng):
    """Group specs of order G: semidirect products (incl. direct and cyclic), Heisenberg, affine."""
    specs = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [1]
        if k > 1 and m >= 3:
            for _ in range(30):
                r = rng.randrange(2, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m and r not in rs:
                    rs.append(r)
                    if len(rs) >= 3:
                        break
        for r in rs:
            specs.append(("sd", m, k, r))
    p = round(G ** (1 / 3))
    for pp in (p - 1, p, p + 1):
        if pp >= 2 and pp ** 3 == G and _is_prime(pp):
            specs.append(("heis", pp))
    q = int((1 + math.sqrt(1 + 4 * G)) / 2)
    if q * (q - 1) == G and _is_prime(q):
        specs.append(("agl", q))
    rng.shuffle(specs)
    return specs


def _candidates(best_n, target, rng):
    """Group candidates (n, K, G, spec) with n > best_n, nearest to target first."""
    out = []
    for K in (1, 2, 3, 4):
        lo = max(2, best_n // (2 * K) + 1)
        for G in range(lo, GMAX + 1):
            n = 2 * K * G
            if n <= best_n:
                continue
            for spec in _specs_of_order(G, rng)[:3]:
                out.append((abs(n - target), rng.random(), n, K, G, spec))
    out.sort(key=lambda t: (t[0], t[1]))
    return [(n, K, G, spec) for _, _, n, K, G, spec in out[:MAX_CANDS]]


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C group-lift search over several groups.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Group-lift search: try candidate groups, nearest the target order first.
    # Each C run has its own wall-clock deadline; the margin covers compilation,
    # parsing and validation.
    budget_end = 0.92 * time_limit - 1.5
    rng = random.Random(seed * 7919 + d * 101 + D)
    target = max(best_n + 2, int(0.45 * moore))
    for n_c, K, G, spec in _candidates(best_n, target, rng):
        left = budget_end - (time.monotonic() - start)
        if left < 2.0:
            break
        if n_c <= best_n:
            continue
        slice_t = min(4.0, left - 1.0)
        try:
            Gt, tab = _spec_table(spec)
            if Gt != G:
                continue
            edges = [(x, tab[x * G + y]) for x in range(G) for y in range(G)]
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{slice_t:.2f}", K],
                            stdin_graph=(G, edges), timeout=slice_t + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
