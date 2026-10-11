"""Bi-Cayley and lifted-group search for bipartite graphs with degree d and diameter D.

Approach: a table-driven C annealer. Each job fixes a finite group G (semidirect
products, direct products with a cyclic factor, cyclic groups) and a base size K.
Vertices are A_{i,g} = i*G+g and B_{j,h} = (K+j)*G+h, and dart (i, j, s) joins
A_{i,g} to B_{j,g*s}. Each of the DEG layers is a permutation of the K base
vertices. Left multiplication is an automorphism, so diameter <= D is checked by
BFS from the 2K block representatives only. Jobs are ordered by target order, so
the first hit is the smallest group order that beats the current best.
"""
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
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 8000
#define TSCALE 0.03
#define KMAX 4
#define GMAX 1200

static struct timespec T0;
static double DEADLINE;
static uint64_t rs[2];

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

static int DEG, DIAM, K, G, T, N;
static int *mt;
static int *dI, *dJ, *dS, *perm;
static int *rJ, *rS, *eJ, *eS;
static int *adj, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;

/* perm for dart t: g -> g * s, using the table mt[x*G+y] = x*y. */
static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = mt[(size_t)g * G + s];
}

/* Sum over block representatives of vertices not reached within DIAM steps.
   Returns BIGC if two darts coincide (that would create a duplicate edge). */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = r * G;
        stamp[r * G] = curstamp;
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

/* Each layer l uses darts t = l*K + i, with dI = i and dJ a random permutation. */
static void random_init(void) {
    int p[KMAX];
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
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

/* Simulated annealing on the total uncovered count. Best state goes to rJ/rS. */
static long long anneal(long long cost) {
    long long bestc = cost;
    memcpy(rJ, dJ, sizeof(int) * (size_t)T);
    memcpy(rS, dS, sizeof(int) * (size_t)T);
    double temp0 = TSCALE * (double)N;
    for (int it = 0; it < ITERS && bestc > 0; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        double temp = temp0 * (1.0 - (double)it / ITERS) + 0.03;
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
            int olds = dS[t], news = rnd_int(G);
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
        if (cost < bestc) {
            bestc = cost;
            memcpy(rJ, dJ, sizeof(int) * (size_t)T);
            memcpy(rS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void emit_state(const int *J, const int *S) {
    memcpy(dJ, J, sizeof(int) * (size_t)T);
    memcpy(dS, S, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    printf("%d %d\n", N, T * G);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", dI[t] * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t sd = strtoull(argv[4], NULL, 10);
    DEADLINE = atof(argv[5]);
    if (DEG < 1 || DIAM < 1 || K < 1 || K > KMAX) {
        printf("0 0\n");
        return 0;
    }

    /* Input: "G G*G" then G*G lines "x y" with x = table entry (row-major). */
    long long hn, hm;
    if (scanf("%lld %lld", &hn, &hm) != 2 || hn < 2 || hn > GMAX || hm != hn * hn) {
        printf("0 0\n");
        return 0;
    }
    G = (int)hn;
    mt = malloc(sizeof(int) * (size_t)hm);
    for (long long i = 0; i < hm; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2 || a < 0 || a >= G) {
            printf("0 0\n");
            return 0;
        }
        mt[i] = a;
    }
    for (int x = 0; x < G; x++)
        if (mt[x] != x || mt[(size_t)x * G] != x) {
            printf("0 0\n");
            return 0;
        }

    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    rJ = malloc(sizeof(int) * (size_t)T);
    rS = malloc(sizeof(int) * (size_t)T);
    eJ = malloc(sizeof(int) * (size_t)T);
    eS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * (size_t)G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) dI[t] = t % K;

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    long long ecost = BIGC;
    int have = 0;
    while (elapsed() < DEADLINE) {
        if (have && rnd_unit() < 0.5) {
            memcpy(dJ, eJ, sizeof(int) * (size_t)T);
            memcpy(dS, eS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(5));
        } else {
            random_init();
        }
        long long c = eval_cost();
        long long rb = anneal(c);
        if (rb == 0) {
            emit_state(rJ, rS);
            return 0;
        }
        if (rb < ecost) {
            ecost = rb;
            memcpy(eJ, rJ, sizeof(int) * (size_t)T);
            memcpy(eS, rS, sizeof(int) * (size_t)T);
            have = 1;
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
# Group specifications: ('sd', m, k, r) = Z_m x| Z_k, or ('prod', s1, s2).
# ----------------------------------------------------------------------------

def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _sd_list(G, rng, extra):
    out = []
    for k in _divisors(G):
        m = G // k
        if m < 2:
            continue
        out.append(("sd", m, k, 1))
        if k >= 2:
            units = [r for r in range(2, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(units)
            for r in units[:extra]:
                out.append(("sd", m, k, r))
    return out


def _specs(G, rng, cap):
    specs = _sd_list(G, rng, 2)
    for o1 in _divisors(G):
        if 6 <= o1 <= G // 2 and G // o1 >= 2:
            inner = [s for s in _sd_list(o1, rng, 1) if s[2] >= 2 and s[3] != 1]
            if inner:
                specs.append(("prod", rng.choice(inner), ("sd", G // o1, 1, 1)))
    rng.shuffle(specs)
    return specs[:cap]


def _mul_of(spec):
    if spec[0] == "sd":
        order, mul, _ = lib.semidirect_group(spec[1], spec[2], spec[3])
        return order, mul
    o1, m1 = _mul_of(spec[1])
    o2, m2 = _mul_of(spec[2])

    def mul(x, y):
        a, b = divmod(x, o2)
        c, e = divmod(y, o2)
        return m1(a, c) * o2 + m2(b, e)

    return o1 * o2, mul


def _table(spec):
    order, mul = _mul_of(spec)
    return order, [mul(x, y) for x in range(order) for y in range(order)]


def _make_jobs(best_n, rng, cap=80):
    """Jobs (K, G, spec) sorted by target vertex count 2KG, smallest first."""
    jobs = []
    for n in range(best_n + 1, best_n + 41):
        group = []
        for K in (1, 2, 3):
            if n % (2 * K) == 0 and n // (2 * K) >= 2:
                G = n // (2 * K)
                for spec in _specs(G, rng, 6):
                    group.append((K, G, spec))
        rng.shuffle(group)
        jobs.extend(group)
        if len(jobs) >= cap:
            break
    return jobs[:cap]


# ----------------------------------------------------------------------------
# Driver.
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    deadline = start + 0.88 * time_limit - 1.0
    rng = random.Random(seed * 1000003 + d * 101 + D)
    jobs = _make_jobs(best_n, rng)
    for idx, (K, G, spec) in enumerate(jobs):
        rem = deadline - time.monotonic()
        if rem < 2.0 or best_n >= lib.moore_bound(d, D):
            break
        slice_t = min(max(2.0, min(6.0, rem / 4.0)), rem - 1.0)
        try:
            order, table = _table(spec)
            if order != G:
                continue
            # The graph text carries the group table: each pair's first entry is one table value.
            out = lib.run_c(C_SOURCE, [d, D, K, seed * 1000 + idx, f"{slice_t:.2f}"],
                            stdin_graph=(G, [(v, 0) for v in table]),
                            timeout=slice_t + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            continue

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
