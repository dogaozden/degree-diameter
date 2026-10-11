import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley / voltage lifts over an arbitrary finite group given by
# its multiplication table (read from stdin). Base graph has K A-vertices and
# K B-vertices. Dart (i, j, s) joins A_i,g to B_j,g*s for all g in the group.
# Left multiplication is an automorphism, so diameter <= D iff BFS of depth D
# from the 2K block representatives reaches everything.
#
# Stdin: "G G*G" then G*G lines "x*G+y z" with z = x*y (identity must be 0).
# Argv: d D seed time_limit lo_n. Only K with 2*K*G >= lo_n are tried.
# Stops at the first valid graph, otherwise prints "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define KMAX 4
#define ITERS 5000
#define ILS_ITERS 2500

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

static int DEG, DIAM, G, K, T, N, MAXT, MAXN;
static int *TAB;
static int *dI, *dJ, *dS, *bestJ, *bestS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *eJ, *eS;
static long long ecost[KMAX + 1];
static int curstamp;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = TAB[(size_t)g * G + s];
}

static void build_all(void) {
    for (int t = 0; t < T; t++) build_perm(t);
}

static void setup_K(int k) {
    K = k;
    T = DEG * K;
    N = 2 * K * G;
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

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
            if (cnt[a] >= DEG || cnt[b] >= DEG) return BIGC;
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
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
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    build_all();
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
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

static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05);
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
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
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void emit(void) {
    int m = T * G;
    printf("%d %d\n", N, m);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", dI[t] * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
}

static int check_group(void) {
    int *seen = calloc((size_t)G, sizeof(int));
    if (!seen) return 0;
    int ok = 1;
    for (int s = 0; s < G && ok; s++) {
        for (int g = 0; g < G; g++) {
            int v = TAB[(size_t)g * G + s];
            if (v < 0 || v >= G || seen[v] == s + 1) { ok = 0; break; }
            seen[v] = s + 1;
        }
    }
    free(seen);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit lo_n < group\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    long long lo_n = argc > 5 ? atoll(argv[5]) : 0;

    int gn = 0, gm = 0;
    if (scanf("%d %d", &gn, &gm) != 2 || gn < 1 || (long long)gm != (long long)gn * gn) {
        printf("0 0\n");
        return 0;
    }
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    G = gn;
    TAB = malloc(sizeof(int) * (size_t)G * G);
    for (size_t i = 0; i < (size_t)G * G; i++) TAB[i] = -1;
    for (int i = 0; i < gm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= G * G) { printf("0 0\n"); return 0; }
        TAB[u] = v;
    }
    if (!check_group()) {
        printf("0 0\n");
        return 0;
    }

    int allow[KMAX], na = 0;
    for (int k = 1; k <= KMAX; k++) {
        long long nn = 2LL * k * G;
        if (nn >= lo_n) allow[na++] = k;
    }
    if (na == 0) {
        printf("0 0\n");
        return 0;
    }

    MAXT = DEG * KMAX;
    MAXN = 2 * KMAX * G;
    dI = malloc(sizeof(int) * (size_t)MAXT);
    dJ = malloc(sizeof(int) * (size_t)MAXT);
    dS = malloc(sizeof(int) * (size_t)MAXT);
    bestJ = malloc(sizeof(int) * (size_t)MAXT);
    bestS = malloc(sizeof(int) * (size_t)MAXT);
    eJ = malloc(sizeof(int) * (size_t)(KMAX + 1) * MAXT);
    eS = malloc(sizeof(int) * (size_t)(KMAX + 1) * MAXT);
    perm = malloc(sizeof(int) * (size_t)MAXT * G);
    adj = malloc(sizeof(int) * (size_t)MAXN * DEG);
    cnt = malloc(sizeof(int) * (size_t)MAXN);
    stamp = calloc((size_t)MAXN, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)MAXN);
    nx = malloc(sizeof(int) * (size_t)MAXN);
    for (int k = 0; k <= KMAX; k++) ecost[k] = BIGC;
    curstamp = 0;

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int Kc = (rnd_unit() < 0.6) ? allow[0] : allow[rnd_int(na)];
        setup_K(Kc);
        int use_elite = (ecost[Kc] < BIGC) && (rnd_unit() < 0.5);
        if (use_elite) {
            memcpy(dJ, eJ + (size_t)Kc * MAXT, sizeof(int) * (size_t)T);
            memcpy(dS, eS + (size_t)Kc * MAXT, sizeof(int) * (size_t)T);
            build_all();
            perturb(2 + rnd_int(4));
            build_all();
        } else {
            random_init();
        }
        long long cost = eval_cost();
        long long bc = run_sa(use_elite ? ILS_ITERS : ITERS, use_elite ? 0.35 : 1.0, cost);
        if (bc == 0) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(dS, bestS, sizeof(int) * (size_t)T);
            build_all();
            if (eval_cost() == 0) {
                emit();
                return 0;
            }
        }
        if (bc < ecost[Kc]) {
            ecost[Kc] = bc;
            memcpy(eJ + (size_t)Kc * MAXT, bestJ, sizeof(int) * (size_t)T);
            memcpy(eS + (size_t)Kc * MAXT, bestS, sizeof(int) * (size_t)T);
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Baseline families (safe fallbacks).
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
# Finite groups as multiplication functions on 0..n-1 with identity 0.
# Families: cyclic, abelian non-cyclic, Heisenberg-type p^3 (non-metacyclic),
# metacyclic Z_m x| Z_k, and products (group of order n/j) x Z_j.
# ----------------------------------------------------------------------------

GMAX = 300      # largest group order given to C (table has G*G entries)
KP = 3          # base-graph size used to pick the group order for a target
KMAX = 4        # must match KMAX in C_SOURCE


def _make_group(desc):
    """Return (order, mul) for a group descriptor; identity is element 0."""
    kind = desc[0]
    if kind == "cyc":
        n = desc[1]
        return n, (lambda x, y: (x + y) % n)
    if kind == "abel":
        a, b = desc[1], desc[2]

        def mul_ab(x, y):
            u1, v1 = divmod(x, b)
            u2, v2 = divmod(y, b)
            return ((u1 + u2) % a) * b + (v1 + v2) % b
        return a * b, mul_ab
    if kind == "heis":
        p = desc[1]
        pp = p * p

        def mul_h(x, y):
            a1, r1 = divmod(x, pp)
            b1, c1 = divmod(r1, p)
            a2, r2 = divmod(y, pp)
            b2, c2 = divmod(r2, p)
            return ((a1 + a2) % p) * pp + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
        return p ** 3, mul_h
    if kind == "meta":
        m, k, r = desc[1], desc[2], desc[3]
        n, mul, _ = lib.semidirect_group(m, k, r)
        return n, mul
    if kind == "prod":
        hn, hmul = _make_group(desc[1])
        j = desc[2]

        def mul_p(x, y):
            h1, z1 = divmod(x, j)
            h2, z2 = divmod(y, j)
            return hmul(h1, h2) * j + (z1 + z2) % j
        return hn * j, mul_p
    raise ValueError(kind)


def _table(n, mul):
    """Flat multiplication table: tab[x*n + y] = x*y."""
    tab = [0] * (n * n)
    for x in range(n):
        base = x * n
        for y in range(n):
            tab[base + y] = mul(x, y)
    return tab


def _metas(n, rng):
    """Metacyclic descriptors Z_m x| Z_k of order n with k <= 13 and a random non-trivial action."""
    out = []
    for k in range(2, min(n, 13) + 1):
        if n % k:
            continue
        m = n // k
        if m < 3:
            continue
        rs_ = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if rs_:
            out.append(("meta", m, k, rng.choice(rs_)))
    return out


def _descriptors(G, rng):
    """Candidate group descriptors of order G; non-abelian ones are preferred."""
    nonab = []
    c = round(G ** (1.0 / 3))
    for q in (c - 1, c, c + 1):
        if q >= 2 and q ** 3 == G:
            nonab.append(("heis", q))
    nonab += _metas(G, rng)
    for j in range(2, G // 6 + 1):
        if G % j == 0:
            hs = _metas(G // j, rng)
            if hs:
                nonab.append(("prod", rng.choice(hs), j))
    abel = []
    for a in range(2, math.isqrt(G) + 1):
        if G % a == 0 and math.gcd(a, G // a) > 1:
            abel.append(("abel", a, G // a))
    if nonab:
        return nonab
    return abel or [("cyc", G)]


def _targets(lo, hi):
    """Geometric sequence of target vertex counts from lo to hi."""
    out, t = [], float(lo)
    while t <= hi:
        out.append(int(round(t)))
        t *= 1.035
    return out or [lo]


# ----------------------------------------------------------------------------
# Driver: fallbacks first, then group-table voltage search in C for each target.
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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    M = lib.moore_bound(d, D)
    if best_n >= M:
        return best

    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed * 1000003 + d * 101 + D)
    lo = max(12, int(0.30 * M))
    hi = min(M, int(0.50 * M))
    targets = _targets(lo, hi)

    job_no = 0
    for _round in range(4):
        jobs = []
        for nt in targets:
            G = -(-nt // (2 * KP))
            if 2 <= G <= GMAX:
                jobs.append((nt, G))
        if not jobs:
            break
        for idx, (nt, G) in enumerate(jobs):
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                break
            lo_n = max(best_n + 1, int(0.92 * nt))
            if 2 * KMAX * G < lo_n:
                continue
            slice_s = min(max(1.0, remaining / (len(jobs) - idx)), remaining)
            try:
                desc = rng.choice(_descriptors(G, rng))
                n_g, mul = _make_group(desc)
                if n_g != G:
                    continue
                if any(mul(0, y) != y or mul(y, 0) != y for y in range(G)):
                    continue
                tab = _table(G, mul)
                job_no += 1
                out = lib.run_c(C_SOURCE, [d, D, seed * 1009 + job_no, f"{slice_s:.2f}", lo_n],
                                stdin_graph=(G, list(enumerate(tab))),
                                timeout=slice_s + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                continue
        if deadline - time.monotonic() < 1.0:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
