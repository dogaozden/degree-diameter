import itertools
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New construction family: lifts over AFFINE groups H x| GF(q).
#
# Elements are maps x -> a*x + b with a in H (a subgroup of order k of GF(q)*)
# and b in GF(q). These groups are not cyclic-by-cyclic semidirect products
# when q is not prime (e.g. GF(27) with k=13, GF(49) with k=8, GF(361) with
# k=1 is the elementary abelian group Z_19^2). The Python side builds the full
# multiplication table and the C engine searches voltage lifts over that
# table, so it does not depend on the group being cyclic or semidirect.
#
# Lift: base graph with K A-blocks and K B-blocks, DEG layers. Layer l is a
# permutation of blocks, and each dart (i, j, s) joins A_{i,g} to B_{j,g*s}.
# Left multiplication is an automorphism, so the diameter check only needs
# BFS from the 2K block representatives.
#
# Safe fallbacks (K_{d,d}, PG(2,q) incidence, Araujo-Pardo-Lopez, W(q)) are
# always kept, and every returned graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 24
#define POOLP 0.6
#define BRK 150
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

static int DEG, DIAM, K, G, T, NV;
static int *MT;                       /* group multiplication table, MT[x*G+y] = x*y, identity 0 */
static int *dI, *dJ, *dS, *bestJ, *bestS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp;
static long long *wt, *unc;
static long long wsum_w, last_w;
static int emitted;
static int *best_e;
static int best_m;
static int pool_n;
static int *poolJ, *poolS;
static long long *poolC;

static int read_group(void) {
    long long n, m;
    if (scanf("%lld %lld", &n, &m) != 2) return 0;
    if (n < 1 || n > 2000 || m != n * n) return 0;
    G = (int)n;
    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (long long i = 0; i < m; i++) MT[i] = -1;
    for (long long i = 0; i < m; i++) {
        long long a, b;
        if (scanf("%lld %lld", &a, &b) != 2) return 0;
        if (a < 0 || a >= m || b < 0 || b >= n) return 0;
        MT[a] = (int)b;
    }
    for (int y = 0; y < G; y++) if (MT[y] != y) return 0;
    for (int x = 0; x < G; x++) if (MT[x * G] != x) return 0;
    char *seen = malloc((size_t)G);
    for (int s = 0; s < G; s++) {
        memset(seen, 0, (size_t)G);
        for (int g = 0; g < G; g++) {
            int v = MT[g * G + s];
            if (v < 0 || v >= G || seen[v]) { free(seen); return 0; }
            seen[v] = 1;
        }
    }
    free(seen);
    return 1;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = MT[g * G + s];
}

/* Returns the true cost (uncovered ordered pairs over block reps). Sets unc[r] and last_w. */
static long long eval_cost(void) {
    int N = NV;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
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
        unc[r] = N - count;
        total += unc[r];
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void reset_weights(void) {
    for (int r = 0; r < 2 * K; r++) wt[r] = 1;
    wsum_w = 2 * K;
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
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
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

/* Annealing on the weighted cost with breakout weight bumps.
   The caller must have just called eval_cost(). Returns the best true cost; the
   best state goes to bestJ/bestS. */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
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
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
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

static void emit_best(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    best_m = m;
}

static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (pool_n < POOLMAX) {
        slot = pool_n++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (poolC[i] > poolC[slot]) slot = i;
        if (poolC[slot] <= cost) return;
    }
    poolC[slot] = cost;
    memcpy(poolJ + (size_t)slot * T, J, sizeof(int) * (size_t)T);
    memcpy(poolS + (size_t)slot * T, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int bi = rnd_int(pool_n);
    for (int s = 0; s < 2; s++) {
        int c = rnd_int(pool_n);
        if (poolC[c] < poolC[bi]) bi = c;
    }
    return bi;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit K\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    if (DEG < 1 || DIAM < 1 || K < 1 || K > MAXK || !read_group()) {
        printf("0 0\n");
        return 0;
    }
    T = DEG * K;
    NV = 2 * K * G;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)NV * DEG);
    cnt = malloc(sizeof(int) * (size_t)NV);
    stamp = calloc((size_t)NV, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NV);
    nx = malloc(sizeof(int) * (size_t)NV);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    poolJ = malloc(sizeof(int) * (size_t)POOLMAX * T);
    poolS = malloc(sizeof(int) * (size_t)POOLMAX * T);
    poolC = malloc(sizeof(long long) * POOLMAX);
    for (int t = 0; t < T; t++) dI[t] = t % K;
    emitted = 0;
    best_e = NULL;
    best_m = 0;
    pool_n = 0;
    curstamp = 0;
    reset_weights();

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (!emitted && elapsed() < DEADLINE) {
        int use_pool = (pool_n > 0 && rnd_unit() < POOLP);
        if (use_pool) {
            int pi = pick_pool();
            memcpy(dJ, poolJ + (size_t)pi * T, sizeof(int) * (size_t)T);
            memcpy(dS, poolS + (size_t)pi * T, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
        } else {
            random_init();
        }
        reset_weights();
        long long cst = eval_cost();
        long long bc = run_sa(use_pool ? ILS_ITERS : ITERS, use_pool ? 0.35 : 1.0, cst);
        if (bc == 0) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(dS, bestS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            emit_best();
            emitted = 1;
            break;
        }
        pool_add(bc, bestJ, bestS);
    }

    if (emitted) {
        printf("%d %d\n", NV, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

_GMAX = 700
_GF_CACHE = {}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# New family: affine groups H x| GF(q) as multiplication tables.
# ----------------------------------------------------------------------------

def _field(q):
    if q not in _GF_CACHE:
        _GF_CACHE[q] = lib.GF(q)
    return _GF_CACHE[q]


def _affine_table(q, k):
    """Multiplication table of H x| GF(q), |H| = k, H the order-k subgroup of GF(q)*.

    Element index ia*q + b stands for x -> H[ia]*x + b. Identity is index 0.
    Product: (a1, b1)(a2, b2) = (a1*a2, a1*b2 + b1).
    Returns (order, table) with table an int64 array of shape (G, G).
    """
    F = _field(q)
    h = F.pow(F.primitive_element(), (q - 1) // k)
    H = [F.pow(h, i) for i in range(k)]          # H[0] = 1
    Hs = np.array(H, dtype=np.int64)
    hidx = np.full(q, -1, dtype=np.int64)
    hidx[Hs] = np.arange(k, dtype=np.int64)
    pa = hidx[F.mul_table[Hs[:, None], Hs[None, :]]]   # index of H[i]*H[j] in H
    G = q * k
    x = np.arange(G, dtype=np.int64)
    ia = x // q
    b = x % q
    IA1, B1 = ia[:, None], b[:, None]
    IA2, B2 = ia[None, :], b[None, :]
    ia_prod = pa[IA1, IA2]
    b_prod = F.add_table[F.mul_table[Hs[IA1], B2], B1]
    table = ia_prod * q + b_prod
    return G, table


def _group_candidates(best_n, moore):
    """(order, K, q, k) for affine groups whose 2*K*order can beat best_n, nearest the anchor first."""
    out = []
    for K in (1, 2, 3, 4):
        lo = max(best_n // (2 * K) + 1, int(0.42 * moore / (2 * K)))
        if lo > _GMAX:
            continue
        hi = min(_GMAX, lo + max(lo // 5, 6))
        for q in range(2, hi + 1):
            if not lib.is_prime_power(q):
                continue
            for k in range(1, q):
                if (q - 1) % k:
                    continue
                G = q * k
                if lo <= G <= hi:
                    out.append((G, K, q, k))
    out.sort()
    if len(out) > 14:
        pick = sorted({int(round(i)) for i in np.linspace(0, len(out) - 1, 14)})
        out = [out[i] for i in pick]
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    cands = _group_candidates(best_n, moore)
    run_idx = 0
    while cands:
        used = time.monotonic() - start
        remaining = 0.88 * time_limit - used - 1.5
        cands = [c for c in cands if 2 * c[1] * c[0] > best_n]
        if not cands or remaining < 1.0:
            break
        G, K, q, k = cands.pop(0)
        share = remaining / (len(cands) + 1)
        slice_t = max(1.0, min(share, remaining))
        slice_t = min(slice_t, time_limit - used - 4.5)
        if slice_t < 0.8:
            break
        hard = slice_t + 3.0
        run_idx += 1
        try:
            Gt, table = _affine_table(q, k)
            edges = list(zip(range(Gt * Gt), table.ravel().tolist()))
            out = lib.run_c(C_SOURCE, [d, D, seed * 7919 + run_idx, f"{slice_t:.2f}", K],
                            stdin_graph=(Gt, edges), timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
