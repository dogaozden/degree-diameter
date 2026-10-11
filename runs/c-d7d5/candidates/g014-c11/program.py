import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley /
# voltage lift over a finite group G with 2K vertex classes.
#
# Groups:
#   gtype 0: semidirect Z_m x|_r Z_k2 (element (a,b) coded as a*k2+b).
#   gtype 1: PSL(2,p) for prime p (matrices mod +-I), order p(p^2-1)/2.
#   gtype 2: PGL(2,p) for prime p (matrices mod scalars), order p(p^2-1).
# Element 0 is always the identity.
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1. Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e]:
# A_{i,g} ~ B_{j, g*s} for all g. Left multiplication is an automorphism,
# so BFS from the 2K representatives A_{i,e}, B_{j,e} decides the diameter.
#
# Moves: change a voltage, or swap the targets of two darts in one layer.
# Cost = unreached (rep, vertex) pairs + duplicate-edge penalty.
#
# Usage: prog d D K gtype a b r seed slice
#   gtype 0: a = m, b = k2, r = r.   gtype 1/2: a = p, b and r ignored.
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define MAXN (1 << 22)

static int DEG, DIAM, K, G, N, NE;
static int GT, MM, K2;
static int POWR[64];
static int MP, PROJ;
static int *MT = NULL;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int code_of(int a, int b, int c, int d) {
    return ((a * MP + b) * MP + c) * MP + d;
}

static void decode_code(int x, int *a, int *b, int *c, int *d) {
    *d = x % MP; x /= MP;
    *c = x % MP; x /= MP;
    *b = x % MP; x /= MP;
    *a = x;
}

static int canon_code(int a, int b, int c, int d) {
    int best = -1;
    for (int lam = 1; lam < MP; lam++) {
        if (!PROJ && lam != 1 && lam != MP - 1) continue;
        int code = code_of(lam * a % MP, lam * b % MP, lam * c % MP, lam * d % MP);
        if (best < 0 || code < best) best = code;
    }
    return best;
}

/* Build PSL(2,p) (proj = 0) or PGL(2,p) (proj = 1) as a multiplication table. */
static int build_matrix_group(int p, int proj) {
    MP = p; PROJ = proj;
    int P4 = p * p * p * p;
    int *idx = malloc(sizeof(int) * (size_t)P4);
    int *elems = malloc(sizeof(int) * (size_t)P4);
    if (!idx || !elems) return 0;
    for (int x = 0; x < P4; x++) idx[x] = -1;
    int ce = 0;
    int idc = code_of(1, 0, 0, 1);
    idx[idc] = ce; elems[ce++] = idc;
    for (int x = 0; x < P4; x++) {
        if (x == idc) continue;
        int a, b, c, d;
        decode_code(x, &a, &b, &c, &d);
        int det = ((a * d - b * c) % p + p) % p;
        if (proj) { if (det == 0) continue; }
        else if (det != 1) continue;
        if (canon_code(a, b, c, d) != x) continue;
        idx[x] = ce; elems[ce++] = x;
    }
    int Gg = ce;
    if ((size_t)Gg * (size_t)Gg > (size_t)4500000) { free(idx); free(elems); return 0; }
    MT = malloc(sizeof(int) * (size_t)Gg * (size_t)Gg);
    if (!MT) { free(idx); free(elems); return 0; }
    for (int i = 0; i < Gg; i++) {
        int a1, b1, c1, d1;
        decode_code(elems[i], &a1, &b1, &c1, &d1);
        for (int j = 0; j < Gg; j++) {
            int a2, b2, c2, d2;
            decode_code(elems[j], &a2, &b2, &c2, &d2);
            int na = (a1 * a2 + b1 * c2) % p;
            int nb = (a1 * b2 + b1 * d2) % p;
            int nc = (c1 * a2 + d1 * c2) % p;
            int nd = (c1 * b2 + d1 * d2) % p;
            int id = idx[canon_code(na, nb, nc, nd)];
            if (id < 0) { free(idx); free(elems); return 0; }
            MT[(size_t)i * Gg + j] = id;
        }
    }
    G = Gg;
    free(idx);
    free(elems);
    return 1;
}

static inline int gmul(int x, int y) {
    if (GT == 1) return MT[(size_t)x * G + y];
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 10) {
        fprintf(stderr, "usage: prog d D K gtype a b r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    int gtype = atoi(argv[4]);
    int A = atoi(argv[5]);
    int B = atoi(argv[6]);
    int R = atoi(argv[7]);
    uint64_t seed = strtoull(argv[8], NULL, 10);
    double slice = atof(argv[9]);

    if (DEG < 1 || DIAM < 1 || K < 1 || K > 64) { printf("0 0\n"); return 0; }

    if (gtype == 0) {
        MM = A; K2 = B; GT = 0;
        if (MM < 1 || K2 < 1 || K2 > 60) { printf("0 0\n"); return 0; }
        if (gcd_int(R, MM) != 1) { printf("0 0\n"); return 0; }
        POWR[0] = 1 % MM;
        for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * R % MM);
        if (((long long)POWR[K2 - 1] * R) % MM != 1 % MM) { printf("0 0\n"); return 0; }
        G = MM * K2;
    } else {
        GT = 1;
        int p = A;
        int isprime = (p >= 2);
        for (int i = 2; i * i <= p; i++) if (p % i == 0) { isprime = 0; break; }
        if (!isprime || p < 3 || p > 13) { printf("0 0\n"); return 0; }
        if (!build_matrix_group(p, gtype == 2)) { printf("0 0\n"); return 0; }
    }
    if (G < 1 || G > 5000) { printf("0 0\n"); return 0; }

    N = 2 * K * G;
    NE = DEG * K;
    if ((size_t)N > MAXN) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            /* Fresh random lift. */
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) {
                dS[e] = rndint(G);
                set_perm(e);
            }
            T0 = 2.0;
        } else {
            /* Reheat from the best state found so far, with a random kick. */
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions (kept from the parent).
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
# Candidate group-lift configurations.
# ----------------------------------------------------------------------------

MATRIX_PRIMES = [3, 5, 7, 11, 13]


def _candidates(best_n, cap, rng, sd_samples=120):
    """Return (score, key) pairs with best_n < score <= cap, where score = 2*K*|G|.

    key ('mat', K, p, proj) is PSL(2,p) (proj=0) or PGL(2,p) (proj=1).
    key ('sd', K, m, k2, r) is the semidirect product Z_m x|_r Z_k2.
    """
    out = {}
    for p in MATRIX_PRIMES:
        for proj in (0, 1):
            G = p * (p * p - 1) // (1 if proj else 2)
            for K in range(1, 9):
                score = 2 * K * G
                if best_n < score <= cap:
                    key = ('mat', K, p, proj)
                    out[key] = (score, key)
    for _ in range(sd_samples):
        K = rng.randint(1, 8)
        lo = best_n // (2 * K) + 1
        hi = cap // (2 * K)
        if lo > hi:
            continue
        G = rng.randint(lo, hi)
        divs = [k for k in range(1, min(G, 60) + 1) if G % k == 0]
        k2 = rng.choice(divs)
        m = G // k2
        r = 1
        if k2 > 1 and m > 2:
            opts = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1]
            if opts and rng.random() < 0.7:
                r = rng.choice(opts)
        key = ('sd', K, m, k2, r)
        out[key] = (2 * K * G, key)
    return list(out.values())


def _run_candidate(d, D, key, seed, slice_s):
    """Run the C annealer for one configuration. Returns (n, edges); raises on failure."""
    if key[0] == 'mat':
        _, K, p, proj = key
        args = [d, D, K, 2 if proj else 1, p, 0, 1, seed, f"{slice_s:.2f}"]
    else:
        _, K, m, k2, r = key
        args = [d, D, K, 0, m, k2, r, seed, f"{slice_s:.2f}"]
    out = lib.run_c(C_SOURCE, args, timeout=slice_s + 10.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except (ValueError, RuntimeError):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: anneal voltages over a randomly chosen group lift whose
    # order is just above the current best. Configurations are drawn from
    # PSL(2,p), PGL(2,p) and semidirect products, with 1-8 base vertices per
    # side. Each configuration is tried once; the C engine returns as soon as
    # it finds a valid graph, so easy targets cost little time.
    tried = set()
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        cap = int(best[0] * 1.35) + 40
        pool = []
        for _ in range(4):
            pool = [c for c in _candidates(best[0], cap, rng) if c[1] not in tried]
            if pool:
                break
            cap = int(cap * 1.5) + 50
        if not pool:
            break
        score, key = rng.choice(pool)
        tried.add(key)
        slice_s = min(remaining - 1.0, 9.0)
        try:
            n, e = _run_candidate(d, D, key, rng.randrange(1, 10 ** 9), slice_s)
        except (RuntimeError, ValueError):
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
