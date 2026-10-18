import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: bi-Cayley lifts over semidirect products
# Z_m x| Z_k2 with kb base vertices per side, searched entirely in C.
#
# A lift has 2*kb*G vertices, where G = m*k2. Vertex (block, g) is joined to
# (kb + j, g*s) by dart (i, j, s) in each of d layers, where each layer is a
# permutation of the kb A-blocks onto the kb B-blocks. Left multiplication by
# any group element is an automorphism, so the diameter condition only needs
# BFS from the identity of each of the 2*kb blocks. The cost is the total
# number of unreached vertices over those sources, plus a penalty for
# duplicate darts. Cost zero gives a valid graph, which is output at once.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd64() % (u64)n); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, kb, M, K2, R, G, N;
static int *pw, *mt, *lay, *inl, *vol, *vinv, *dist, *queue, *nbuf;

/* Group element a*K2+b means (a,b); product (a,b)(c,e) = (a + R^b c, b + e). */
static int gmul_raw(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int na = (int)(((long long)pw[b] * c + a) % M);
    int nb = (b + e) % K2;
    return na * K2 + nb;
}

static inline int gmul(int x, int y) {
    return mt ? mt[(size_t)x * (size_t)G + (size_t)y] : gmul_raw(x, y);
}

static int ginv_raw(int s) {
    int a = s / K2, b = s % K2;
    int nb = (K2 - b) % K2;
    int t = (int)(((long long)pw[nb] * a) % M);
    int na = (M - t) % M;
    return na * K2 + nb;
}

/* Neighbours of vertex v = blk*G + g, one per layer. */
static void nbrs(int v, int *out) {
    int blk = v / G;
    int g = v - blk * G;
    if (blk < kb) {
        for (int l = 0; l < d_; l++) {
            int j = lay[l * kb + blk];
            out[l] = (kb + j) * G + gmul(g, vol[l * kb + blk]);
        }
    } else {
        int j = blk - kb;
        for (int l = 0; l < d_; l++) {
            int i = inl[l * kb + j];
            out[l] = i * G + gmul(g, vinv[l * kb + i]);
        }
    }
}

static long long dupcount(void) {
    long long c = 0;
    int K = d_ * kb;
    for (int a = 0; a < K; a++) {
        int ia = a % kb;
        for (int b = a + 1; b < K; b++) {
            if (b % kb == ia && lay[a] == lay[b] && vol[a] == vol[b]) c++;
        }
    }
    return c;
}

/* Sum over the 2*kb block identities of the number of unreached vertices. */
static long long evalcost(void) {
    long long total = 0;
    int NB = 2 * kb;
    for (int src = 0; src < NB; src++) {
        for (int v = 0; v < N; v++) dist[v] = -1;
        int s0 = src * G;
        int h = 0, t = 0;
        queue[t++] = s0;
        dist[s0] = 0;
        while (h < t) {
            int v = queue[h++];
            int dv = dist[v];
            if (dv >= D_) continue;
            nbrs(v, nbuf);
            for (int l = 0; l < d_; l++) {
                int u = nbuf[l];
                if (dist[u] < 0) { dist[u] = dv + 1; queue[t++] = u; }
            }
        }
        total += N - t;
    }
    return total;
}

static long long evalfull(void) {
    return evalcost() + (long long)N * dupcount();
}

static void randomize(void) {
    int *p = malloc(sizeof(int) * (size_t)kb);
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < kb; i++) p[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < kb; i++) {
            lay[l * kb + i] = p[i];
            inl[l * kb + p[i]] = i;
        }
    }
    for (int a = 0; a < d_ * kb; a++) {
        vol[a] = rint_(G);
        vinv[a] = ginv_raw(vol[a]);
    }
    free(p);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    kb = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || kb < 1 || kb > 16 || M < 2 || K2 < 1 || R < 0 || R >= M) {
        printf("0 0\n");
        return 0;
    }
    if ((long long)M * K2 > 200000LL) { printf("0 0\n"); return 0; }
    G = M * K2;
    N = 2 * kb * G;
    if (N > 400000) { printf("0 0\n"); return 0; }

    pw = malloc(sizeof(int) * (size_t)K2);
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * R % M);
    if ((long long)pw[K2 - 1] * R % M != 1 % M) { printf("0 0\n"); return 0; }

    int nd = d_ * kb;
    lay = malloc(sizeof(int) * (size_t)nd);
    inl = malloc(sizeof(int) * (size_t)nd);
    vol = malloc(sizeof(int) * (size_t)nd);
    vinv = malloc(sizeof(int) * (size_t)nd);
    dist = malloc(sizeof(int) * (size_t)N);
    queue = malloc(sizeof(int) * (size_t)N);
    nbuf = malloc(sizeof(int) * (size_t)d_);
    if (!pw || !lay || !inl || !vol || !vinv || !dist || !queue || !nbuf) {
        printf("0 0\n");
        return 0;
    }
    mt = NULL;
    if (G <= 2500) {
        mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
        if (mt) {
            for (int x = 0; x < G; x++)
                for (int y = 0; y < G; y++)
                    mt[(size_t)x * G + y] = gmul_raw(x, y);
        }
    }

    randomize();
    long long cur = evalfull();
    double T0 = 0.05 * (double)cur + 2.0, T1 = 0.2;
    double T = T0;
    clock_t start = clock();
    double el = 0.0;
    long long it = 0;

    while (cur > 0) {
        if ((it & 63) == 0) {
            el = (double)(clock() - start) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            T = T0 * pow(T1 / T0, el / limit);
        }
        it++;

        int mv = rint_(100);
        if (mv < 70 || kb < 2) {
            int l = rint_(d_), i = rint_(kb), idx = l * kb + i;
            int nv = rint_(G);
            int ov = vol[idx];
            if (nv == ov) continue;
            int oi = vinv[idx];
            vol[idx] = nv;
            vinv[idx] = ginv_raw(nv);
            long long nc = evalfull();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                vol[idx] = ov;
                vinv[idx] = oi;
            }
        } else {
            int l = rint_(d_), i1 = rint_(kb), i2 = rint_(kb);
            if (i1 == i2) continue;
            int a1 = l * kb + i1, a2 = l * kb + i2;
            int j1 = lay[a1], j2 = lay[a2];
            lay[a1] = j2;
            lay[a2] = j1;
            inl[l * kb + j2] = i1;
            inl[l * kb + j1] = i2;
            long long nc = evalfull();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                lay[a1] = j1;
                lay[a2] = j2;
                inl[l * kb + j1] = i1;
                inl[l * kb + j2] = i2;
            }
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    long long m = (long long)kb * d_ * G;
    printf("%d %lld\n", N, m);
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < kb; i++) {
            int j = lay[l * kb + i];
            int s = vol[l * kb + i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (kb + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
_K2_CHOICES = (1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (G, m, k2, r) for Z_m x| Z_k2 with G = m*k2 >= target, or None."""
    for _ in range(300):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-target // k2) + rng.randrange(0, 3))
        G = m * k2
        if G < target:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [1]
            if k2 % 2 == 0:
                cands.append(m - 1)
            if m > 2:
                cands += [rng.randrange(2, m) for _ in range(40)]
            r = None
            for c in cands:
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return G, m, k2, r
    return None


def _run_lift(d, D, kb, m, k2, r, seed, secs):
    """Run the C lift search for one group; returns (n, edges), possibly (0, [])."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{secs:.2f}", kb, m, k2, r],
                    timeout=secs + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 2: K_{d,d} meets the bipartite Moore bound 2d.
    if D == 2 or d == 1:
        return best

    # D = 3 constructions (the calibration case returns immediately).
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    # Main search: bi-Cayley lifts over semidirect products, searched in C.
    deadline = t0 + max(0.5, time_limit - max(3.0, 0.08 * time_limit))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_kb():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remain = deadline - time.monotonic()
        if remain < 1.0:
            break
        kb = pick_kb()
        base = best[0] // (2 * kb)
        target = base + 1 + rng.randrange(0, base // 60 + 2)
        g = _sample_group(target, rng)
        if g is None:
            continue
        G, m, k2, r = g
        if 2 * kb * G <= best[0]:
            continue
        secs = min(remain - 0.5, rng.uniform(4.0, 9.0))
        if secs < 0.5:
            break
        trials[kb] += 1
        try:
            n, e = _run_lift(d, D, kb, m, k2, r, rng.randrange(1, 1 << 30), secs)
        except Exception:
            continue
        if n >= 2 and n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            wins[kb] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
