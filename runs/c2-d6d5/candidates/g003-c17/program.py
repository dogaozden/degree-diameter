import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXK 16
#define MAXG 1000
#define MAXT 128
#define MAXN (2 * MAXK * MAXG)

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bi-Cayley lifts over a finite group G given by its multiplication table.
   Base: k "A" blocks and k "B" blocks; vertices A_{i,g} = i*G+g, B_{j,g} = (k+j)*G+g.
   Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. Left multiplication is an automorphism,
   so the diameter is checked from the 2k block identities only. */
static int d_, D_, K_, G_, N_;
static int nG_ = 0;
static int gord[MAXT];
static int *gtab[MAXT];
static int *MT;
static int RS[MAXG * MAXG];
static int nb[MAXD * MAXN];
static u64 bufA[MAXN], bufB[MAXN];
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

static int valid_group(const int *tab, int G) {
    static int mk[MAXG];
    for (int y = 0; y < G; y++)
        if (tab[y] != y || tab[y * G] != y) return 0;
    for (int s = 0; s < G; s++) {
        for (int y = 0; y < G; y++) mk[y] = 0;
        for (int x = 0; x < G; x++) {
            int y = tab[x * G + s];
            if (y < 0 || y >= G || mk[y]) return 0;
            mk[y] = 1;
        }
    }
    return 1;
}

static void prep_group(int g) {
    int G = gord[g];
    G_ = G;
    MT = gtab[g];
    for (int x = 0; x < G; x++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[x * G + s]] = x;
}

static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
    u64 *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nb[l * N + v]];
            nxt[v] = x;
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(cur[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    return unreached + 1000 * dup;
}

static int search(double tend, int iters, int patience) {
    int k = K_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            setdart(l, i, lay[l][i], VS[l][i]);
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > tend) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;
        if (k >= 2 && rndu() < 0.25) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            setdart(l, i1, t2, VS[l][i1]);
            setdart(l, i2, t1, VS[l][i2]);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                setdart(l, i1, t1, VS[l][i1]);
                setdart(l, i2, t2, VS[l][i2]);
            }
        } else {
            int l = rndi(d), i = rndi(k);
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            setdart(l, i, lay[l][i], nw);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                VS[l][i] = old;
                setdart(l, i, lay[l][i], old);
            }
        }
    }
    return cost == 0;
}

static void store_best(void) {
    int N = N_, k = K_, G = G_, d = d_;
    int kG = k * G;
    int cnt = kG * d;
    int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
    int p = 0;
    for (int u = 0; u < kG; u++)
        for (int l = 0; l < d; l++) {
            ne[2 * p] = u;
            ne[2 * p + 1] = nb[l * N + u];
            p++;
        }
    free(bE);
    bE = ne;
    bEc = cnt;
    bestN = N;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int thr = atoi(argv[5]);
    int floorN = atoi(argv[6]);
    if (d_ < 3 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }
    if (thr < 2) thr = 2;
    if (floorN < 2) floorN = 2;
    if (floorN > thr) floorN = thr;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Input: "n m" then m lines of two ints. The Python side packs the group library
       as a flat integer stream: T, then for each group G and its G*G table entries. */
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) m0 = 0;
    if (m0 < 0) m0 = 0;
    int *buf = malloc(sizeof(int) * (size_t)(2 * m0 + 2));
    int total = 0;
    for (int i = 0; i < 2 * m0; i++) {
        if (scanf("%d", &buf[i]) != 1) break;
        total++;
    }
    int pos = 0;
    int T = total > 0 ? buf[pos++] : 0;
    for (int t = 0; t < T && nG_ < MAXT; t++) {
        if (pos >= total) break;
        int G = buf[pos++];
        if (G < 2 || G > MAXG || pos + G * G > total) break;
        int *tab = malloc(sizeof(int) * (size_t)G * G);
        memcpy(tab, buf + pos, sizeof(int) * (size_t)G * G);
        pos += G * G;
        if (valid_group(tab, G)) {
            gord[nG_] = G;
            gtab[nG_] = tab;
            nG_++;
        } else {
            free(tab);
        }
    }
    free(buf);
    if (nG_ == 0) { printf("0 0\n"); return 0; }

    double tend = now() + tl;
    int fails = 0;
    int ks[MAXK];
    while (now() < tend) {
        int g = rndi(nG_);
        int G = gord[g];
        int nk = 0;
        for (int k = 1; k <= MAXK && nk < 3; k++) {
            long long N = 2LL * k * G;
            if (N >= thr && N <= MAXN) ks[nk++] = k;
        }
        if (nk > 0) {
            int k = ks[rndi(nk)];
            prep_group(g);
            K_ = k;
            N_ = 2 * k * G;
            if (search(tend, 30000, 5000)) {
                if (N_ > bestN) store_best();
                thr = bestN + 1;
                fails = 0;
                continue;
            }
        }
        fails++;
        if (fails >= 4 && bestN == 0) {
            int nt = thr - thr / 50 - 1;
            if (nt < floorN) nt = floorN;
            thr = nt;
            fails = 0;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


# ---- group multiplication factories (identity is always element 0) ----

def _make_cyclic(m):
    def mul(x, y):
        return (x + y) % m
    return mul


def _make_heis(p):
    """Heisenberg group over Z_p: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    pp = p * p

    def mul(x, y):
        a, r = divmod(x, pp)
        b, c = divmod(r, p)
        a2, r2 = divmod(y, pp)
        b2, c2 = divmod(r2, p)
        return ((a + a2) % p) * pp + ((b + b2) % p) * p + (c + c2 + a * b2) % p
    return mul


def _make_diag(p, k, r1, r2):
    """Z_p^2 semidirect Z_k acting by diag(r1, r2), where r1^k = r2^k = 1 mod p."""
    def dec(e):
        b = e % k
        t = e // k
        return t // p, t % p, b

    def mul(e1, e2):
        x, y, b = dec(e1)
        x2, y2, c = dec(e2)
        X = (x + pow(r1, b, p) * x2) % p
        Y = (y + pow(r2, b, p) * y2) % p
        return (X * p + Y) * k + (b + c) % k
    return mul


def _make_semi(m, k, r):
    return lib.semidirect_group(m, k, r)[1]


def _table(order, mul):
    return [mul(x, y) for x in range(order) for y in range(order)]


def _group_library(thr, rng, gmax=420):
    """Random selection of groups whose orders can host a lift with about thr vertices.

    Returns a list of (order, mul-table) pairs. Groups of order >= thr/2 are preferred,
    because a single block (k = 1) then already reaches the target size.
    """
    gmin = max(2, thr // 16)
    if gmax < gmin:
        return []

    def ok(order):
        return gmin <= order <= gmax

    cands = []  # (order, factory, args)
    for p in _primes_upto(7):
        if ok(p ** 3):
            cands.append((p ** 3, _make_heis, (p,)))
    for p in _primes_upto(23):
        if p * p > gmax:
            break
        for k in range(2, p):
            if (p - 1) % k:
                continue
            order = p * p * k
            if not ok(order):
                continue
            roots = [r for r in range(1, p) if pow(r, k, p) == 1]
            for _ in range(2):
                cands.append((order, _make_diag, (p, k, rng.choice(roots), rng.choice(roots))))
    for k in range(2, 13):
        for m in range(max(2, gmin // k), gmax // k + 1):
            order = m * k
            if not ok(order):
                continue
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not rs:
                continue
            for r in rng.sample(rs, min(2, len(rs))):
                cands.append((order, _make_semi, (m, k, r)))
    for m in range(max(2, gmin), gmax + 1):
        cands.append((m, _make_cyclic, (m,)))

    rng.shuffle(cands)
    pool_a = [c for c in cands if 2 * c[0] >= thr]
    pool_b = [c for c in cands if 2 * c[0] < thr]
    chosen = []
    for pool, cap in ((pool_a, 800_000), (pool_b, 200_000)):
        used = 0
        for order, factory, args in pool:
            if len(chosen) >= 30:
                break
            if used + order * order > cap:
                continue
            used += order * order
            chosen.append((order, _table(order, factory(*args))))
    return chosen


def _encode(groups):
    """Pack the group library as pairs so it can travel through lib.run_c as a graph."""
    flat = [len(groups)]
    for order, tab in groups:
        flat.append(order)
        flat.extend(tab)
    if len(flat) % 2:
        flat.append(0)
    return [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    # Start the search near 40% of the Moore bound (record for d=6, D=5 is about 44%).
    thr = max(best_n + 1, int(0.40 * lib.moore_bound(d, D)))
    rng = random.Random(seed * 7919 + d * 131 + D)
    while True:
        groups = _group_library(thr, rng)
        if groups or thr <= best_n + 1:
            break
        thr = max(best_n + 1, thr // 2)
    if not groups:
        return best

    left = time_limit - 12.0 - (time.monotonic() - start)
    if left < 2.0:
        return best

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(left, 2), thr, best_n + 1],
                        stdin_graph=(1, _encode(groups)), timeout=left + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
