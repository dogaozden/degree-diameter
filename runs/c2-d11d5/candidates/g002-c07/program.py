"""Bold variant: a C engine searches bi-Cayley (bi-lift) graphs over semidirect products
Z_m x| Z_k2 and the non-abelian affine group AGL(1,p). Layers are permutations, so every
vertex has degree exactly d. Diameter is checked from one representative per block, which is
valid because the group acts by left multiplication. The C search runs for most of the time
budget and ratchets the order upward. Exact constructions (projective planes, W(q) for D=4)
and the K_{d,d} fallback remain, and every returned graph passes lib.is_valid."""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 6
#define MAXG 10000
#define MAXN (2 * MAXK * MAXG)
#define MAXE (MAXK * MAXG * MAXD)
#define PEN 1000

typedef struct {
    int type;            /* 0: Z_m x| Z_k2, 1: AGL(1,p) */
    int m, k2, r, p, G;
    int pw[64];          /* type 0: r^b mod m */
    int ainv[512];       /* type 1: inverse mod p */
} Grp;

static Grp grp;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int gmul(int x, int y) {
    if (grp.type == 0) {
        int k2 = grp.k2, m = grp.m;
        int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
        return ((a + (int)((long)grp.pw[b] * c % m)) % m) * k2 + (b + e) % k2;
    } else {
        int p = grp.p;
        int a = x / p + 1, b = x % p, c = y / p + 1, e = y % p;
        int ac = (a * c) % p;
        int ae = (a * e + b) % p;
        return (ac - 1) * p + ae;
    }
}

static int ginv(int x) {
    if (grp.type == 0) {
        int k2 = grp.k2, m = grp.m;
        int a = x / k2, b = x % k2;
        int nb = (k2 - b) % k2;
        int na = (int)((m - ((long)grp.pw[nb] * a) % m) % m);
        return na * k2 + nb;
    } else {
        int p = grp.p;
        int a = x / p + 1, b = x % p;
        int ia = grp.ainv[a];
        int e = (int)(((long)(p - b) % p) * ia % p);
        return (ia - 1) * p + e;
    }
}

static long powmod(long a, long e, long m) {
    long r = 1 % m;
    a %= m;
    while (e > 0) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void setup_semidirect(int m, int k2, int r) {
    grp.type = 0; grp.m = m; grp.k2 = k2; grp.r = r; grp.G = m * k2;
    long v = 1 % m;
    for (int b = 0; b < k2; b++) { grp.pw[b] = (int)v; v = v * r % m; }
}

static void setup_affine(int p) {
    grp.type = 1; grp.p = p; grp.G = p * (p - 1);
    for (int a = 1; a < p; a++) grp.ainv[a] = (int)powmod(a, p - 2, p);
}

/* Search state: K base vertices per side, G group order, N = 2KG vertices. */
static int dd, DD, K, G, N;
static int lay[MAXD][MAXK], layinv[MAXD][MAXK];
static int S[MAXD][MAXK], Si[MAXD][MAXK];
static int F[MAXD][MAXK][MAXG], Fi[MAXD][MAXK][MAXG];
static uint16_t bufA[MAXN], bufB[MAXN], accR[MAXN];
static uint16_t *cur, *nxt;
static int pc[1 << 12];
static int primes[100], np_;
static int ebu[MAXE], ebv[MAXE];
static int best_n = 0, best_m = 0;

static void set_volt(int l, int i, int s) {
    S[l][i] = s;
    Si[l][i] = ginv(s);
    int sv = S[l][i], si = Si[l][i];
    for (int g = 0; g < G; g++) {
        F[l][i][g] = gmul(g, sv);
        Fi[l][i][g] = gmul(g, si);
    }
}

static void random_state(void) {
    for (int l = 0; l < dd; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) { lay[l][i] = perm[i]; layinv[l][perm[i]] = i; }
        for (int i = 0; i < K; i++) set_volt(l, i, rndint(G));
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < dd; l1++)
            for (int l2 = l1 + 1; l2 < dd; l2++)
                if (lay[l1][i] == lay[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

/* Bitmask per vertex: bit b set iff representative of block b is within DD of the vertex. */
static void compute_reach(void) {
    memset(cur, 0, sizeof(uint16_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[b * G] = (uint16_t)(1u << b);
    for (int t = 0; t < DD; t++) {
        int changed = 0;
        for (int i = 0; i < K; i++) {
            for (int g = 0; g < G; g++) {
                int v = i * G + g;
                uint16_t acc = cur[v];
                for (int l = 0; l < dd; l++) {
                    int j = lay[l][i];
                    acc |= cur[(K + j) * G + F[l][i][g]];
                }
                nxt[v] = acc;
                changed |= (acc != cur[v]);
            }
        }
        for (int j = 0; j < K; j++) {
            for (int h = 0; h < G; h++) {
                int v = (K + j) * G + h;
                uint16_t acc = cur[v];
                for (int l = 0; l < dd; l++) {
                    int i = layinv[l][j];
                    acc |= cur[i * G + Fi[l][i][h]];
                }
                nxt[v] = acc;
                changed |= (acc != cur[v]);
            }
        }
        uint16_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
}

static long total_cost(void) {
    compute_reach();
    long sum = 0;
    for (int v = 0; v < N; v++) sum += pc[cur[v]];
    long unreached = (long)2 * K * N - sum;
    return unreached + (long)PEN * dupcount();
}

static int run_sa(long maxit, long patience, double tend) {
    uint16_t full = (uint16_t)((1u << (2 * K)) - 1);
    random_state();
    long cost = total_cost();
    memcpy(accR, cur, sizeof(uint16_t) * (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long bestc = cost, last = 0;
    for (long t = 0; t < maxit && cost > 0; t++) {
        if ((t & 31) == 0 && now() > tend) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)maxit);
        if (temp < 0.5) temp = 0.5;
        long c2;
        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(dd);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int j1 = lay[l][i1], j2 = lay[l][i2];
            lay[l][i1] = j2; lay[l][i2] = j1;
            layinv[l][j2] = i1; layinv[l][j1] = i2;
            c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(accR, cur, sizeof(uint16_t) * (size_t)N);
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                lay[l][i1] = j1; lay[l][i2] = j2;
                layinv[l][j1] = i1; layinv[l][j2] = i2;
            }
            continue;
        }
        int bad = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 64; tr++) {
                int v = rndint(N);
                if (accR[v] != full) { bad = v; break; }
            }
        }
        int l = rndint(dd);
        int i;
        if (bad >= 0) {
            int blk = bad / G;
            if (blk < K) i = blk;
            else i = layinv[l][blk - K];
        } else {
            i = rndint(K);
        }
        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        set_volt(l, i, nw);
        c2 = total_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(accR, cur, sizeof(uint16_t) * (size_t)N);
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            set_volt(l, i, old);
        }
    }
    return cost == 0;
}

static void store_solution(void) {
    int idx = 0;
    for (int i = 0; i < K; i++)
        for (int g = 0; g < G; g++)
            for (int l = 0; l < dd; l++) {
                int j = lay[l][i];
                ebu[idx] = i * G + g;
                ebv[idx] = (K + j) * G + F[l][i][g];
                idx++;
            }
    best_n = N;
    best_m = idx;
}

static const int K2S[18] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 24, 30};

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]) / 1000.0;
    int min_n = atoi(argv[5]);
    rs = 88172645463325252ULL ^ (seed * 0x9E3779B97F4A7C15ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    if (dd < 3 || dd > MAXD || DD < 3) { printf("0 0\n"); return 0; }
    for (int i = 0; i < (1 << 12); i++) pc[i] = pc[i >> 1] + (i & 1);
    cur = bufA; nxt = bufB;
    np_ = 0;
    for (int p = 3; p < 500; p++) {
        int ip = 1;
        for (int q = 2; q * q <= p; q++) if (p % q == 0) { ip = 0; break; }
        if (ip) primes[np_++] = p;
    }
    double t0 = now(), tend = t0 + budget;
    while (now() < tend) {
        int thr = best_n > min_n ? best_n : min_n;
        K = 1 + rndint(MAXK);
        int lo = thr / (2 * K) + 1;
        int hi = lo + lo / 8 + 3;
        if (hi > MAXG) hi = MAXG;
        if (lo > hi) continue;
        int ok = 0;
        if (rnd01() < 0.4) {
            int cand[100], nc = 0;
            for (int t = 0; t < np_; t++) {
                long g2 = (long)primes[t] * (primes[t] - 1);
                if (g2 >= lo && g2 <= hi) cand[nc++] = primes[t];
            }
            if (nc > 0) { setup_affine(cand[rndint(nc)]); ok = 1; }
        }
        if (!ok) {
            int gt = lo + rndint(hi - lo + 1);
            int k2 = K2S[rndint(18)];
            int m = (gt + k2 - 1) / k2;
            if (m < 2) m = 2;
            if (m * k2 > MAXG) continue;
            int r = 1;
            if (k2 > 1 && m > 2) {
                for (int tr = 0; tr < 200; tr++) {
                    int c = 2 + rndint(m - 2);
                    if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            }
            setup_semidirect(m, k2, r);
        }
        G = grp.G;
        N = 2 * K * G;
        if (G > MAXG || N <= thr || N > MAXN) continue;
        int res = run_sa(30000, 5000, tend);
        if (res) store_solution();
    }
    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", ebu[e], ebv[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions.
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold search: C engine over bi-Cayley lifts (semidirect and affine groups).
    budget = min(0.8 * time_limit, time_limit - 10.0)
    if budget >= 3.0:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, int(seed) % 1000000007 + 1, int(budget * 1000), best_n],
                stdin_graph=None,
                timeout=min(budget + 8.0, time_limit - 3.0),
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
