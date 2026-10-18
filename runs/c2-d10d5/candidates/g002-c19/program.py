import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (voltage) lift search over Z_m x| Z_k2 with k base blocks
# per side. Each layer is a permutation of the blocks plus one group voltage
# per block, so every vertex has degree d. Validity (diameter <= D) is checked
# with bitmask reachability from the 2k block representatives. Left
# multiplication is an automorphism, so this covers all pairs.
#
# Search: simulated annealing over permutations and voltages, defect-targeted
# voltage moves, a bandit over base sizes k, and an adaptive target order T
# that climbs on success and relaxes on failure.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define MAXN 40000
#define MAXE ((MAXN / 2) * MAXD + 16)
#define PEN 1000LL

static int d_, D_, K_, GO, gm, gk2;
static int gpow[64];
static int sig[MAXD][MAXK], sinv[MAXD][MAXK], sv[MAXD][MAXK], svi[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t RA[MAXN], RB[MAXN], RC[MAXN];
static unsigned char pc16[1 << 16];
static int bu[MAXE], bv[MAXE];
static int bestN = 0, bestM = 0;
static uint64_t rs = 0x2545F4914F6CDD1DULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int pow_ok(int m, int k2, int r) {
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) p = (p * r) % m;
    return p == 1 % m;
}

static void set_group(int m, int k2, int r) {
    gm = m; gk2 = k2; GO = m * k2;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { gpow[b] = (int)p; p = (p * r) % m; }
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int a = x / gk2, b = x - a * gk2;
    int c = y / gk2, e = y - c * gk2;
    long long t = (long long)gpow[b] * c + a;
    int a2 = (int)(t % gm);
    int b2 = b + e; if (b2 >= gk2) b2 -= gk2;
    return a2 * gk2 + b2;
}

/* inverse of (a,b) is (-r^(-b) a, -b) */
static inline int ginv(int x) {
    int a = x / gk2, b = x - a * gk2;
    int nb = (gk2 - b) % gk2;
    long long t = (long long)((gm - a % gm) % gm) * gpow[nb] % gm;
    return (int)t * gk2 + nb;
}

static void build_layer(int l) {
    int k = K_, G = GO;
    for (int i = 0; i < k; i++) {
        int j = sig[l][i], s = sv[l][i];
        for (int g = 0; g < G; g++) nbr[l][i * G + g] = (k + j) * G + gmul(g, s);
    }
    for (int j = 0; j < k; j++) {
        int i = sinv[l][j], si = svi[l][i];
        for (int h = 0; h < G; h++) nbr[l][(k + j) * G + h] = i * G + gmul(h, si);
    }
}

static void eval_reach(uint64_t *out) {
    int k = K_, G = GO, N = 2 * k * G, d = d_;
    uint64_t *src = out, *dst = RC;
    memset(out, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) out[b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = src[v];
            for (int l = 0; l < d; l++) x |= src[nbr[l][v]];
            dst[v] = x;
            if (x != src[v]) changed = 1;
        }
        uint64_t *tmp = src; src = dst; dst = tmp;
        if (!changed) break;
    }
    if (src != out) memcpy(out, src, sizeof(uint64_t) * (size_t)N);
}

static long long total_cost(const uint64_t *R) {
    int k = K_, G = GO, N = 2 * k * G;
    long long c = 0;
    for (int v = 0; v < N; v++) c += 2 * k - pc16[R[v] & 0xFFFF];
    return c;
}

static long long dup_count(void) {
    long long c = 0;
    for (int i = 0; i < K_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (sig[l1][i] == sig[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static void random_state(void) {
    int k = K_, G = GO;
    for (int l = 0; l < d_; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            sig[l][i] = perm[i];
            sinv[l][perm[i]] = i;
            sv[l][i] = rndi(G);
            svi[l][i] = ginv(sv[l][i]);
        }
        build_layer(l);
    }
}

static int pick_defect(const uint64_t *R, int *vout) {
    int k = K_, G = GO, N = 2 * k * G;
    uint64_t full = (1ULL << (2 * k)) - 1;
    int start = rndi(N);
    for (int t = 0; t < N; t++) {
        int v = (start + t) % N;
        if (R[v] != full) { *vout = v; return 1; }
    }
    return 0;
}

static int run_sa(long iters, long patience, clock_t deadline) {
    int k = K_, G = GO, d = d_;
    uint64_t *cur = RA, *nxt = RB;
    random_state();
    eval_reach(cur);
    long long cost = total_cost(cur) + PEN * dup_count();
    long long best = cost;
    long last_imp = 0;
    double c0 = (double)(cost > 0 ? cost : 1);
    for (long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if ((t & 63) == 0 && clock() > deadline) break;
        if (t - last_imp > patience) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / (double)iters) + 0.3;
        double x = rndu();
        int mode, l = rndi(d), i1 = 0, i2 = 0, i = 0;
        int o1 = 0, o2 = 0, os = 0, oi = 0;
        if (k >= 2 && x < 0.2) {
            mode = 0;
            i1 = rndi(k);
            do { i2 = rndi(k); } while (i2 == i1);
            o1 = sig[l][i1]; o2 = sig[l][i2];
            sig[l][i1] = o2; sig[l][i2] = o1;
            sinv[l][o2] = i1; sinv[l][o1] = i2;
        } else {
            mode = 1;
            i = -1;
            if (rndu() < 0.4) {
                int v;
                if (pick_defect(cur, &v)) {
                    int bl = v / G;
                    if (bl < k) i = bl;
                    else i = sinv[l][bl - k];
                }
            }
            if (i < 0) i = rndi(k);
            os = sv[l][i]; oi = svi[l][i];
            int nv = rndi(G);
            if (nv == os) continue;
            sv[l][i] = nv; svi[l][i] = ginv(nv);
        }
        build_layer(l);
        eval_reach(nxt);
        long long c2 = total_cost(nxt) + PEN * dup_count();
        int accept = (c2 <= cost) || (rndu() < exp(-(double)(c2 - cost) / temp));
        if (accept) {
            uint64_t *tmp = cur; cur = nxt; nxt = tmp;
            cost = c2;
            if (cost < best) { best = cost; last_imp = t; }
        } else {
            if (mode == 0) {
                sig[l][i1] = o1; sig[l][i2] = o2;
                sinv[l][o1] = i1; sinv[l][o2] = i2;
            } else {
                sv[l][i] = os; svi[l][i] = oi;
            }
            build_layer(l);
        }
    }
    return cost == 0;
}

static void record_best(void) {
    int k = K_, G = GO, d = d_;
    int m = 0;
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++) {
            bu[m] = u; bv[m] = nbr[l][u]; m++;
        }
    bestN = 2 * k * G;
    bestM = m;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double T0 = (argc >= 6) ? atof(argv[5]) : 0.0;
    if (d_ < 1 || d_ > MAXD) { printf("1 0\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    for (int x = 0; x < 65536; x++) {
        int c = 0, y = x;
        while (y) { c += y & 1; y >>= 1; }
        pc16[x] = (unsigned char)c;
    }

    /* Baseline K_{d,d}: valid for D >= 2. */
    bestN = 2 * d_;
    bestM = d_ * d_;
    for (int a = 0; a < d_; a++)
        for (int b = 0; b < d_; b++) {
            bu[a * d_ + b] = a;
            bv[a * d_ + b] = d_ + b;
        }
    if (D_ < 2) {
        printf("%d %d\n", bestN, bestM);
        for (int e = 0; e < bestM; e++) printf("%d %d\n", bu[e], bv[e]);
        return 0;
    }

    clock_t start = clock();
    clock_t deadline = start + (clock_t)(budget * CLOCKS_PER_SEC);

    double moore = 0.0;
    {
        double p = 1.0;
        for (int i = 0; i < D_; i++) { moore += p; p *= (double)(d_ - 1); }
        moore *= 2.0;
    }
    double T = (T0 > 0.0) ? T0 : 0.3 * moore;
    if (T > 36000.0) T = 36000.0;
    if (T < bestN + 2) T = bestN + 2;

    static const int KS[] = {1, 2, 3, 4, 5, 6, 8};
    const int NKS = 7;
    static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24};
    const int NK2 = 14;
    double trials[7] = {0}, wins[7] = {0};

    while (clock() < deadline) {
        int ki = 0;
        if (rndu() < 0.2) {
            ki = rndi(NKS);
        } else {
            double bs = -1.0;
            for (int q = 0; q < NKS; q++) {
                double sc = (wins[q] + 1.0) / (trials[q] + 2.0) + 0.02 * rndu();
                if (sc > bs) { bs = sc; ki = q; }
            }
        }
        int k = KS[ki];
        int tgtG = (int)ceil(T / (2.0 * k)) + rndi(2);
        int k2 = K2S[rndi(NK2)];
        int m = (tgtG + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1 && m > 2) {
            for (int tries = 0; tries < 300; tries++) {
                int c = 2 + rndi(m - 2);
                if (gcd_i(c, m) == 1 && pow_ok(m, k2, c)) { r = c; break; }
            }
        }
        set_group(m, k2, r);
        if (2 * k * GO > MAXN) continue;
        K_ = k;
        trials[ki] += 1.0;
        int ok = run_sa(5000, 1000, deadline);
        if (ok) {
            wins[ki] += 1.0;
            int n = 2 * k * GO;
            if (n > bestN) record_best();
            double nd = (double)n;
            T = ((T > nd) ? T : nd) * 1.01 + 1.0;
            if (T > 36000.0) T = 36000.0;
        } else {
            T *= 0.995;
            if (T < bestN + 2) T = bestN + 2;
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
"""

_MAX_C_D = 16


# ----------------------------------------------------------------------------
# Exact constructions (safe baselines).
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
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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
                return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D == 2:
        return best

    # Bold change: move the voltage-lift search fully into C, with an adaptive
    # target order and no Python-side search loop.
    if 3 <= d <= _MAX_C_D and D >= 3:
        elapsed = time.monotonic() - t0
        budget = min(0.75 * time_limit, time_limit - 14.0) - elapsed
        if budget >= 3.0:
            moore = lib.moore_bound(d, D)
            t_guess = max(best_n + 2, int(0.3 * moore))
            args = [d, D, seed, f"{budget:.2f}", t_guess]
            try:
                out = lib.run_c(C_SOURCE, args, timeout=budget + 6.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


def _gq_placeholder():
    """Unused; kept to avoid accidental edits to the layout above."""
    return None
