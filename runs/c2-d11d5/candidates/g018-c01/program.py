"""Combined program: exact small constructions first, then a C voltage-lift annealer over
semidirect products Z_m x| Z_k2 with 1-6 base vertices per side. The C search replaces the
Python annealer and the grow-by-two engine. Every returned graph is checked with lib.is_valid,
and K_{d,d} (or an exact construction) is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley voltage-lift annealer over semidirect products Z_m x| Z_k2.
 * Usage:  prog d D seed time_limit        (stdin ignored)
 * stdout: "n m" + edges of the largest valid lift found, or "0 0".
 *
 * Vertices: block b in 0..2K-1 holds vertices b*G + g, g in 0..G-1 (group element code a*K2+b).
 * A-block i, layer l: A_{i,g} ~ B_{j,g*s}, where j = perm[l][i], s = volt[l][i].
 * Left translations by group elements are automorphisms, so the graph has diameter <= D
 * exactly when every block identity (b*G) is within distance D of every vertex.
 * Cost = (unreached block-identity/vertex pairs) + PEN * (duplicate darts).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 24000
#define MAXD 24
#define MAXBK 6
#define BEST_CAP (MAXN * MAXD / 2 + 16)
#define PEN 300L
#define ITERS 4000L
#define PATIENCE 1200L

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2LL * D;
    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
    }
    return 2 * s;
}

static long mod_pow(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long gcd_l(long a, long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long mod_inv(long a, long m) {
    long t = 0, nt = 1, r = m, nr = ((a % m) + m) % m;
    while (nr) {
        long q = r / nr, tmp;
        tmp = t - q * nt;
        t = nt;
        nt = tmp;
        tmp = r - q * nr;
        r = nr;
        nr = tmp;
    }
    if (t < 0) t += m;
    return t;
}

static int is_prime(int x) {
    if (x < 2) return 0;
    for (long p = 2; p * p <= x; p++)
        if (x % p == 0) return 0;
    return 1;
}

/* ---------------- group Z_GM x| Z_GK, element code a*GK + b ---------------- */
static int BK, GM, GK, G, N;
static int rpw[64], rinvpw[64];

static void set_group(int m, int k2, int r) {
    GM = m;
    GK = k2;
    G = m * k2;
    long ri = mod_inv(r, m);
    rpw[0] = 1 % m;
    rinvpw[0] = 1 % m;
    for (int b = 1; b < k2; b++) {
        rpw[b] = (int)((long)rpw[b - 1] * r % m);
        rinvpw[b] = (int)((long)rinvpw[b - 1] * ri % m);
    }
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    long t = (long)rpw[b] * c % GM;
    int aa = (int)((a + t) % GM);
    int bb = b + e;
    if (bb >= GK) bb -= GK;
    return aa * GK + bb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    long t = (long)rinvpw[b] * a % GM;
    int c = (int)((GM - t) % GM);
    int nb = (GK - b) % GK;
    return c * GK + nb;
}

static void setup_group(int target) {
    static const int ks[18] = {1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 8, 9, 10, 12, 16};
    int k2 = ks[rndint(18)];
    int m = (target + k2 - 1) / k2;
    if (rndint(3) == 0) m += rndint(4);
    if (m < 3) m = 3;
    if (k2 == 1) {
        set_group(m, 1, 1);
        return;
    }
    if (rndint(10) < 6) {
        /* prime modulus with an element of order dividing k2: many non-abelian actions */
        for (int mm = m, t = 0; t < 400; t++, mm++) {
            if (!is_prime(mm) || (mm - 1) % k2 != 0) continue;
            for (int tr = 0; tr < 50; tr++) {
                long x = 2 + rndint(mm - 2);
                long y = mod_pow(x, (mm - 1) / k2, mm);
                if (y != 1) {
                    set_group(mm, k2, (int)y);
                    return;
                }
            }
        }
    }
    for (int tr = 0; tr < 200; tr++) {
        int c = 1 + rndint(m - 1);
        if (gcd_l(c, m) == 1 && mod_pow(c, k2, m) == 1 % m) {
            set_group(m, k2, c);
            return;
        }
    }
    set_group(m, k2, 1); /* abelian fallback, always valid */
}

/* ---------------- lift state ---------------- */
static int perm[MAXD][MAXBK], iperm[MAXD][MAXBK];
static int volt[MAXD][MAXBK], vinv[MAXD][MAXBK];
static int nbr[MAXD][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN];

static void rebuild_layer(int l) {
    for (int i = 0; i < BK; i++) {
        int j = perm[l][i], s = volt[l][i];
        int ba = i * G, bb = (BK + j) * G;
        for (int g = 0; g < G; g++) nbr[l][ba + g] = bb + gmul(g, s);
    }
    for (int j = 0; j < BK; j++) {
        int i = iperm[l][j], si = vinv[l][i];
        int bb = (BK + j) * G, ba = i * G;
        for (int h = 0; h < G; h++) nbr[l][bb + h] = ba + gmul(h, si);
    }
}

static long unreached_cost(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * BK; b++) cur[b * G] |= 1ULL << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long unr = 0;
    int full = 2 * BK;
    for (int v = 0; v < N; v++) unr += full - __builtin_popcountll(cur[v]);
    return unr;
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < BK; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && volt[l1][i] == volt[l2][i]) c++;
    return c;
}

static long full_cost(void) { return unreached_cost() + PEN * dupcount(); }

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < BK; i++) perm[l][i] = i;
        for (int i = BK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < BK; i++) iperm[l][perm[l][i]] = i;
        for (int i = 0; i < BK; i++) {
            volt[l][i] = rndint(G);
            vinv[l][i] = ginv(volt[l][i]);
        }
        rebuild_layer(l);
    }
}

static void swap_perm(int l, int i1, int i2) {
    int t = perm[l][i1];
    perm[l][i1] = perm[l][i2];
    perm[l][i2] = t;
    iperm[l][perm[l][i1]] = i1;
    iperm[l][perm[l][i2]] = i2;
}

/* Simulated annealing on one (BK, group) configuration. Returns final cost (0 = valid). */
static long anneal(long iters, long patience) {
    random_state();
    long cost = full_cost();
    double c0 = cost > 0 ? (double)cost : 1.0;
    double T0 = 0.02 * c0 + 1.0;
    long best_c = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > t_end) break;
        if (t - last > patience) break;
        double T = T0 * (1.0 - (double)t / (double)iters) + 0.2;
        if (BK == 1 || rndint(100) < 75) {
            int l = rndint(d), i = rndint(BK);
            int old = volt[l][i], oldinv = vinv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            volt[l][i] = nw;
            vinv[l][i] = ginv(nw);
            rebuild_layer(l);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                volt[l][i] = old;
                vinv[l][i] = oldinv;
                rebuild_layer(l);
            }
        } else {
            int l = rndint(d), i1 = rndint(BK), i2 = rndint(BK - 1);
            if (i2 >= i1) i2++;
            swap_perm(l, i1, i2);
            rebuild_layer(l);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                swap_perm(l, i1, i2);
                rebuild_layer(l);
            }
        }
        if (cost < best_c) {
            best_c = cost;
            last = t;
        }
    }
    return cost;
}

/* ---------------- best graph ---------------- */
static int best_N = 0, best_M = 0;
static int bu[BEST_CAP], bv[BEST_CAP];

static void record(void) {
    best_N = N;
    best_M = 0;
    for (int v = 0; v < BK * G; v++)
        for (int l = 0; l < d; l++) {
            if (best_M >= BEST_CAP) return;
            bu[best_M] = v;
            bv[best_M] = nbr[l][v];
            best_M++;
        }
}

static int trials[MAXBK + 1], wins[MAXBK + 1];

static int pick_bk(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXBK);
    int bestb = 1;
    double bs = -1.0;
    for (int b = 1; b <= MAXBK; b++) {
        double s = (wins[b] + 1.0) / (trials[b] + 2.0) + 0.02 * rnd01();
        if (s > bs) {
            bs = s;
            bestb = b;
        }
    }
    return bestb;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long long mb = moore_bound();
    double bump = 0.03;
    while (now() < t_end) {
        int b = pick_bk();
        BK = b;
        double base = best_N > 0 ? (double)best_N / (2.0 * BK) : 2.0;
        int target = (int)(base * (1.0 + bump)) + 1 + rndint(2);
        setup_group(target);
        N = 2 * BK * G;
        if (N > MAXN || (long long)N > mb) {
            bump *= 0.5;
            continue;
        }
        if (N <= best_N) continue;
        trials[b]++;
        long c = anneal(ITERS, PATIENCE);
        if (c == 0) {
            wins[b]++;
            record();
            bump = 0.03;
        } else {
            bump = bump * 0.97 - 0.0005;
            if (bump < 0) bump = 0;
        }
    }

    if (best_N == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_N, best_M);
    for (int i = 0; i < best_M; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# build
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

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C voltage-lift annealer over semidirect products.
    if d < 3:
        return best
    budget = max(1.0, 0.85 * time_limit - 1.5) - (time.monotonic() - t0)
    if budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 8)
            n_out, e_out = lib.parse_graph_text(text)
            consider(n_out, e_out)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
