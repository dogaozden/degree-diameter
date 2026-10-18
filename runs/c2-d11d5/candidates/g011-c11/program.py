"""Bold change for the weak target (d >= 5, D >= 5): a new C engine replaces the Python lift search.

Construction: bi-Cayley lifts over semidirect products Z_m x| Z_k2, with a base of K blocks per side
and d layers, each layer a perfect matching between the A and B blocks with a group voltage. The C
engine enumerates every admissible r for each (m, k2) pair, anneals voltages and partner matchings
using a bit-parallel reach test over block representatives (by group transitivity, the diameter is
at most D iff every representative reaches every vertex within D), and ratchets the target order up
after each success.

Safety: K_{d,d} is the fallback, the exact PG/Araujo-Lopez/generalized-quadrangle constructions are
used where they apply, and every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley lift search over semidirect groups Z_m x| Z_k2.
 * Usage: prog d D seed time_limit start_n
 * Output: "n m" + edges of the best valid graph with n > start_n, or "0 0".
 */

typedef uint64_t u64;

#define MAXK 6
#define MAXDEG 32
#define NCAP 90000
#define PEN 1000L
#define PATIENCE 2500

typedef struct {
    int m, k2, G;
    int rp[64];
} Group;

static const int K2LIST[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
#define NK2 ((int)(sizeof(K2LIST) / sizeof(K2LIST[0])))

static int d, D;
static u64 rs = 88172645463325252ULL;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(int dd, int DD) {
    if (DD <= 0 || dd <= 0) return 1;
    if (dd == 1) return 2;
    if (dd == 2) return 2L * DD;
    long s = 0, p = 1;
    for (int i = 0; i < DD; i++) {
        s += p;
        p *= (dd - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Element (a, b) is coded a*k2 + b; (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(const Group *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2;
    int c = y / g->k2, e = y % g->k2;
    long t = ((long)g->rp[b] * c + a) % g->m;
    return (int)(t * g->k2 + (b + e) % g->k2);
}

/* Inverse of (a, b) is (-r^(-b) a, -b), with r^(-b) = r^(k2-b). */
static int ginv(const Group *g, int x) {
    int a = x / g->k2, b = x % g->k2;
    int nb = (g->k2 - b) % g->k2;
    long t = (((long)(g->m - g->rp[nb])) % g->m) * a % g->m;
    return (int)(t * g->k2 + nb);
}

static int make_group(Group *g, int m, int k2, int r) {
    if (m < 2 || k2 < 1 || k2 > 63) return 0;
    g->m = m;
    g->k2 = k2;
    g->G = m * k2;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        g->rp[b] = (int)p;
        p = p * r % m;
    }
    return p == 1 % m;
}

/* Uniformly random r in Z_m with r^k2 = 1 mod m (r = 1 always qualifies). */
static int pick_r(int m, int k2) {
    long cnt = 0;
    for (int c = 1; c < m; c++)
        if (powmod(c, k2, m) == 1 % m) cnt++;
    if (cnt == 0) return 1;
    long pick = (long)(rnd() % (u64)cnt);
    for (int c = 1; c < m; c++)
        if (powmod(c, k2, m) == 1 % m) {
            if (pick == 0) return c;
            pick--;
        }
    return 1;
}

static Group grp;
static int K, G, N;
static int L[MAXDEG][MAXK];   /* partner B-block of A-block i in layer l */
static int S[MAXDEG][MAXK];   /* voltage of dart (l, i) */
static int *nbr;              /* nbr[l * NCAP + v] */
static u64 *curR, *T1, *T2, *last_R;

static Group bestGrp;
static int bestK;
static int bestL[MAXDEG][MAXK], bestS[MAXDEG][MAXK];

/* A_{i,g} ~ B_{j,g*s} for dart (l, i) with j = L[l][i], s = S[l][i]. */
static void set_dart(int l, int i) {
    int j = L[l][i], s = S[l][i];
    int si = ginv(&grp, s);
    int *row = nbr + (size_t)l * NCAP;
    int ab = i * G, bb = (K + j) * G;
    for (int x = 0; x < G; x++) {
        row[ab + x] = bb + gmul(&grp, x, s);
        row[bb + x] = ab + gmul(&grp, x, si);
    }
}

/* Bit b of R[v] is set when block representative b is within distance D of v. */
static u64 *eval_reach(void) {
    u64 *a = T1, *b = T2;
    memset(a, 0, sizeof(u64) * (size_t)N);
    for (int bl = 0; bl < 2 * K; bl++) a[(size_t)bl * G] = 1ULL << bl;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) b[v] = a[v];
        for (int l = 0; l < d; l++) {
            const int *row = nbr + (size_t)l * NCAP;
            for (int v = 0; v < N; v++) b[v] |= a[row[v]];
        }
        int changed = 0;
        for (int v = 0; v < N; v++) changed |= (b[v] != a[v]);
        u64 *t = a;
        a = b;
        b = t;
        if (!changed) break;
    }
    return a;
}

/* Number of duplicate darts: same partner block and same voltage in two layers. */
static long count_dups(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (L[l1][i] == L[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    last_R = eval_reach();
    long unr = 0;
    int w = 2 * K;
    for (int v = 0; v < N; v++) unr += w - __builtin_popcountll(last_R[v]);
    return unr + PEN * count_dups();
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            L[l][i] = perm[i];
            S[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Pick a dart touching a currently unreached vertex (biased choice). */
static void pick_bad(int *lo, int *io) {
    int full = 2 * K;
    int v = rndint(N);
    for (int tries = 0; tries < 30; tries++) {
        if (__builtin_popcountll(curR[v]) != full) break;
        v = rndint(N);
    }
    int bl = v / G;
    int l = rndint(d);
    int i = 0;
    if (bl < K) {
        i = bl;
    } else {
        int j = bl - K;
        for (i = 0; i < K; i++)
            if (L[l][i] == j) break;
        if (i >= K) i = rndint(K);
    }
    *lo = l;
    *io = i;
}

/* Simulated annealing on the current group. Returns 1 when the state is valid. */
static int anneal(double deadline) {
    random_state();
    long cost = full_cost();
    memcpy(curR, last_R, sizeof(u64) * (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    double t_start = now();
    double span = deadline - t_start;
    if (span <= 0) return 0;
    double frac = 0.0;
    for (long t = 0; cost > 0; t++) {
        if ((t & 3) == 0) {
            double nw = now();
            if (nw > deadline) break;
            frac = (nw - t_start) / span;
        }
        if (t - last > PATIENCE) break;
        double temp = 0.01 * c0 * (1.0 - frac);
        if (temp < 0.3) temp = 0.3;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int a1 = L[l][i1], a2 = L[l][i2];
            L[l][i1] = a2;
            L[l][i2] = a1;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(curR, last_R, sizeof(u64) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                L[l][i1] = a1;
                L[l][i2] = a2;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l, i;
            if (rnd01() < 0.5) {
                l = rndint(d);
                i = rndint(K);
            } else {
                pick_bad(&l, &i);
            }
            int old = S[l][i];
            int nw2 = rndint(G);
            if (nw2 == old) continue;
            S[l][i] = nw2;
            set_dart(l, i);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(curR, last_R, sizeof(u64) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
    }
    return cost == 0;
}

static void print_best(void) {
    int Gb = bestGrp.G;
    long m = (long)d * bestK * Gb;
    printf("%d %ld\n", 2 * bestK * Gb, m);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < bestK; i++) {
            int j = bestL[l][i], s = bestS[l][i];
            for (int x = 0; x < Gb; x++)
                printf("%d %d\n", i * Gb + x, (bestK + j) * Gb + gmul(&bestGrp, x, s));
        }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long best_n = atol(argv[5]);
    t_end = now() + limit;
    rs ^= (u64)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 3) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound(d, D);
    if (best_n >= moore) {
        printf("0 0\n");
        return 0;
    }
    nbr = malloc(sizeof(int) * (size_t)MAXDEG * NCAP);
    curR = malloc(sizeof(u64) * NCAP);
    T1 = malloc(sizeof(u64) * NCAP);
    T2 = malloc(sizeof(u64) * NCAP);
    if (!nbr || !curR || !T1 || !T2) {
        printf("0 0\n");
        return 0;
    }

    double goal = (double)best_n * 1.02 + 2.0;
    int trials[MAXK + 1], wins[MAXK + 1];
    memset(trials, 0, sizeof trials);
    memset(wins, 0, sizeof wins);
    int have = 0;

    while (now() < t_end) {
        if (goal > (double)moore) goal = (double)moore;
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        long target = (long)ceil(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        int k2 = K2LIST[rndint(NK2)];
        long mm = (target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        if (mm > NCAP) continue;
        int m = (int)mm;
        int r = pick_r(m, k2);
        Group cand;
        if (!make_group(&cand, m, k2, r)) continue;
        long Nc = 2L * k * cand.G;
        if (Nc > NCAP || Nc > moore) continue;
        if (Nc <= best_n) {
            goal = (double)best_n * 1.01 + 2.0;
            continue;
        }
        grp = cand;
        K = k;
        G = cand.G;
        N = (int)Nc;
        trials[k]++;
        double remain = t_end - now();
        if (remain < 0.2) break;
        double cap_t = 0.3 * remain;
        if (cap_t < 6.0) cap_t = 6.0;
        if (cap_t > remain) cap_t = remain;
        int ok = anneal(now() + cap_t);
        if (ok) {
            wins[k]++;
            best_n = N;
            bestK = K;
            bestGrp = grp;
            memcpy(bestL, L, sizeof L);
            memcpy(bestS, S, sizeof S);
            have = 1;
            goal = (double)N * 1.05 + 2.0;
        } else {
            double lo = (double)best_n * 1.01 + 1.0;
            double g2 = goal * 0.995;
            goal = g2 > lo ? g2 : lo;
        }
    }

    if (have) print_best();
    else printf("0 0\n");
    return 0;
}
'''


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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions (the calibration case returns here immediately).
    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    except Exception:
        pass
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Bi-Cayley voltage-lift search in C, using the remaining budget.
    # The C budget leaves room for compilation, output parsing and lib.is_valid.
    remaining = final - time.monotonic()
    if d >= 2 and remaining > 5.0:
        c_budget = remaining - 4.0
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best_n],
                             timeout=remaining)
            n, e = lib.parse_graph_text(text)
            if n > best_n and e:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
