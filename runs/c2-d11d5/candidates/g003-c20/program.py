"""Combined program: exact constructions where they exist, then a C bi-Cayley voltage-lift search.

New in this version:
  * The C engine searches voltage lifts over semidirect products Z_m x| Z_k2 with
    k = 1..6 base vertices per side, entirely in C (about 50x faster than the numpy version).
  * Representative reach: because left multiplication by the group is an automorphism of
    the lift, a lift has diameter <= D iff every vertex is within distance D of each of
    the 2k block representatives (g = identity). This needs one bitmask of 2k bits per
    vertex, instead of a full N x N reachability table.
  * Incremental updates: a voltage or layer-swap move refreshes only the affected blocks of
    the neighbour table.

Every returned graph is checked with lib.is_valid. K_{d,d} (or an exact construction) is the fallback.
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

#define MAXN 24000
#define MAXD 16
#define MAXK 6
#define MAXP 64
#define PEN 2000L

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ---- group Z_m x| Z_k2, element (a,b) coded as a*K2+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
static int MM = 2, K2 = 1, RR = 1, GO = 2;
static long PW[MAXP];

static void set_group(int m, int k2, int r) {
    MM = m;
    K2 = k2;
    RR = r;
    GO = m * k2;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        PW[b] = p;
        p = p * r % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    long t = ((long)a + PW[b] * (long)c) % MM;
    int be = b + e;
    if (be >= K2) be -= K2;
    return (int)t * K2 + be;
}

static inline int ginv(int x) {
    int a = x / K2, b = x - a * K2;
    int nb_ = (K2 - b) % K2;
    long t = PW[nb_] * (long)a % MM;
    long na = (MM - t) % MM;
    return (int)na * K2 + nb_;
}

/* ---- lift state ---- */
static int K = 1, G = 2, N = 4;
static int lay[MAXD][MAXK], ilay[MAXD][MAXK], S[MAXD][MAXK];
static int nb[MAXN][MAXD];
static uint32_t ra[MAXN], rb[MAXN];
static uint32_t *lastR = ra;

/* A block i, vertex i*G+g, dart (l,i) -> B block p=lay[l][i]: neighbour (K+p)*G + g*s. */
static void refresh_A(int l, int i) {
    int p = lay[l][i], s = S[l][i];
    int base = i * G, tb = (K + p) * G;
    for (int g = 0; g < G; g++) nb[base + g][l] = tb + gmul(g, s);
}

/* B block p, vertex (K+p)*G+h, partner A block i=ilay[l][p]: neighbour i*G + h*s^-1. */
static void refresh_B(int l, int p) {
    int i = ilay[l][p], s = S[l][i], si = ginv(s);
    int base = (K + p) * G, tb = i * G;
    for (int h = 0; h < G; h++) nb[base + h][l] = tb + gmul(h, si);
}

static void refresh_all(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) ilay[l][lay[l][i]] = i;
        for (int i = 0; i < K; i++) refresh_A(l, i);
        for (int p = 0; p < K; p++) refresh_B(l, p);
    }
}

static void apply_swap(int l, int i1, int i2) {
    int p1 = lay[l][i1], p2 = lay[l][i2];
    lay[l][i1] = p2;
    lay[l][i2] = p1;
    ilay[l][p1] = i2;
    ilay[l][p2] = i1;
    refresh_A(l, i1);
    refresh_A(l, i2);
    refresh_B(l, p1);
    refresh_B(l, p2);
}

static void apply_volt(int l, int i, int s) {
    S[l][i] = s;
    refresh_A(l, i);
    refresh_B(l, lay[l][i]);
}

/* Representative reach: bit b of R[v] is set when block representative b (vertex b*G) is
 * within distance D of v. Left-translation symmetry makes this equivalent to diameter <= D.
 * Returns the number of unreached (vertex, representative) pairs. */
static long reach_eval(void) {
    uint32_t full = (1u << (2 * K)) - 1u;
    uint32_t *R = ra, *Q = rb;
    for (int v = 0; v < N; v++) R[v] = 0;
    for (int b = 0; b < 2 * K; b++) R[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t u = R[v];
            const int *nv = nb[v];
            for (int l = 0; l < d; l++) u |= R[nv[l]];
            Q[v] = u;
            changed |= (u != R[v]);
        }
        uint32_t *t = R;
        R = Q;
        Q = t;
        if (!changed) break;
    }
    lastR = R;
    long bad = 0;
    for (int v = 0; v < N; v++) bad += __builtin_popcount(full & ~R[v]);
    return bad;
}

/* Parallel edges: same A block, same B block (same layer partner), same voltage. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

static long eval_cost(void) { return reach_eval() + PEN * dup_count(); }

static int accept(long c2, long cost, double T) {
    if (c2 <= cost) return 1;
    return rnd01() < exp(-(double)(c2 - cost) / T);
}

/* Simulated annealing on the current group. Returns 0 on success (state is valid). */
static long anneal(long iters, double until) {
    refresh_all();
    long cost = eval_cost();
    if (cost == 0) return 0;
    double c0 = (double)cost;
    long best = cost, last = 0;
    for (long t = 0; t < iters; t++) {
        if ((t & 31) == 0 && now() > until) break;
        if (t - last > iters / 3 + 500) break;
        double frac = (double)t / (double)iters;
        double T = 0.02 * c0 * (1.0 - frac) + 0.3;
        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            apply_swap(l, i1, i2);
            long c2 = eval_cost();
            if (accept(c2, cost, T)) cost = c2;
            else apply_swap(l, i1, i2);
        } else {
            int l, i;
            if (rnd01() < 0.5 && lastR) {
                uint32_t full = (1u << (2 * K)) - 1u;
                int v = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int cand = rndint(N);
                    if (lastR[cand] != full) { v = cand; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndint(d);
                    if (b < K) i = b;
                    else i = ilay[l][b - K];
                } else {
                    l = rndint(d);
                    i = rndint(K);
                }
            } else {
                l = rndint(d);
                i = rndint(K);
            }
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            apply_volt(l, i, nw);
            long c2 = eval_cost();
            if (accept(c2, cost, T)) cost = c2;
            else apply_volt(l, i, old);
        }
        if (cost < best) { best = cost; last = t; }
        if (cost == 0) return 0;
    }
    return cost;
}

/* ---- group sampling ---- */
static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}
static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void sample_group(long target) {
    static const int K2S[13] = {1, 1, 1, 2, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    int k2 = K2S[rndint(13)];
    long m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 == 2 && m >= 3 && rnd01() < 0.3) {
        r = (int)(m - 1);
    } else if (k2 >= 2 && m >= 3) {
        for (int tr = 0; tr < 40; tr++) {
            long c = 1 + rndint((int)(m - 1));
            if (gcdl(c, m) == 1 && powmodl(c, k2, m) == 1 % m) { r = (int)c; break; }
        }
    }
    set_group((int)m, k2, r);
}

static int pick_k(const int *wins, const int *trials) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.05 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

static long moore_bound(int dd, int DD) {
    if (DD <= 0 || dd <= 0) return 1;
    if (dd == 1) return 2;
    if (dd == 2) return 2L * DD;
    long s = 0, p = 1;
    for (int i = 0; i < DD; i++) {
        s += p;
        p *= (dd - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int blay[MAXD][MAXK], bS[MAXD][MAXK];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    double t0 = now();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    t_end = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long cap = moore_bound(d, D);
    if (cap > MAXN) cap = MAXN;

    int wins[MAXK + 1], trials[MAXK + 1];
    memset(wins, 0, sizeof wins);
    memset(trials, 0, sizeof trials);

    const long ITERS = 8000;
    long goal = 2L * d + 2;
    long bestN = 0;
    int bK = 0, bG = 0, bM = 0, bK2 = 0, bR = 0;

    while (now() < t_end) {
        if (bestN >= cap) break;
        if (goal > cap) goal = cap;
        if (goal < bestN + 1) goal = bestN + 1;
        if (goal > cap) break;

        int k = pick_k(wins, trials);
        long target = goal / (2L * k) + rndint(3);
        if (target < 2) target = 2;
        sample_group(target);
        long Nc = 2L * k * GO;
        if (Nc > cap) continue;

        K = k;
        G = GO;
        N = (int)Nc;
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < K; i++) lay[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = lay[l][i];
                lay[l][i] = lay[l][j];
                lay[l][j] = tmp;
            }
            for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        }

        trials[k]++;
        long c = anneal(ITERS, t_end);
        if (c == 0) {
            wins[k]++;
            bestN = N;
            memcpy(blay, lay, sizeof lay);
            memcpy(bS, S, sizeof S);
            bK = K;
            bG = G;
            bM = MM;
            bK2 = K2;
            bR = RR;
            goal = (long)(N * 1.03) + 2;
        } else {
            long g2 = (long)(bestN * 1.01) + 1;
            long g3 = goal * 995 / 1000;
            goal = g2 > g3 ? g2 : g3;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK2, bR);
    K = bK;
    G = bG;
    N = 2 * K * G;
    memcpy(lay, blay, sizeof lay);
    memcpy(S, bS, sizeof S);
    refresh_all();
    if (eval_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    long m = (long)(K * G) * d;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[v][l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions for the small-D cases.
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

    # Main search: C bi-Cayley voltage-lift annealing with representative reach.
    deadline = t0 + 0.9 * time_limit - 1.5
    budget = deadline - time.monotonic() - 1.0
    if d >= 2 and D >= 2 and budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             timeout=budget + 3.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
