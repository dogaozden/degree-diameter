"""Lift search with a C annealer over bi-Cayley voltage lifts on semidirect products Z_m x| Z_k2.

The C engine samples base sizes k, groups and voltages, anneals to a zero-cost lift
(every pair within distance D), and ratchets the target order upward after each success.
Python builds exact constructions first (projective plane, Araujo-Pardo-Lopez, GQ(W(q)))
and falls back to K_{d,d}. Every returned graph passes lib.is_valid.
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

#define MAXN 16384
#define MAXK 8
#define MAXD 32
#define MAXPOW 64
#define PEN 1000L
#define PATIENCE 30000L

static int d, D;
static uint64_t rs = 88172645463325252ULL;

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
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ---- group Z_M x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + R^b c, b+e) ---- */
static int Mm, K2, Rr, G;
static int powr[MAXPOW];

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static long powmod_i(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static void set_group(int m, int k2, int r) {
    Mm = m;
    K2 = k2;
    Rr = r;
    G = m * k2;
    powr[0] = 1 % m;
    for (int t = 1; t < k2; t++) powr[t] = (int)((long)powr[t - 1] * r % m);
}
static inline int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int t = (int)(((long)powr[b] * c + a) % Mm);
    int f = b + e;
    if (f >= K2) f -= K2;
    return t * K2 + f;
}
static inline int ginv(int x) {
    int a = x / K2, b = x - a * K2;
    int nb = (K2 - b) % K2;
    int neg = (Mm - powr[nb]) % Mm;
    int c = (int)(((long)neg * a) % Mm);
    return c * K2 + nb;
}

/* ---- lift state: base size K, layers are permutations of K blocks ---- */
static int K, N;
static int layers[MAXD][MAXK], invl[MAXD][MAXK];
static int S[MAXD][MAXK], Si[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t Ra[MAXN], Rb[MAXN];

/* A_{i,g} ~ B_{j,g*s} with j = layers[l][i]; B_{j,h} ~ A_{i,h*s^-1}. */
static void set_dart(int l, int i) {
    int j = layers[l][i], s = S[l][i], si = Si[l][i];
    int ab = i * G, bb = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ab + g] = bb + gmul(g, s);
        nbr[l][bb + g] = ab + gmul(g, si);
    }
}

static void swap_perm(int l, int i1, int i2) {
    int j1 = layers[l][i1], j2 = layers[l][i2];
    layers[l][i1] = j2;
    layers[l][i2] = j1;
    invl[l][j2] = i1;
    invl[l][j1] = i2;
    set_dart(l, i1);
    set_dart(l, i2);
}

static void random_config(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layers[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < K; i++) invl[l][layers[l][i]] = i;
        for (int i = 0; i < K; i++) {
            S[l][i] = rndint(G);
            Si[l][i] = ginv(S[l][i]);
            set_dart(l, i);
        }
    }
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Sum over vertices v and blocks b of [dist(v, rep_b) > D], rep_b = b*G (identity). */
static long compute_cost(void) {
    uint64_t *cur = Ra, *nxt = Rb;
    for (int v = 0; v < N; v++) cur[v] = (v % G == 0) ? (1ULL << (v / G)) : 0ULL;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t acc = cur[v];
            for (int l = 0; l < d; l++) acc |= cur[nbr[l][v]];
            nxt[v] = acc;
            if (acc != cur[v]) changed = 1;
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) cost += 2 * K - __builtin_popcountll(cur[v]);
    return cost;
}

/* Simulated annealing on voltages and layer permutations until cost 0 or time out. */
static int anneal(double slice_end) {
    double t_start = now();
    double span = slice_end - t_start;
    long cost = compute_cost() + PEN * dupcount();
    if (cost == 0) return 1;
    if (span <= 0) return 0;
    double T0 = 0.02 * (double)cost;
    if (T0 < 2.0) T0 = 2.0;
    double Tend = 0.3;
    double temp = T0;
    long last_imp = 0, best = cost;
    for (long it = 1;; it++) {
        if ((it & 7) == 0) {
            double tn = now();
            if (tn >= slice_end) break;
            double frac = (tn - t_start) / span;
            temp = T0 * pow(Tend / T0, frac);
        }
        if (it - last_imp > PATIENCE) break;
        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_perm(l, i1, i2);
            long nc = compute_cost() + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                swap_perm(l, i1, i2);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            Si[l][i] = ginv(nw);
            set_dart(l, i);
            long nc = compute_cost() + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                S[l][i] = old;
                Si[l][i] = ginv(old);
                set_dart(l, i);
            }
        }
        if (cost < best) {
            best = cost;
            last_imp = it;
        }
        if (cost == 0) return 1;
    }
    return cost == 0;
}

static const int KCH[] = {1, 2, 3, 4, 5, 6};
static const int K2CH[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
static int trials[MAXK + 1], wins[MAXK + 1];

static int choose_k(void) {
    if (rnd01() < 0.2) return KCH[rndint(6)];
    int bestk = 1;
    double bs = -1.0;
    for (int idx = 0; idx < 6; idx++) {
        int k = KCH[idx];
        double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.05 * rnd01();
        if (sc > bs) {
            bs = sc;
            bestk = k;
        }
    }
    return bestk;
}

/* Random semidirect group with order >= Gmin (r = 1 gives an abelian product). */
static void sample_group(long Gmin) {
    int k2 = K2CH[rndint(20)];
    long m = (Gmin + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && m > 2 && rndint(3) != 0) {
        for (int t = 0; t < 80; t++) {
            long c = 2 + rndint((int)(m - 2));
            if (gcd_i((int)c, (int)m) == 1 && powmod_i(c, k2, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    set_group((int)m, k2, r);
}

static long moore_bound(void) {
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

static int best_nbr[MAXD][MAXN];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t_end = now() + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long cap = MAXN;
    if (moore < cap) cap = moore;
    double goal = moore / 5.0;
    if (goal > cap) goal = (double)cap;

    long best_n = 0, best_A = 0;
    int best_d = d;

    while (now() < t_end) {
        if (goal > cap) goal = (double)cap;
        if (best_n >= moore) break;
        double left = t_end - now();
        if (left < 0.3) break;

        int k = choose_k();
        double slice = left / 5.0;
        if (slice < 3.0) slice = 3.0;
        if (slice > left) slice = left;

        long Gmin = (long)ceil(goal / (2.0 * k)) + rndint(3);
        K = k;
        sample_group(Gmin);
        long n_try = 2L * K * G;
        if (n_try > cap || n_try > MAXN) {
            goal *= 0.995;
            continue;
        }
        N = (int)n_try;
        trials[k]++;
        random_config();

        if (anneal(now() + slice)) {
            wins[k]++;
            best_n = N;
            best_A = (long)K * G;
            best_d = d;
            for (int l = 0; l < d; l++) memcpy(best_nbr[l], nbr[l], sizeof(int) * (size_t)N);
            goal = N * 1.01;
        } else {
            goal *= 0.99;
            if (goal < 2.0 * d) goal = 2.0 * d;
            if (best_n > 0 && goal < best_n * 1.01) goal = best_n * 1.01;
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", best_n, best_A * best_d);
    for (long v = 0; v < best_A; v++)
        for (int l = 0; l < best_d; l++)
            printf("%ld %d\n", v, best_nbr[l][v]);
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

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

    # Main search: C annealer over bi-Cayley lifts, using nearly all remaining time.
    total = max(1.0, 0.9 * time_limit - 2.0)
    budget = t0 + total - time.monotonic() - 1.0
    if budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             timeout=budget + 6.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
