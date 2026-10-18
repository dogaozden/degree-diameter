"""Bold variant: bi-Cayley lift annealing moved into C.

Lifts are G-invariant under left multiplication, so validity only needs the reach
bitmasks of the 2K block representatives. C runs simulated annealing over layer
permutations and voltages for semidirect groups Z_m x| Z_k2, with a bandit over the
block count K and a ratcheted order goal. Python supplies exact constructions as the
fallback and validates every returned graph with lib.is_valid.
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

#define MAXL 32
#define MAXK 8
#define MAXG 8192
#define MAXN 65536
#define PEN 1000L
#define KUSE 6

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* ---- group Z_m x| Z_k2, element a*k2 + b, (a,b)(c,e) = (a + r^b c, b + e) ---- */
static int GM = 2, GK2 = 1;
static int rpow[64];

static int gcdi(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void set_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    rpow[0] = 1 % m;
    for (int b = 1; b < k2; b++) rpow[b] = (int)((long long)rpow[b - 1] * r % m);
}

static inline int gmulv(int x, int y) {
    int a = x / GK2, b = x - a * GK2;
    int c = y / GK2, e = y - c * GK2;
    int na = (int)(((long long)a + (long long)rpow[b] * c) % GM);
    int nb = b + e;
    if (nb >= GK2) nb -= GK2;
    return na * GK2 + nb;
}

/* ---- lift state: K A-blocks, K B-blocks, G elements each, d layers ---- */
static int K, G, N;
static int lay[MAXL][MAXK], layinv[MAXL][MAXK], S[MAXL][MAXK];
static int nbr[MAXL][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN], wa[MAXN], wb[MAXN];
static uint64_t *acc = bufA, *cand = bufB;

static int bestN = 0, bK = 1, bG = 2, bm = 2, bk2 = 1, br = 1;
static int bL[MAXL][MAXK], bS[MAXL][MAXK];

/* A-block i, layer l, pairs with B-block p under voltage s: A_{i,g} ~ B_{p,g*s}. */
static void set_dart(int l, int i, int p, int s) {
    int ba = i * G, bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int a = ba + g;
        int b = bb + gmulv(g, s);
        nbr[l][a] = b;
        nbr[l][b] = a;
    }
}

static long dup_count(void) {
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return dup;
}

/* Computes reach masks into res and returns the cost (0 means valid). */
static long eval_into(uint64_t *res) {
    int NN = 2 * K * G;
    int full = 2 * K;
    uint64_t *c = wa, *a = wb;
    for (int v = 0; v < NN; v++) c[v] = (v % G == 0) ? (1ULL << (v / G)) : 0ULL;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            uint64_t x = c[v];
            for (int l = 0; l < d; l++) x |= c[nbr[l][v]];
            a[v] = x;
            if (x != c[v]) changed = 1;
        }
        uint64_t *t = c;
        c = a;
        a = t;
        if (!changed) break;
    }
    memcpy(res, c, sizeof(uint64_t) * (size_t)NN);
    long unr = 0;
    for (int v = 0; v < NN; v++) unr += full - __builtin_popcountll(res[v]);
    return unr + PEN * dup_count();
}

static void swap_layers(int l, int i1, int i2) {
    int p1 = lay[l][i1], p2 = lay[l][i2];
    lay[l][i1] = p2;
    lay[l][i2] = p1;
    layinv[l][p2] = i1;
    layinv[l][p1] = i2;
    set_dart(l, i1, p2, S[l][i1]);
    set_dart(l, i2, p1, S[l][i2]);
}

static void set_volt(int l, int i, int s) {
    S[l][i] = s;
    set_dart(l, i, lay[l][i], s);
}

static int anneal(int k, int g, int m, int k2, int r, double deadline, long iters, long patience) {
    K = k;
    G = g;
    N = 2 * K * G;
    set_group(m, k2, r);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            layinv[l][lay[l][i]] = i;
            S[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i, lay[l][i], S[l][i]);

    uint64_t fullmask = (1ULL << (2 * K)) - 1;
    long cost = eval_into(acc);
    double T0 = 0.05 * (double)cost + 1.0;
    long rb = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > deadline) break;
        double frac = (double)t / (double)iters;
        double T = T0 * pow(0.01, frac);
        if (T < 0.05) T = 0.05;

        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_layers(l, i1, i2);
            long nc = eval_into(cand);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                uint64_t *tmp = acc;
                acc = cand;
                cand = tmp;
                cost = nc;
                if (cost < rb) {
                    rb = cost;
                    last = t;
                }
            } else {
                swap_layers(l, i1, i2);
            }
        } else {
            int l = rndint(d), i = -1;
            if (rnd01() < 0.5) {
                for (int tr = 0; tr < 30 && i < 0; tr++) {
                    int v = rndint(N);
                    if (acc[v] != fullmask) {
                        int blk = v / G;
                        i = (blk < K) ? blk : layinv[l][blk - K];
                    }
                }
            }
            if (i < 0) i = rndint(K);
            int old = S[l][i];
            int ns = rndint(G);
            if (ns == old) continue;
            set_volt(l, i, ns);
            long nc = eval_into(cand);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                uint64_t *tmp = acc;
                acc = cand;
                cand = tmp;
                cost = nc;
                if (cost < rb) {
                    rb = cost;
                    last = t;
                }
            } else {
                set_volt(l, i, old);
            }
        }
    }
    return cost == 0;
}

static void save_best(int m, int k2, int r) {
    bestN = N;
    bK = K;
    bG = G;
    bm = m;
    bk2 = k2;
    br = r;
    memcpy(bL, lay, sizeof lay);
    memcpy(bS, S, sizeof S);
}

static int rebuild(void) {
    K = bK;
    G = bG;
    N = 2 * K * G;
    set_group(bm, bk2, br);
    memcpy(lay, bL, sizeof lay);
    memcpy(S, bS, sizeof S);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) layinv[l][lay[l][i]] = i;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i, lay[l][i], S[l][i]);
    return eval_into(cand) == 0;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int sample_group(int target, int *om, int *ok2, int *orr) {
    static const int CH[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    int nch = (int)(sizeof CH / sizeof CH[0]);
    for (int att = 0; att < 300; att++) {
        int k2 = CH[rndint(nch)];
        int m = (target + k2 - 1) / k2 + rndint(3);
        if (m < 2) m = 2;
        if (k2 == 1) {
            *om = m;
            *ok2 = 1;
            *orr = 1;
            return 1;
        }
        int r = -1;
        if (k2 == 2 && rndint(10) < 3) {
            int c = m - 1;
            if (c >= 1 && gcdi(c, m) == 1 && powmod(c, 2, m) == 1 % m) r = c;
        }
        for (int t = 0; r < 0 && t < 80; t++) {
            int c = 1 + rndint(m - 1);
            if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) r = c;
        }
        if (r < 0) continue;
        *om = m;
        *ok2 = k2;
        *orr = r;
        return 1;
    }
    return 0;
}

static int pick_k(const long *trials, const long *wins) {
    if (rnd01() < 0.2) return 1 + rndint(KUSE);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= KUSE; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit base_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long base_n = atol(argv[5]);
    if (d < 2 || d > MAXL || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t_end = now() + limit - 0.5;
    long moore = moore_bound();
    double goal = (double)base_n * 1.05;
    if (goal < 4.0) goal = 4.0;
    long trials[KUSE + 1] = {0}, wins[KUSE + 1] = {0};

    while (now() < t_end) {
        if (goal > (double)moore) goal = (double)moore;
        if (goal > MAXN / 2.0) goal = MAXN / 2.0;
        int k = pick_k(trials, wins);
        int tg = (int)(goal / (2.0 * k)) + rndint(3);
        if (tg < 2) tg = 2;
        int m, k2, r;
        if (!sample_group(tg, &m, &k2, &r)) {
            goal *= 0.99;
            continue;
        }
        int g = m * k2;
        if (g > MAXG || 2L * k * g > MAXN) {
            goal *= 0.99;
            continue;
        }
        int NN = 2 * k * g;
        long known = bestN > base_n ? bestN : base_n;
        if (NN <= known) {
            if (goal < known * 1.01) goal = known * 1.01;
            continue;
        }
        trials[k]++;
        int ok = anneal(k, g, m, k2, r, t_end - 0.2, 400000L, 4000L);
        if (ok) {
            wins[k]++;
            if (NN > bestN) save_best(m, k2, r);
            if (goal < NN * 1.10) goal = NN * 1.10;
        } else {
            double floor_goal = (double)known * 1.01;
            goal *= 0.97;
            if (goal < floor_goal) goal = floor_goal;
        }
    }

    if (bestN > base_n && rebuild()) {
        long mm = (long)d * bK * bG;
        int KG = bK * bG;
        printf("%d %ld\n", bestN, mm);
        for (int u = 0; u < KG; u++)
            for (int l = 0; l < d; l++) printf("%d %d\n", u, nbr[l][u]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (fallbacks and calibration cases).
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

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() - t0 < 0.3 * time_limit:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Phase 2 (main): C bi-Cayley lift annealing, started from the best construction.
    if best_n >= lib.moore_bound(d, D):
        return best
    budget = 0.82 * time_limit - 3.0 - (time.monotonic() - t0)
    if 2 <= d <= 32 and D >= 2 and budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                             stdin_graph=None, timeout=budget + 8.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    return best
