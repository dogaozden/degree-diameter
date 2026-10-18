"""Voltage-lift search with an exact C annealer over semidirect products Z_m x| Z_k2.

Each base graph is a d-regular bipartite multigraph on K + K vertices, written as d perfect
matchings (layers) with a voltage per dart. The lift is invariant under left multiplication
by G on every block, so the diameter condition reduces to one BFS per block representative,
which makes the cost exact and cheap. C does the search (group sampling, annealing over
voltages and layer swaps, a bandit over K), and Python only builds fallbacks and validates.
"""
import itertools
import math
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

#define MAXV 24576
#define MAXD 24
#define MAXK 8

static int d, D;
static double t_end;
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

static long long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2LL * D;
    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000LL) break;
    }
    return 2 * s;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

/* ---- semidirect group Z_GM x| Z_GK2, element a*GK2+b, (a,b)(c,e) = (a+r^b c, b+e) ---- */
static int GM = 3, GK2 = 1, GR = 1, GG = 3;
static int PW[64];

static void set_group(int m, int k2, int r) {
    GM = m; GK2 = k2; GR = r; GG = m * k2;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        PW[b] = (int)p;
        p = p * r % m;
    }
}
static int gmul(int x, int y) {
    int a = x / GK2, b = x - a * GK2;
    int c = y / GK2, e = y - c * GK2;
    int a2 = (int)((a + (long long)PW[b] * c) % GM);
    int b2 = (b + e) % GK2;
    return a2 * GK2 + b2;
}
static int ginv(int x) {
    int a = x / GK2, b = x - a * GK2;
    int nb = (GK2 - b) % GK2;
    int a2 = (int)(((long long)((GM - PW[nb]) % GM)) * a % GM);
    return a2 * GK2 + nb;
}

static void sample_group(int target) {
    static const int K2[] = {1, 1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    int nk = (int)(sizeof(K2) / sizeof(K2[0]));
    for (int t = 0; t < 100; t++) {
        int k2 = K2[rndint(nk)];
        int m = (target + k2 - 1) / k2;
        if (m < 3) m = 3;
        if (k2 == 1) { set_group(m, 1, 1); return; }
        for (int rt = 0; rt < 300; rt++) {
            int c = 1 + rndint(m - 1);
            if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                set_group(m, k2, c);
                return;
            }
        }
    }
    set_group(target < 3 ? 3 : target, 1, 1);
}

/* ---- lift state ---- */
static int K;
static long long NN;
static int perm[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXV][MAXD];

static void set_dart(int l, int i) {
    int j = perm[l][i], s = S[l][i];
    int si = ginv(s);
    int Ai = i * GG, Bj = (K + j) * GG;
    for (int g = 0; g < GG; g++) {
        nbr[Ai + g][l] = Bj + gmul(g, s);
        nbr[Bj + g][l] = Ai + gmul(g, si);
    }
}
static void rebuild_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}
static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            perm[l][i] = p[i];
            S[l][i] = rndint(GG);
        }
    }
    rebuild_all();
}

/* Sum over block representatives of unreached vertices within distance D. Exact by symmetry. */
static int vis[MAXV];
static int vstamp = 0;
static int bq[MAXV];

static long long reach_cost(void) {
    long long cost = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * GG;
        vstamp++;
        int head = 0, tail = 0;
        bq[tail++] = src;
        vis[src] = vstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = bq[head++];
                for (int l = 0; l < d; l++) {
                    int u = nbr[v][l];
                    if (vis[u] != vstamp) {
                        vis[u] = vstamp;
                        bq[tail++] = u;
                    }
                }
            }
        }
        cost += NN - tail;
    }
    return cost;
}

static long long dup_count(void) {
    long long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

static long long full_cost(void) {
    return reach_cost() + 2 * NN * dup_count();
}

static long long bestNN = 0;
static int bK, bM, bK2, bR;
static int bPerm[MAXD][MAXK], bS[MAXD][MAXK];

static void save_best(void) {
    bestNN = NN;
    bK = K; bM = GM; bK2 = GK2; bR = GR;
    memcpy(bPerm, perm, sizeof perm);
    memcpy(bS, S, sizeof S);
}

static int anneal(long long maxit, long long patience) {
    random_state();
    long long cost = full_cost();
    double T0 = 0.02 * (double)cost;
    if (T0 < 2.0) T0 = 2.0;
    long long best = cost, last = 0;
    for (long long t = 0; t < maxit; t++) {
        if (cost == 0) return 1;
        if (t - last > patience) return 0;
        if ((t & 15) == 0 && now() > t_end) return 0;
        double frac = (double)t / (double)maxit;
        double T = T0 * pow(0.01, frac);
        if (T < 0.3) T = 0.3;
        int l = rndint(d), i = rndint(K);
        if (K >= 2 && rnd01() < 0.3) {
            int i2 = rndint(K - 1);
            if (i2 >= i) i2++;
            int tmp = perm[l][i]; perm[l][i] = perm[l][i2]; perm[l][i2] = tmp;
            set_dart(l, i);
            set_dart(l, i2);
            long long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                tmp = perm[l][i]; perm[l][i] = perm[l][i2]; perm[l][i2] = tmp;
                set_dart(l, i);
                set_dart(l, i2);
            }
        } else {
            int old = S[l][i];
            int nv = rndint(GG);
            if (nv == old) continue;
            S[l][i] = nv;
            set_dart(l, i);
            long long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < best) { best = cost; last = t; }
    }
    return cost == 0;
}

static void emit(void) {
    if (bestNN == 0) { printf("0 0\n"); return; }
    K = bK;
    set_group(bM, bK2, bR);
    NN = bestNN;
    memcpy(perm, bPerm, sizeof perm);
    memcpy(S, bS, sizeof S);
    rebuild_all();
    if (full_cost() != 0) { printf("0 0\n"); return; }
    long long m = (long long)K * GG * d;
    printf("%lld %lld\n", NN, m);
    for (int v = 0; v < K * GG; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[v][l]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [hint]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double hint = argc > 5 ? atof(argv[5]) : 0.0;
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    long long mb = moore_bound();
    long long mx = mb < MAXV ? mb : MAXV;
    double goal = hint > 0 ? hint : 0.25 * (double)mb;
    if (goal < 8) goal = 8;
    if (goal > (double)mx) goal = (double)mx;

    int trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }

    while (now() < t_end) {
        if (bestNN >= mx) break;
        int kc;
        if (rnd01() < 0.2) {
            kc = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            kc = 1;
            for (int k = 1; k <= MAXK; k++) {
                double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
                if (s > bs) { bs = s; kc = k; }
            }
        }
        K = kc;
        int target = (int)ceil(goal / (2.0 * K)) + rndint(3);
        if (target < 3) target = 3;
        sample_group(target);
        NN = 2LL * K * GG;
        if (NN > mx) {
            goal *= 0.98;
            continue;
        }
        if (NN <= bestNN) {
            goal = (double)bestNN * 1.01;
            if (goal > (double)mx) goal = (double)mx;
            continue;
        }
        trials[K]++;
        if (anneal(6000, 1200)) {
            wins[K]++;
            if (NN > bestNN) save_best();
            goal = (double)NN * 1.02;
            if (goal > (double)mx) goal = (double)mx;
        } else {
            double g2 = goal * 0.99;
            double lo = (double)bestNN * 1.01;
            goal = g2 > lo ? g2 : lo;
        }
    }
    emit();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions used for calibration-style cases.
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

    # Main search: exact voltage-lift annealing in C.
    budget = max(1.0, 0.85 * time_limit - 3.0 - (time.monotonic() - t0))
    hint = int(0.21 * lib.moore_bound(d, D))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), hint],
                         stdin_graph=None, timeout=budget + 4)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
