"""Bi-Cayley voltage-lift search with a C annealer (new engine), plus exact small constructions.

Construction: vertices A_{i,g} and B_{j,h} for base blocks i, j < k and g, h in a semidirect
product G = Z_m x| Z_k2. Each of the d layers is a permutation of the blocks, with voltage
s: A_{i,g} ~ B_{p,g*s}. Left multiplication by G is an automorphism, so the graph has
diameter <= D iff every block representative reaches all N vertices within D steps.

The C engine (new in this version) anneals over block permutations and voltages, using
2k BFS runs per evaluation (not a full all-pairs bitset). Python samples groups and bases
with a bandit, ratchets the target order, and keeps the largest graph that passes lib.is_valid.
K_{d,d} (or an exact construction) is always the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage: prog d D seed time_limit m k2 r k
 * Group: Z_m x| Z_k2, element (a,b) coded a*k2+b, (a,b)*(c,e) = (a + r^b c, b + e).
 * Output: "N M" and M edges of a valid lift with N = 2*k*m*k2 vertices, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXDEG 16
#define MAXK 8
#define MAXN 20000
#define RESTART_IT 6000

static int d, D, k, k2, m, r, G, N;
static int powr[64];
static int lay[MAXDEG][MAXK], sv[MAXDEG][MAXK], ilay[MAXDEG][MAXK], invs[MAXDEG][MAXK];
static int nb[MAXN][MAXDEG];
static int vis[MAXN];
static int qu[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long t = (long)powr[b] * c + a;
    return (int)(t % m) * k2 + (b + e) % k2;
}

static int ginv(int x) {
    int a = x / k2, b = x % k2;
    int nbb = (k2 - b) % k2;
    long t = (long)powr[nbb] * a;
    int c = (int)((m - t % m) % m);
    return c * k2 + nbb;
}

static void build_nbr(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            ilay[l][lay[l][i]] = i;
            invs[l][i] = ginv(sv[l][i]);
        }
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int p = lay[l][i];
                nb[v][l] = (k + p) * G + gmul(g, sv[l][i]);
            }
        }
    for (int j = 0; j < k; j++)
        for (int h = 0; h < G; h++) {
            int w = (k + j) * G + h;
            for (int l = 0; l < d; l++) {
                int ai = ilay[l][j];
                nb[w][l] = ai * G + gmul(h, invs[l][ai]);
            }
        }
}

static int ball_size(int src) {
    stamp++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp;
    for (int dep = 0; dep < D; dep++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int v = qu[head++];
            for (int l = 0; l < d; l++) {
                int u = nb[v][l];
                if (vis[u] != stamp) {
                    vis[u] = stamp;
                    qu[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Zero iff the lift is simple and has diameter <= D (by left-translation symmetry). */
static long eval_cost(void) {
    build_nbr();
    long unr = 0, dup = 0;
    for (int b = 0; b < 2 * k; b++) unr += N - ball_size(b * G);
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && sv[l1][i] == sv[l2][i]) dup++;
    return unr + (long)N * dup;
}

static void randomize(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < k; i++) sv[l][i] = rndint(G);
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    m = atoi(argv[5]);
    k2 = atoi(argv[6]);
    r = atoi(argv[7]);
    k = atoi(argv[8]);
    if (d < 1 || d > MAXDEG || D < 1 || k < 1 || k > MAXK || m < 2 || k2 < 1 || k2 > 64) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    N = 2 * k * G;
    if (N > MAXN) {
        printf("0 0\n");
        return 0;
    }
    if (r < 0 || r >= m) {
        printf("0 0\n");
        return 0;
    }
    powr[0] = 1 % m;
    for (int t = 1; t < k2; t++) powr[t] = (int)((long)powr[t - 1] * r % m);
    if ((long)powr[k2 - 1] * r % m != 1 % m || gcdi(r, m) != 1) {
        printf("0 0\n");
        return 0;
    }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    double t_end = now() + limit;
    int found = 0;
    while (!found && now() < t_end) {
        randomize();
        long cur = eval_cost();
        double c0 = cur > 1 ? (double)cur : 1.0;
        for (int it = 0; it < RESTART_IT; it++) {
            if ((it & 31) == 0 && now() > t_end) break;
            double frac = (double)it / RESTART_IT;
            double T = 0.05 * c0 * (1.0 - frac) + 0.3;
            int saveL[MAXDEG][MAXK], saveS[MAXDEG][MAXK];
            memcpy(saveL, lay, sizeof lay);
            memcpy(saveS, sv, sizeof sv);
            if (k >= 2 && rnd01() < 0.35) {
                int l = rndint(d);
                int i1 = rndint(k);
                int i2 = rndint(k - 1);
                if (i2 >= i1) i2++;
                int t = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = t;
            } else {
                int l = rndint(d);
                int i = rndint(k);
                sv[l][i] = rndint(G);
            }
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) {
                    found = 1;
                    break;
                }
            } else {
                memcpy(lay, saveL, sizeof lay);
                memcpy(sv, saveS, sizeof sv);
            }
        }
    }

    if (!found || eval_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    long M = (long)k * G * d;
    printf("%d %ld\n", N, M);
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[v][l]);
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
                for s in L:
                    if p < s:
                        covered.add((p, s))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Group sampling for Z_m x| Z_k2.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) with m*k2 >= target, r^k2 = 1 mod m and gcd(r, m) = 1, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        if k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) == 1 and pow(r, 2, m) == 1 % m:
                return m, 2, r
            continue
        for _ in range(60):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


_KS = (1, 2, 3, 4, 5, 6)
_N_MAX = 19000


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
    rng = random.Random(seed)

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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Bi-Cayley annealing in C: a bandit over base sizes k and group orders,
    # with a ratcheted target order.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = min(float(best_n) * 1.3, _N_MAX)
    call = 0

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = final - time.monotonic()
        if remaining < 2.0:
            break
        k = pick_k()
        target = max(2, int(math.ceil(goal / (2 * k))))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(best_n * 1.03, goal * 0.93)
            continue
        m, k2, r = g
        n_try = 2 * k * m * k2
        if n_try <= best_n:
            goal = max(goal, best_n * 1.05)
            continue
        if n_try > 20000:
            goal = max(best_n * 1.03, goal * 0.93)
            continue

        slice_s = min(remaining - 0.5, max(3.0, min(10.0, remaining / 4.0)))
        if slice_s < 1.0:
            break
        trials[k] += 1
        out = None
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 1000 + call, round(slice_s * 0.9, 2),
                                        m, k2, r, k],
                             timeout=slice_s + 5)
            out = lib.parse_graph_text(text)
        except Exception:
            out = None
        call += 1

        if out is not None and out[0] > best_n:
            before = best_n
            consider(out[0], out[1])
            if best_n > before:
                wins[k] += 1
                goal = min(max(goal, best_n * 1.08), _N_MAX)
            else:
                goal = max(best_n * 1.03, goal * 0.93)
        else:
            goal = max(best_n * 1.03, goal * 0.93)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
