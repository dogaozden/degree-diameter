import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over voltages of bi-Cayley lifts on Z_M x| Z_K2.
#
# Group element (a, b) is coded a*K2 + b with (a,b)(c,e) = (a + r^b c, b+e).
# Base: KK vertices per side and dd layers. Each layer is a permutation of
# range(KK), so every vertex has degree exactly dd. Dart t = (i, j, s) joins
# A_{i,g} to B_{j, g*s} for all g. Left multiplication is an automorphism, so
# BFS from the 2*KK identity representatives decides diameter.
# Cost = unreached (representative, vertex) pairs + PEN * duplicate darts.
# The engine only reports a graph strictly larger than minN.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 6
#define MAXG 4096
#define MAXN (2 * MAXK * MAXG)
#define MAXT (MAXD * MAXK)
#define MAXE (MAXT * MAXG)
#define PEN 1000
#define ITERS 20000

static int dd, DD, KK, MM, K2, GG, NN, TT;
static long long pw[MAXG];
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int adj[MAXN * MAXD];
static int deg[MAXN];
static int vis[MAXN], que[MAXN];
static int seenk[MAXK * MAXK * MAXG];
static int stamp_v = 0, stamp_k = 0;
static uint64_t rs = 88172645463325252ULL;
static double tlimit;
static struct timespec t_start;
static int bestN = 0, bestM = 0;
static int bestEu[MAXE], bestEv[MAXE];

static uint64_t xr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(xr() % (uint64_t)n); }
static double urand(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)(t.tv_sec - t_start.tv_sec) + 1e-9 * (double)(t.tv_nsec - t_start.tv_nsec);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long na = ((long long)a + pw[b] * (long long)c) % MM;
    return (int)na * K2 + (b + e) % K2;
}

static int pick_group(int target) {
    for (int tries = 0; tries < 300 && target + tries <= MAXG; tries++) {
        int Gc = target + tries;
        int divs[64], nd = 0;
        for (int x = 1; x <= Gc && nd < 64; x++)
            if (Gc % x == 0) divs[nd++] = x;
        int k2 = divs[rndint(nd)];
        int m = Gc / k2;
        int r = 1;
        if (k2 > 1 && m >= 2) {
            int ok = 0;
            for (int t = 0; t < 100; t++) {
                int c = 1 + rndint(m - 1);
                if (gcd_i(c, m) == 1 && powmod_ll(c, k2, m) == 1 % m) { r = c; ok = 1; break; }
            }
            if (!ok) continue;
        }
        MM = m;
        K2 = k2;
        GG = m * k2;
        pw[0] = 1 % m;
        for (int b = 1; b < k2; b++) pw[b] = (pw[b - 1] * r) % m;
        return 1;
    }
    return 0;
}

static void build_adj(void) {
    memset(deg, 0, sizeof(int) * (size_t)NN);
    for (int t = 0; t < TT; t++) {
        for (int g = 0; g < GG; g++) {
            int a = dI[t] * GG + g;
            int b = (KK + dJ[t]) * GG + gmul(g, dS[t]);
            adj[a * dd + deg[a]++] = b;
            adj[b * dd + deg[b]++] = a;
        }
    }
}

static long long cost_eval(void) {
    build_adj();
    long long dup = 0;
    stamp_k++;
    for (int t = 0; t < TT; t++) {
        int key = (dI[t] * KK + dJ[t]) * GG + dS[t];
        if (seenk[key] == stamp_k) dup++;
        else seenk[key] = stamp_k;
    }
    long long total = 0;
    for (int r = 0; r < 2 * KK; r++) {
        int src = r * GG;
        stamp_v++;
        int head = 0, tail = 0;
        vis[src] = stamp_v;
        que[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = que[head++];
                for (int k = 0; k < dd; k++) {
                    int v = adj[u * dd + k];
                    if (vis[v] != stamp_v) {
                        vis[v] = stamp_v;
                        que[tail++] = v;
                    }
                }
            }
        }
        total += NN - tail;
    }
    return total + (long long)PEN * dup;
}

static void init_layers(void) {
    for (int l = 0; l < dd; l++) {
        int perm[MAXK];
        for (int i = 0; i < KK; i++) perm[i] = i;
        for (int i = KK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < KK; i++) {
            int t = l * KK + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(GG);
        }
    }
}

static void save_best(void) {
    int m = 0;
    for (int t = 0; t < TT; t++)
        for (int g = 0; g < GG; g++) {
            int a = dI[t] * GG + g;
            int b = (KK + dJ[t]) * GG + gmul(g, dS[t]);
            bestEu[m] = a;
            bestEv[m] = b;
            m++;
        }
    bestM = m;
    bestN = NN;
}

static long long anneal(int iters) {
    init_layers();
    long long cur = cost_eval();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > tlimit) break;
        double temp = 2.0 * (1.0 - (double)it / (double)iters) + 0.05;
        int swapmove = (KK >= 2 && rndint(3) == 0);
        if (!swapmove) {
            int t = rndint(TT);
            int old = dS[t];
            int nw = rndint(GG);
            if (nw == old) continue;
            dS[t] = nw;
            long long c2 = cost_eval();
            if (c2 <= cur || urand() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else dS[t] = old;
        } else {
            int l = rndint(dd);
            int i1 = rndint(KK), i2 = rndint(KK);
            if (i1 == i2) continue;
            int a = l * KK + i1, b = l * KK + i2;
            int tmp = dJ[a];
            dJ[a] = dJ[b];
            dJ[b] = tmp;
            long long c2 = cost_eval();
            if (c2 <= cur || urand() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else {
                tmp = dJ[a];
                dJ[a] = dJ[b];
                dJ[b] = tmp;
            }
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    tlimit = atof(argv[4]);
    int minN = argc > 5 ? atoi(argv[5]) : 0;
    if (dd < 1 || dd > MAXD || DD < 1) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    clock_gettime(CLOCK_MONOTONIC, &t_start);

    int best_n = minN;
    static const int ks[5] = {1, 2, 2, 3, 4};
    while (elapsed() < tlimit) {
        KK = ks[rndint(5)];
        int base = best_n / (2 * KK);
        int target = base + 1 + rndint(base / 40 + 2);
        if (!pick_group(target)) continue;
        NN = 2 * KK * GG;
        if (NN > MAXN) continue;
        TT = dd * KK;
        long long c = anneal(ITERS);
        if (c == 0 && NN > best_n) {
            best_n = NN;
            save_best();
        }
    }

    if (bestN > minN) {
        printf("%d %d\n", bestN, bestM);
        for (int e = 0; e < bestM; e++) printf("%d %d\n", bestEu[e], bestEv[e]);
    } else {
        printf("0 0\n");
    }
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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group sampling for the Python fallback only.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


# ----------------------------------------------------------------------------
# Entry point.
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

    # Exact constructions.
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

    budget = max(2.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + budget

    # Main path: C annealing over bi-Cayley lifts, climbing above best_n.
    c_ok = False
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed) & 0xFFFFFFFF, f"{budget:.2f}", best_n],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
        c_ok = True
    except Exception:
        c_ok = False

    # Python fallback, used only if the C engine failed.
    if not c_ok:
        rng = random.Random(seed)
        while time.monotonic() < deadline:
            k = rng.choice([1, 2, 2, 3])
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            order, mul = g
            darts = []
            for _ in range(d):
                p = list(range(k))
                rng.shuffle(p)
                for i in range(k):
                    darts.append((i, k + p[i], rng.randrange(order)))
            n, e = lib.group_lift(2 * k, darts, order, mul)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
