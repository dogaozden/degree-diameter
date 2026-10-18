"""Bi-Cayley lift search over Z_m x| Z_k groups, run by a C annealer, with exact constructions for D = 3, 4."""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
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
# C engine: bi-Cayley lift over G = Z_m x| Z_k with b base vertices per side.
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (b+j)*G + h. Layer l is a permutation
# sig[l] of the base indices, with voltage sv[l][i]: A_{i,g} ~ B_{sig[l][i], g*s}.
# Left translation is an automorphism, so only the 2b block representatives
# (identity element of each block) need BFS. Cost = unreached pairs + dup penalty.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 10
#define MAXG 4096
#define MAXDEG 16
#define MAXV (2 * MAXB * MAXG)

static int d, D, b, m, kk, G, N;
static int rp[MAXG];
static int sig[MAXDEG][MAXB];
static int sv[MAXDEG][MAXB];
static int nb[MAXV * MAXDEG];
static int mark[MAXV];
static int queue_[MAXV];
static int curstamp = 0;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gmul(int x, int y) {
    int a = x / kk, bb = x % kk, c = y / kk, e = y % kk;
    return (int)(((long)a + (long)rp[bb] * c) % m) * kk + (bb + e) % kk;
}

static void set_layer_i(int l, int i) {
    int j = sig[l][i], s = sv[l][i];
    for (int x = 0; x < G; x++) {
        int a = i * G + x;
        int bv = (b + j) * G + gmul(x, s);
        nb[a * MAXDEG + l] = bv;
        nb[bv * MAXDEG + l] = a;
    }
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXB];
        for (int i = 0; i < b; i++) perm[i] = i;
        for (int i = b - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < b; i++) {
            sig[l][i] = perm[i];
            sv[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < b; i++) set_layer_i(l, i);
}

static long eval_cost(void) {
    long unre = 0;
    for (int rep = 0; rep < 2 * b; rep++) {
        int src = rep * G;
        curstamp++;
        int head = 0, tail = 0;
        queue_[tail++] = src;
        mark[src] = curstamp;
        for (int dep = 0; dep < D && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int v = queue_[head++];
                const int *row = &nb[v * MAXDEG];
                for (int l = 0; l < d; l++) {
                    int u = row[l];
                    if (mark[u] != curstamp) {
                        mark[u] = curstamp;
                        queue_[tail++] = u;
                    }
                }
            }
        }
        unre += N - tail;
    }
    return unre;
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < b; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (sig[l1][i] == sig[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static long cost_now(void) {
    return eval_cost() + (long)(4 * N) * dup_count();
}

static int anneal(long iters, double until) {
    long cost = cost_now();
    double c0 = cost > 1 ? (double)cost : 1.0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > until) return 0;
        double temp = 0.5 + 0.02 * c0 * (1.0 - (double)t / (double)iters);
        if (b >= 2 && rnd01() < 0.4) {
            int l = rndint(d), i1 = rndint(b), i2 = rndint(b - 1);
            if (i2 >= i1) i2++;
            int tmp = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = tmp;
            set_layer_i(l, i1);
            set_layer_i(l, i2);
            long c2 = cost_now();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
            } else {
                tmp = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = tmp;
                set_layer_i(l, i1);
                set_layer_i(l, i2);
            }
        } else {
            int l = rndint(d), i = rndint(b);
            int old = sv[l][i], nw = rndint(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            set_layer_i(l, i);
            long c2 = cost_now();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
            } else {
                sv[l][i] = old;
                set_layer_i(l, i);
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D m k r b seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    m = atoi(argv[3]);
    kk = atoi(argv[4]);
    int r = atoi(argv[5]);
    b = atoi(argv[6]);
    long seed = atol(argv[7]);
    double limit = atof(argv[8]);

    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || b < 1 || b > MAXB || m < 2 || kk < 1) {
        printf("0 0\n");
        return 0;
    }
    G = m * kk;
    if (G > MAXG) { printf("0 0\n"); return 0; }
    N = 2 * b * G;
    if (N > MAXV) { printf("0 0\n"); return 0; }
    if (D < 2) { printf("0 0\n"); return 0; }

    rp[0] = 1 % m;
    for (int t = 1; t < kk; t++) rp[t] = (int)((long)rp[t - 1] * (r % m) % m);
    if (kk > 1 && (long)rp[kk - 1] * (r % m) % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }

    long iters = 30000;
    int found = 0;
    while (now() < t_end) {
        random_init();
        if (anneal(iters, t_end)) {
            found = 1;
            break;
        }
    }
    if (!found) {
        printf("0 0\n");
        return 0;
    }
    long M = (long)b * G * d;
    printf("%d %ld\n", N, M);
    for (int v = 0; v < b * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[v * MAXDEG + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python driver.
# ----------------------------------------------------------------------------

MAXB = 10


def _group_options(lo, hi, rng, maxb):
    """Shuffled list of (b, m, k, r) with lo <= 2*b*m*k <= hi and r^k = 1 mod m."""
    out = []
    g_lo = max(2, -(-lo // (2 * maxb)))
    for G in range(g_lo, hi // 2 + 1):
        bs = [b for b in range(1, maxb + 1) if lo <= 2 * b * G <= hi]
        if not bs:
            continue
        for k in range(1, G + 1):
            if G % k:
                continue
            m = G // k
            if m < 2:
                continue
            if k == 1:
                rlist = [1]
            else:
                rlist = [1]
                if m == 2:
                    rlist = [1]
                else:
                    for _ in range(30):
                        r = rng.randrange(2, m)
                        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                            rlist.append(r)
            for r in set(rlist[:3]):
                for b in bs:
                    out.append((b, m, k, r))
    rng.shuffle(out)
    return out


def _lift_search(best, d, D, rng, end):
    """Repeatedly ask the C annealer for a valid lift just above the current best order."""
    moore = lib.moore_bound(d, D)
    fails = 0
    while True:
        left = end - time.monotonic()
        if left < 2.0 or fails > 60:
            break
        lo = best[0] + 2
        if lo > moore:
            break
        hi = min(moore, int(lo * (1.03 + 0.02 * fails)) + 2)
        opts = _group_options(lo, hi, rng, MAXB)
        if not opts:
            fails += 1
            continue
        b, m, k, r = opts[0]
        slice_ = min(left - 1.0, 6.0)
        if slice_ < 1.0:
            break
        try:
            text = lib.run_c(C_SOURCE, [d, D, m, k, r, b, rng.randrange(1 << 30), round(slice_, 2)],
                             timeout=slice_ + 6)
            n, e = lib.parse_graph_text(text)
        except (RuntimeError, ValueError):
            fails += 1
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            fails = 0
        else:
            fails += 1
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search over Z_m x| Z_k with up to MAXB base vertices per side.
    if D >= 2 and d <= 16:
        try:
            best = _lift_search(best, d, D, rng, end)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
