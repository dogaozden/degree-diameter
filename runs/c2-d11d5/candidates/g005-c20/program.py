"""Bi-Cayley voltage search over metacyclic groups, with exact fallbacks.

For D >= 3 the search side is a bi-Cayley graph over a group G of order about n/2:
A_g ~ B_{g*s} for s in a connection set S of size d. Left multiplication is an
automorphism, so diameter <= D only needs BFS from A_1 and B_1. A C engine anneals S
over groups Z_m x|_r Z_k, ratcheting the order upward. Every result is checked with
lib.is_valid, and K_{d,d}, cycles, or exact constructions are the fallbacks.
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

#define MAXG 12000
#define MAXS 32

static int d, D, G;
static int gm, gk, gr;
static int pw[64];
static int S[MAXS];
static int Rt[MAXS][MAXG];
static int Lt[MAXS][MAXG];
static int saveR[MAXG], saveL[MAXG];
static int bestS[MAXS];
static int bestm, bestk, bestr, bestG;
static int vis[2 * MAXG];
static int qu[2 * MAXG];
static int stamp_ctr = 0;
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
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static long lgcd(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long lpowmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bd(int dd, int DD) {
    long s = 0, p = 1;
    for (int i = 0; i < DD; i++) {
        s += p;
        p *= (dd - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void set_group(int m, int k, int r) {
    gm = m;
    gk = k;
    gr = r;
    G = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    long ra = ((long)a + (long)pw[b] * c) % gm;
    return (int)(ra * gk + (b + e) % gk);
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    long t = ((long)pw[nb] * a) % gm;
    long na = (gm - t) % gm;
    return (int)(na * gk + nb);
}

static void set_elem(int j, int t) {
    S[j] = t;
    int ti = ginv(t);
    for (int g = 0; g < G; g++) {
        Rt[j][g] = gmul(g, t);
        Lt[j][g] = gmul(g, ti);
    }
}

/* Number of vertices within distance D of src (src is A-side if src < G, else B-side). */
static int reach(int src) {
    int st = ++stamp_ctr;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = st;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int lim = tail;
        while (head < lim) {
            int v = qu[head++];
            if (v < G) {
                for (int j = 0; j < d; j++) {
                    int u = G + Rt[j][v];
                    if (vis[u] != st) { vis[u] = st; qu[tail++] = u; }
                }
            } else {
                int h = v - G;
                for (int j = 0; j < d; j++) {
                    int u = Lt[j][h];
                    if (vis[u] != st) { vis[u] = st; qu[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static int eval_cost(void) {
    return (2 * G - reach(0)) + (2 * G - reach(G));
}

static int pick_k(void) {
    static const int ks[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    return ks[rndi(11)];
}

static int make_group(int goal, int k) {
    int m = (goal + k - 1) / k;
    if (m < 3) m = 3;
    if (k == 1) {
        set_group(m, 1, 1);
        return 1;
    }
    for (int tries = 0; tries < 400; tries++) {
        int r = rnd01() < 0.15 ? 1 : 1 + rndi(m - 1);
        if (lgcd(r, m) != 1) continue;
        if (lpowmod(r, k, m) != 1 % m) continue;
        set_group(m, k, r);
        return 1;
    }
    return 0;
}

static int anneal(double until) {
    for (int j = 0; j < d; j++) {
        int t, ok;
        do {
            t = rndi(G);
            ok = 1;
            for (int i = 0; i < j; i++) if (S[i] == t) ok = 0;
        } while (!ok);
        set_elem(j, t);
    }
    int cost = eval_cost();
    if (cost == 0) return 1;
    double Tb = 1.0 + 0.02 * cost;
    long it = 0;
    while (cost > 0) {
        if ((it & 255) == 0 && now() > until) return 0;
        it++;
        int j = rndi(d);
        int t = rndi(G);
        int dup = 0;
        for (int i = 0; i < d; i++) if (S[i] == t) { dup = 1; break; }
        if (dup) continue;
        int old = S[j];
        memcpy(saveR, Rt[j], sizeof(int) * G);
        memcpy(saveL, Lt[j], sizeof(int) * G);
        set_elem(j, t);
        int nc = eval_cost();
        double T = Tb * (1.0 - (double)(it % 30000) / 30000.0) + 0.3;
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
            cost = nc;
        } else {
            S[j] = old;
            memcpy(Rt[j], saveR, sizeof(int) * G);
            memcpy(Lt[j], saveL, sizeof(int) * G);
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int startG = argc > 5 ? atoi(argv[5]) : 0;
    double tend = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 3 || d > MAXS || D < 3) {
        printf("0 0\n");
        return 0;
    }
    long mb = moore_bd(d, D);
    long capl = mb / 2;
    int cap = capl > MAXG ? MAXG : (int)capl;

    int curBest = startG;
    int found = 0;
    int goal = startG + 1;
    if (goal < d + 1) goal = d + 1;

    while (now() < tend - 0.5 && goal <= cap) {
        double left = tend - now() - 0.3;
        double slice = left < 5.0 ? left : (left / 4.0 > 5.0 ? left / 4.0 : 5.0);
        int k = pick_k();
        if (!make_group(goal, k)) continue;
        if (G > cap || G <= d) continue;
        if (anneal(now() + slice)) {
            found = 1;
            curBest = G;
            bestm = gm;
            bestk = gk;
            bestr = gr;
            bestG = G;
            memcpy(bestS, S, sizeof(int) * d);
            goal = G + 1;
        } else {
            int base = curBest + 1;
            goal = base + (goal - base) / 2;
            if (goal < base) goal = base;
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestm, bestk, bestr);
    for (int j = 0; j < d; j++) set_elem(j, bestS[j]);
    printf("%d %ld\n", 2 * G, (long)G * d);
    for (int g = 0; g < G; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, G + Rt[j][g]);
    return 0;
}
'''


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = (n, [(i, (i + 1) % n) for i in range(n)])
        if lib.is_valid(cyc[0], cyc[1], d, D):
            return cyc
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Main search: bi-Cayley annealing in C, starting above the current best order.
    if D >= 3:
        total = max(1.0, 0.85 * time_limit - 2.0)
        deadline = t0 + total
        remaining = deadline - time.monotonic()
        if remaining > 3.0:
            budget = round(remaining - 1.0, 2)
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, budget, best_n // 2],
                                 timeout=budget + 15)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
