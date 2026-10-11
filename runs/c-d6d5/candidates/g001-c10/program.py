import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealed voltage lifts over semidirect products Z_m x| Z_k2.
#
# Base graph: k A-vertices and k B-vertices, with d "layers". Layer L is a
# permutation of the k B-vertices, so each A_i has d darts and each B_j gets d.
# Dart x = (layer L, source i) carries a target j and a voltage s in G.
# Edges: A_{i,h} ~ B_{j,h*s} for all h in G.
#
# Left multiplication is an automorphism, so the graph has diameter <= D iff a
# BFS of depth D from each of the 2k representatives A_{i,0}, B_{j,0} reaches
# every vertex. Cost = total unreached (representative, vertex) pairs, plus a
# penalty for duplicate darts.
#
# Moves: change one voltage, or swap two target vertices inside one layer
# (this changes the base graph itself). Simulated annealing with restarts.
# Each restart targets a group order strictly above the best found so far, and
# the best valid graph is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 4
#define MAXV 20000
#define MAXEDGE 200000
#define DUP_PEN 1000
#define ITERS 20000

typedef struct { int m, k2, G; int pw[16]; } Grp;
typedef struct { int d, D, k, G, nd; int dj[MAXD*MAXK]; int ds[MAXD*MAXK]; } Cfg;

static uint64_t rs = 88172645463325252ULL;
static int adjv[MAXV][MAXD];
static int adjc[MAXV];
static int seen[MAXV];
static int qbuf[MAXV];
static int stamp = 0;
static int eu[MAXEDGE], ev[MAXEDGE];
static int best_n = 0, best_m = 0;
static int have = 0;
static int g_d, g_D;
static double t_stop;

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static int gmul(const Grp *gr, int x, int y) {
    int a = x / gr->k2, b = x % gr->k2;
    int c = y / gr->k2, e = y % gr->k2;
    int na = (int)(((long long)a + (long long)gr->pw[b] * c) % gr->m);
    int nb = (b + e) % gr->k2;
    return na * gr->k2 + nb;
}

/* Random semidirect product of order G: element (a,b) coded a*k2+b,
   (a,b)(c,e) = (a + r^b c, b + e), valid when r^k2 = 1 mod m, gcd(r,m)=1. */
static void make_group(Grp *gr, int G) {
    int cand[16], nc = 0;
    for (int k2 = 2; k2 <= 12; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    int k2 = 1;
    if (nc > 0 && rndint(4) != 0) k2 = cand[rndint(nc)];
    int m = G / k2;
    int r = 1;
    if (k2 > 1 && m > 2) {
        for (int tries = 0; tries < 300; tries++) {
            int cr = 1 + rndint(m - 1);
            if (gcd_i(cr, m) == 1 && powmod(cr, k2, m) == 1 % m) { r = cr; break; }
        }
    }
    gr->m = m; gr->k2 = k2; gr->G = G;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        gr->pw[b] = (int)p;
        p = p * r % m;
    }
}

/* Cost = duplicate penalty, or the number of unreached (rep, vertex) pairs. */
static long eval_cost(const Grp *gr, const Cfg *c) {
    int k = c->k, G = gr->G, nd = c->nd;
    long dup = 0;
    for (int x = 0; x < nd; x++)
        for (int y = x + 1; y < nd; y++)
            if (x % k == y % k && c->dj[x] == c->dj[y] && c->ds[x] == c->ds[y]) dup++;
    if (dup > 0) return DUP_PEN * dup;

    int N = 2 * k * G;
    for (int v = 0; v < N; v++) adjc[v] = 0;
    for (int x = 0; x < nd; x++) {
        int i = x % k, j = c->dj[x], s = c->ds[x];
        for (int h = 0; h < G; h++) {
            int a = i * G + h;
            int b = (k + j) * G + gmul(gr, h, s);
            adjv[a][adjc[a]++] = b;
            adjv[b][adjc[b]++] = a;
        }
    }

    long unreached = 0;
    int nr = 0, reps[2 * MAXK];
    for (int i = 0; i < k; i++) reps[nr++] = i * G;
    for (int j = 0; j < k; j++) reps[nr++] = (k + j) * G;
    for (int r = 0; r < nr; r++) {
        if (stamp > 2000000000) { memset(seen, 0, sizeof(seen)); stamp = 0; }
        ++stamp;
        int src = reps[r];
        int head = 0, tail = 0;
        qbuf[tail++] = src;
        seen[src] = stamp;
        int dep = 0;
        while (head < tail && dep < c->D) {
            int end = tail;
            while (head < end) {
                int u = qbuf[head++];
                for (int t = 0; t < adjc[u]; t++) {
                    int v = adjv[u][t];
                    if (seen[v] != stamp) { seen[v] = stamp; qbuf[tail++] = v; }
                }
            }
            dep++;
        }
        unreached += N - tail;
    }
    return unreached;
}

static int anneal(const Grp *gr, Cfg *c, long iters) {
    int k = c->k, d = c->d, nd = c->nd, G = gr->G;
    int perm[MAXK];
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[r]; perm[r] = t;
        }
        for (int i = 0; i < k; i++) c->dj[L * k + i] = perm[i];
    }
    for (int x = 0; x < nd; x++) c->ds[x] = rndint(G);

    long cur = eval_cost(gr, c);
    for (long t = 0; t < iters; t++) {
        if (cur == 0) return 1;
        if ((t & 127) == 0 && now() > t_stop) break;
        double T = 2.0 * (1.0 - (double)t / (double)iters) + 0.05;
        if (k > 1 && rnd01() < 0.35) {
            int L = rndint(d), i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int x1 = L * k + i1, x2 = L * k + i2;
            int tmp = c->dj[x1]; c->dj[x1] = c->dj[x2]; c->dj[x2] = tmp;
            long nc = eval_cost(gr, c);
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                tmp = c->dj[x1]; c->dj[x1] = c->dj[x2]; c->dj[x2] = tmp;
            }
        } else {
            int x = rndint(nd);
            int old = c->ds[x];
            c->ds[x] = rndint(G);
            long nc = eval_cost(gr, c);
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                c->ds[x] = old;
            }
        }
    }
    return cur == 0;
}

static void record(const Grp *gr, const Cfg *c) {
    int k = c->k, G = gr->G, m = 0;
    for (int x = 0; x < c->nd; x++) {
        int i = x % k, j = c->dj[x], s = c->ds[x];
        for (int h = 0; h < G; h++) {
            if (m >= MAXEDGE) return;
            eu[m] = i * G + h;
            ev[m] = (k + j) * G + gmul(gr, h, s);
            m++;
        }
    }
    best_m = m;
    best_n = 2 * k * G;
    have = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed time [min_n]\n"); return 1; }
    g_d = atoi(argv[1]);
    g_D = atoi(argv[2]);
    long long seed = atoll(argv[3]);
    double tl = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    if (g_d < 1 || g_d > MAXD || g_D < 1) { printf("0 0\n"); return 0; }

    rs = ((uint64_t)seed * 0x9E3779B97F4A7C15ULL) ^ 0x1234567ULL;
    if (rs == 0) rs = 1;
    best_n = min_n;
    t_stop = now() + tl;

    while (now() < t_stop) {
        int k = 1 + rndint(3);
        int Gmin = best_n / (2 * k) + 1;
        if (Gmin < 2) Gmin = 2;
        int G = Gmin + rndint(Gmin / 10 + 3);
        if (2 * k * G > MAXV) continue;
        Grp gr;
        make_group(&gr, G);
        Cfg c;
        c.d = g_d; c.D = g_D; c.k = k; c.G = G; c.nd = g_d * k;
        if (anneal(&gr, &c, ITERS)) record(&gr, &c);
    }

    if (!have) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", eu[e], ev[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
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


def _baseline(d, D):
    """Simple always-valid graph: K2, a cycle, or K_{d,d}."""
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    best = _baseline(d, D)

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d >= 3 and D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
    if d >= 3 and D >= 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Calibration: the Moore bound is reached, so nothing can beat it.
    if D == 3 and best[0] >= lib.moore_bound(d, D):
        return best

    if d >= 3 and D >= 3 and d <= 16:
        elapsed = time.monotonic() - start
        remaining = time_limit - elapsed
        budget = max(1.0, 0.7 * remaining - 0.5)
        timeout = max(2.0, 0.9 * remaining)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]], timeout=timeout)
            n, e = lib.parse_graph_text(out)
            consider((n, e))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _baseline(d, D)
    return best
