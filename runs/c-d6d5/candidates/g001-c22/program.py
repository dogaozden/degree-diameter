import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts with group Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h, with base sizes k, group order G.
# Layer l gives darts (i, p_l(i), s): A_i,g ~ B_{p_l(i)}, g*s. Each A_i and each B_j
# has degree d. Left multiplication is an automorphism, so diameter <= D holds iff a
# BFS of depth D from A_i,identity and B_j,identity covers all vertices.
#
# Moves: change one voltage, or swap two base targets inside one layer (keeps the
# degrees exact). The search grows the order: each success raises the target G.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 4
#define GK 64
#define BIGC 1000000000LL

typedef struct { int m, kk, r; int pw[GK]; } Grp;

typedef struct {
    int d, D, k, G, N, nd;
    Grp grp;
    int *di, *dj, *ds;
    int *adj, *cnt, *mark, *queue;
    int stamp;
} Ctx;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect product Z_m x| Z_kk, element a*kk+b, (a,b)*(c,d) = (a + r^b c, b+d). */
static inline int gmul(const Grp *g, int x, int y) {
    int a = x / g->kk, b = x % g->kk;
    int c = y / g->kk, dd = y % g->kk;
    long long t = ((long long)a + (long long)g->pw[b] * c) % g->m;
    return (int)t * g->kk + (b + dd) % g->kk;
}

static int setup_group(Grp *g, int G) {
    int divs[GK];
    int nd = 0;
    for (int k2 = 1; k2 <= GK && k2 <= G / 2; k2++)
        if (G % k2 == 0) divs[nd++] = k2;
    if (nd == 0) return 0;
    int k2 = divs[rndint(nd)];
    int m = G / k2;
    int *cand = malloc(sizeof(int) * (size_t)m);
    int nc = 0;
    for (int r = 1; r < m; r++)
        if (gcd_i(r, m) == 1 && powmod_ll(r, k2, m) == 1 % m) cand[nc++] = r;
    if (nc == 0) { free(cand); return 0; }
    int r = cand[rndint(nc)];
    free(cand);
    g->m = m;
    g->kk = k2;
    g->r = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        g->pw[b] = (int)p;
        p = p * r % m;
    }
    return 1;
}

static void ctx_init(Ctx *c, int d, int D, int k, const Grp *grp) {
    c->d = d;
    c->D = D;
    c->k = k;
    c->G = grp->m * grp->kk;
    c->N = 2 * k * c->G;
    c->nd = k * d;
    c->grp = *grp;
    c->di = malloc(sizeof(int) * (size_t)c->nd);
    c->dj = malloc(sizeof(int) * (size_t)c->nd);
    c->ds = malloc(sizeof(int) * (size_t)c->nd);
    c->adj = malloc(sizeof(int) * (size_t)c->N * (size_t)d);
    c->cnt = malloc(sizeof(int) * (size_t)c->N);
    c->mark = calloc((size_t)c->N, sizeof(int));
    c->queue = malloc(sizeof(int) * (size_t)c->N);
    c->stamp = 0;
    for (int layer = 0; layer < d; layer++) {
        int perm[KMAX];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            int t = layer * k + i;
            c->di[t] = i;
            c->dj[t] = perm[i];
            c->ds[t] = rndint(c->G);
        }
    }
}

static void ctx_free(Ctx *c) {
    free(c->di);
    free(c->dj);
    free(c->ds);
    free(c->adj);
    free(c->cnt);
    free(c->mark);
    free(c->queue);
}

/* Number of (representative, vertex) pairs not reached within D. Zero means valid. */
static long long cost_of(Ctx *c) {
    int d = c->d, k = c->k, G = c->G, N = c->N, nd = c->nd;
    for (int t = 0; t < nd; t++)
        for (int u = t + 1; u < nd; u++)
            if (c->di[t] == c->di[u] && c->dj[t] == c->dj[u] && c->ds[t] == c->ds[u])
                return BIGC;
    memset(c->cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < nd; t++) {
        int i = c->di[t], j = c->dj[t], s = c->ds[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + gmul(&c->grp, g, s);
            c->adj[(size_t)a * d + c->cnt[a]++] = b;
            c->adj[(size_t)b * d + c->cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int rr = 0; rr < 2 * k; rr++) {
        int src = (rr < k) ? rr * G : (k + (rr - k)) * G;
        c->stamp++;
        int head = 0, tail = 0;
        c->queue[tail++] = src;
        c->mark[src] = c->stamp;
        for (int lev = 0; lev < c->D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = c->queue[head++];
                for (int q = 0; q < d; q++) {
                    int v = c->adj[(size_t)u * d + q];
                    if (c->mark[v] != c->stamp) {
                        c->mark[v] = c->stamp;
                        c->queue[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long long anneal(Ctx *c, long long iters, double T0, double T1,
                        clock_t deadline, int *bdj, int *bds) {
    long long cur = cost_of(c);
    long long best = cur;
    memcpy(bdj, c->dj, sizeof(int) * (size_t)c->nd);
    memcpy(bds, c->ds, sizeof(int) * (size_t)c->nd);
    for (long long it = 0; it < iters && best > 0; it++) {
        if ((it & 127) == 0 && clock() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (c->k == 1 || rndint(2) == 0) {
            int t = rndint(c->nd);
            int old = c->ds[t];
            c->ds[t] = rndint(c->G);
            long long nc = cost_of(c);
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T))
                cur = nc;
            else
                c->ds[t] = old;
        } else {
            int layer = rndint(c->d);
            int i1 = rndint(c->k);
            int i2 = rndint(c->k - 1);
            if (i2 >= i1) i2++;
            int t1 = layer * c->k + i1, t2 = layer * c->k + i2;
            int tmp = c->dj[t1];
            c->dj[t1] = c->dj[t2];
            c->dj[t2] = tmp;
            long long nc = cost_of(c);
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                tmp = c->dj[t1];
                c->dj[t1] = c->dj[t2];
                c->dj[t2] = tmp;
            }
        }
        if (cur < best) {
            best = cur;
            memcpy(bdj, c->dj, sizeof(int) * (size_t)c->nd);
            memcpy(bds, c->ds, sizeof(int) * (size_t)c->nd);
        }
    }
    return best;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int base = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    clock_t deadline = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);

    int maxnd = KMAX * d;
    int *tdj = malloc(sizeof(int) * (size_t)maxnd);
    int *tds = malloc(sizeof(int) * (size_t)maxnd);
    int *bdj = malloc(sizeof(int) * (size_t)maxnd);
    int *bds = malloc(sizeof(int) * (size_t)maxnd);
    int found = 0, bk = 0;
    Grp bgrp;
    memset(&bgrp, 0, sizeof(bgrp));
    static const int ktab[10] = {1, 1, 1, 1, 2, 2, 2, 3, 3, 4};

    while (clock() < deadline) {
        int k = ktab[rndint(10)];
        int lo = base / (2 * k);
        int G = lo + 1 + rndint(lo / 8 + 3);
        if (G < 2) G = 2;
        Grp grp;
        if (!setup_group(&grp, G)) continue;
        Ctx c;
        ctx_init(&c, d, D, k, &grp);
        long long res = anneal(&c, 30000, 2.0, 0.05, deadline, tdj, tds);
        if (res == 0 && 2LL * k * c.G > base) {
            base = 2 * k * c.G;
            found = 1;
            bk = k;
            bgrp = grp;
            memcpy(bdj, tdj, sizeof(int) * (size_t)(k * d));
            memcpy(bds, tds, sizeof(int) * (size_t)(k * d));
        }
        ctx_free(&c);
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    Ctx c;
    ctx_init(&c, d, D, bk, &bgrp);
    memcpy(c.dj, bdj, sizeof(int) * (size_t)(bk * d));
    memcpy(c.ds, bds, sizeof(int) * (size_t)(bk * d));
    long long res = cost_of(&c);
    if (res != 0) {
        printf("0 0\n");
        return 0;
    }
    int Ak = bk * c.G;
    printf("%d %d\n", 2 * Ak, Ak * d);
    for (int a = 0; a < Ak; a++)
        for (int q = 0; q < d; q++)
            printf("%d %d\n", a, c.adj[(size_t)a * d + q]);
    ctx_free(&c);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (baselines).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to gain, return instantly.
    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = time_limit - (time.monotonic() - t0)
    cbudget = max(0.5, 0.7 * remaining - 1.0)
    timeout = max(1.0, 0.85 * remaining)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{cbudget:.2f}", best[0]],
                        stdin_graph=None, timeout=timeout)
        n, e = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
