"""Bi-Cayley (group voltage) lifts over metacyclic groups, searched by simulated annealing in C.

New in this version
- The search runs in a C engine (C_SOURCE). It anneals over voltage assignments on a
  d-regular "layered" base multigraph: k A-vertices and k B-vertices, with one perfect
  matching (a permutation) per layer. Each dart carries a voltage in a random metacyclic
  group Z_m x| Z_k2 (r^k2 = 1 mod m), so the lift has 2kG vertices.
- Diameter is checked on orbit representatives only. Left translation by any group element
  is an automorphism, so distances from the 2k representatives determine the diameter. Each
  move costs 2k BFS runs on 2kG vertices, which allows far more moves than a Python loop.
- Cost = (unreached (representative, vertex) pairs) + N * (number of duplicated darts).
  Zero cost means a valid simple bipartite graph with diameter <= D.
- A ladder: the target order is always above the best valid order found so far, so the
  engine keeps climbing while time remains.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXK2 64

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* ---------------- metacyclic group Z_m x| Z_k2, element (a,b) coded as a*k2+b ---------------- */

typedef struct {
    int G, m, k2;
    long long r;
    long long pw[MAXK2];   /* pw[b] = r^b mod m */
} Group;

static long long lmod(long long a, long long m) {
    a %= m;
    return a < 0 ? a + m : a;
}

static long long gcdll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b = lmod(b, m);
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void make_group(Group *g, int G, int k2, int m, long long r) {
    g->G = G;
    g->m = m;
    g->k2 = k2;
    g->r = r;
    g->pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) g->pw[b] = (g->pw[b - 1] * r) % m;
}

/* (a,b)*(c,e) = (a + r^b c, b + e) */
static int gmul(const Group *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    long long na = lmod((long long)a + g->pw[b] * (long long)c, g->m);
    int nb = (b + e) % g->k2;
    return (int)(na * g->k2 + nb);
}

/* (a,b)^-1 = (-r^(-b) a, -b) */
static int ginv(const Group *g, int x) {
    int a = x / g->k2, b = x % g->k2;
    int nb = (g->k2 - b) % g->k2;
    long long na = lmod(-g->pw[nb] * (long long)a, g->m);
    return (int)(na * g->k2 + nb);
}

static void random_group(Group *g, int G) {
    int cand[256];
    int nc = 0;
    for (int k2 = 1; k2 <= MAXK2 && k2 <= G; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    int k2 = cand[rndint(nc)];
    int m = G / k2;
    long long r = 1 % m;
    if (k2 > 1) {
        for (int t = 0; t < 300; t++) {
            long long c = 1 + rndint(m - 1);
            if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    make_group(g, G, k2, m, r);
}

/* ---------------- layered bi-Cayley lift ---------------- */
/* Vertices: A_{i,x} = i*G + x, B_{j,h} = (k+j)*G + h.
   Layer l is a permutation dj[l*k+i] of the B indices; dart (l,i) has voltage ds[l*k+i].
   Edge A_{i,x} -- B_{dj, x*ds}. Every vertex then has exactly d distinct neighbours
   when there are no duplicate darts. */

typedef struct {
    int k, d, G, N, stamp;
    Group grp;
    int *dj, *ds, *dsi;
    int *adj, *vis, *queue;
} Lift;

static void lift_alloc(Lift *L, int k, int d, int G) {
    L->k = k;
    L->d = d;
    L->G = G;
    L->N = 2 * k * G;
    L->stamp = 0;
    L->dj = malloc(sizeof(int) * (size_t)(k * d));
    L->ds = malloc(sizeof(int) * (size_t)(k * d));
    L->dsi = malloc(sizeof(int) * (size_t)(k * d));
    L->adj = malloc(sizeof(int) * (size_t)L->N * (size_t)d);
    L->vis = calloc((size_t)L->N, sizeof(int));
    L->queue = malloc(sizeof(int) * (size_t)L->N);
}

static void lift_free(Lift *L) {
    free(L->dj);
    free(L->ds);
    free(L->dsi);
    free(L->adj);
    free(L->vis);
    free(L->queue);
}

static void random_init(Lift *L) {
    int k = L->k, d = L->d;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            int idx = l * k + i;
            L->dj[idx] = perm[i];
            L->ds[idx] = rndint(L->G);
            L->dsi[idx] = ginv(&L->grp, L->ds[idx]);
        }
    }
}

static void build_adj(Lift *L) {
    int k = L->k, d = L->d, G = L->G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int idx = l * k + i;
            int j = L->dj[idx], s = L->ds[idx], si = L->dsi[idx];
            for (int x = 0; x < G; x++) {
                int a = i * G + x;
                L->adj[(size_t)a * d + l] = (k + j) * G + gmul(&L->grp, x, s);
                int b = (k + j) * G + x;
                L->adj[(size_t)b * d + l] = i * G + gmul(&L->grp, x, si);
            }
        }
    }
}

static int count_dups(const Lift *L) {
    int c = 0;
    for (int i = 0; i < L->k; i++)
        for (int l = 0; l < L->d; l++)
            for (int l2 = l + 1; l2 < L->d; l2++) {
                int a = l * L->k + i, b = l2 * L->k + i;
                if (L->dj[a] == L->dj[b] && L->ds[a] == L->ds[b]) c++;
            }
    return c;
}

/* Cost = unreached (representative, vertex) pairs + N per duplicate dart pair. */
static long long eval_cost(Lift *L, int D) {
    int k = L->k, d = L->d, G = L->G, N = L->N;
    long long cost = (long long)count_dups(L) * (long long)N;
    build_adj(L);
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        if (++L->stamp >= 0x7ffffff0) {
            memset(L->vis, 0, sizeof(int) * (size_t)N);
            L->stamp = 1;
        }
        int head = 0, tail = 0;
        L->queue[tail++] = src;
        L->vis[src] = L->stamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = L->queue[head++];
                const int *au = L->adj + (size_t)u * d;
                for (int t = 0; t < d; t++) {
                    int v = au[t];
                    if (L->vis[v] != L->stamp) {
                        L->vis[v] = L->stamp;
                        L->queue[tail++] = v;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

/* Simulated annealing. Returns 1 when a valid lift is reached (state left in L). */
static int anneal(Lift *L, int D, long long iters, double T0, double T1, double tend) {
    int k = L->k, d = L->d, G = L->G;
    long long cost = eval_cost(L, D);
    if (cost == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && cpu_now() > tend) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        long long c2;
        if (k >= 2 && rnd01() < 0.4) {
            /* swap the B-targets of two darts in the same layer */
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int a = l * k + i1, b = l * k + i2;
            int t = L->dj[a];
            L->dj[a] = L->dj[b];
            L->dj[b] = t;
            c2 = eval_cost(L, D);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = L->dj[a];
                L->dj[a] = L->dj[b];
                L->dj[b] = t;
            }
        } else {
            /* change one voltage */
            int idx = rndint(d * k);
            int os = L->ds[idx], osi = L->dsi[idx];
            int ns = rndint(G);
            if (ns == os) continue;
            L->ds[idx] = ns;
            L->dsi[idx] = ginv(&L->grp, ns);
            c2 = eval_cost(L, D);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                L->ds[idx] = os;
                L->dsi[idx] = osi;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    int c;
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();
    while ((c = getchar()) != EOF) {
    }

    if (d < 2 || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double tend = cpu_now() + budget;
    int best_n = 0, best_m = 0;
    int *best_e = NULL;

    while (cpu_now() < tend) {
        int k = 1 + rndint(4);
        int Gmin = best_n / (2 * k) + 1;
        if (Gmin < 2) Gmin = 2;
        int spread = Gmin / 12 + 2;
        int G = Gmin + rndint(spread);

        Lift L;
        lift_alloc(&L, k, d, G);
        random_group(&L.grp, G);
        random_init(&L);
        int ok = anneal(&L, D, 100000, 3.0, 0.15, tend);
        if (ok) {
            build_adj(&L);
            int cnt = k * G * d;
            int *e = malloc(sizeof(int) * 2 * (size_t)cnt);
            int m = 0;
            for (int i = 0; i < k; i++)
                for (int x = 0; x < G; x++)
                    for (int l = 0; l < d; l++) {
                        int a = i * G + x;
                        e[2 * m] = a;
                        e[2 * m + 1] = L.adj[(size_t)a * d + l];
                        m++;
                    }
            if (L.N > best_n) {
                free(best_e);
                best_e = e;
                best_n = L.N;
                best_m = m;
            } else {
                free(e);
            }
        }
        lift_free(&L);
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int t = 0; t < best_m; t++) printf("%d %d\n", best_e[2 * t], best_e[2 * t + 1]);
    free(best_e);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python baselines (kept from the parent, used as safe fallbacks).
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - t0 < 0.1 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search in C. Leave a margin for the compile step and Python overhead.
    budget = 0.82 * time_limit - (time.monotonic() - t0) - 1.0
    if d >= 2 and budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=None, timeout=0.9 * time_limit)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
