"""Bold variant: bi-Cayley voltage-lift annealing in C over semidirect groups Z_m x| Z_k2,
with k base vertices per side. Each layer is a block permutation plus voltages, and a
bitmask BFS from the 2k block representatives scores each candidate. The exact PG/GQ/Araujo
constructions and the K_{d,d} fallback remain as safe baselines."""
import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: block-voltage lifts over semidirect groups, annealed with bitmask
# reachability from block representatives (valid by left-translation symmetry).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search: bi-Cayley lift annealing.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXK 8
#define MAXW (MAXN / 64)
#define PEN 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (bitset BFS). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

/* ---- Semidirect group Z_m x| Z_k2, element (a,b) = a*k2+b,
 *      (a,b)(c,e) = (a + r^b c mod m, b+e mod k2), requires r^k2 = 1 mod m. ---- */
typedef struct {
    int m, k2, r;
    int rp[MAXN];
} Grp;

static Grp Gr;
static int Gord;           /* group order = block size */
static int Kb;             /* base vertices per side */
static int invt[MAXN];

static int gmul(int x, int y) {
    int k2 = Gr.k2, m = Gr.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    return (int)(((long)a + (long)Gr.rp[b] * c) % m) * k2 + (b + e) % k2;
}

/* Uniformly random (m, r) with m*k2 = G among all valid semidirect structures. */
static void random_group(int G) {
    long cnt = 0;
    int bm = 1, bk = G, br = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        for (int r = 0; r < m; r++) {
            if (m > 1 && (r == 0 || gcd(r, m) != 1)) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    Gr.m = bm;
    Gr.k2 = bk;
    Gr.r = br;
    Gr.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) Gr.rp[b] = (int)((long)Gr.rp[b - 1] * br % bm);
    Gord = G;
    for (int x = 0; x < G; x++) {
        int a = x / bk, b = x % bk;
        int nb = (bk - b) % bk;
        long t = (long)Gr.rp[nb] * a % bm;
        int na = (int)((bm - t) % bm);
        invt[x] = na * bk + nb;
    }
}

/* ---- Lift state: layer l maps A-block i to B-block perm[l][i] with voltage volt[l][i].
 *      A_{i,g} ~ B_{p, g*s};  B_{p,h} ~ A_{i, h*s^-1}. ---- */
static int perm[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t mA[MAXN], mB[MAXN];

static void fill_layer(int l) {
    int k = Kb, G = Gord;
    for (int i = 0; i < k; i++) {
        int p = perm[l][i], s = volt[l][i], si = invt[s];
        for (int g = 0; g < G; g++) {
            nbr[l][i * G + g] = (k + p) * G + gmul(g, s);
            nbr[l][(k + p) * G + g] = i * G + gmul(g, si);
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < Kb; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && volt[l1][i] == volt[l2][i]) c++;
    return c;
}

/* Sum over vertices of the number of block representatives NOT within distance D.
 * By left-translation symmetry this is zero iff the lift has diameter <= D. */
static long lift_cost(void) {
    int k = Kb, G = Gord, N = 2 * k * G;
    uint64_t *cur = mA, *nxt = mB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long miss = 0;
    for (int v = 0; v < N; v++) miss += 2 * k - __builtin_popcountll(cur[v]);
    return miss;
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        int pr[MAXK];
        for (int i = 0; i < Kb; i++) pr[i] = i;
        for (int i = Kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pr[i]; pr[i] = pr[j]; pr[j] = t;
        }
        for (int i = 0; i < Kb; i++) {
            perm[l][i] = pr[i];
            volt[l][i] = rndint(Gord);
        }
    }
}

/* Simulated annealing on the current group. Returns 1 if a valid lift was reached. */
static int anneal(long maxit, long patience, double until) {
    random_lift();
    for (int l = 0; l < d; l++) fill_layer(l);
    long cost = lift_cost() + PEN * dupcount();
    long best_cost = cost, last = 0;
    for (long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 255) == 0 && now() > until) break;
        if (it - last > patience) break;
        double T = 4.0 * (1.0 - (double)it / (double)maxit) + 0.05;
        int l = rndint(d), i = rndint(Kb);
        int oldp = perm[l][i], oldv = volt[l][i];
        int j = -1, oldpj = 0, oldvj = 0;
        if (Kb >= 2 && rnd01() < 0.3) {
            j = rndint(Kb - 1);
            if (j >= i) j++;
            oldpj = perm[l][j];
            oldvj = volt[l][j];
            perm[l][i] = oldpj;
            perm[l][j] = oldp;
        } else {
            volt[l][i] = rndint(Gord);
        }
        fill_layer(l);
        long nc = lift_cost() + PEN * dupcount();
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
            cost = nc;
            if (cost < best_cost) { best_cost = cost; last = it; }
        } else {
            perm[l][i] = oldp;
            volt[l][i] = oldv;
            if (j >= 0) { perm[l][j] = oldpj; volt[l][j] = oldvj; }
            fill_layer(l);
        }
    }
    return cost == 0;
}

static void graph_from_lift(Graph *g) {
    int k = Kb, G = Gord, N = 2 * k * G;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= k * G; }
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++) add_edge(g, u, nbr[l][u]);
}

static int pick_k(void) { return 1 + rndint(MAXK); }

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    static Graph best, cand;
    if (d < 1 || D < 1 || d > MAXD || 2 * d > MAXN) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    while (D >= 2 && now() < t_end && best.n < moore) {
        int k = pick_k();
        int G = best.n / (2 * k) + 1 + rndint(3);
        if (G < 2) G = 2;
        if (2L * k * G > moore || 2L * k * G > MAXN) continue;
        random_group(G);
        Kb = k;
        if (anneal(60000, 15000, t_end)) {
            graph_from_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
        }
    }

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the current best if (n, e) is a larger valid graph."""
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

    # Bold search phase: one C run doing bi-Cayley voltage-lift annealing.
    if D >= 2 and time.monotonic() < end - 1.0:
        budget = end - time.monotonic() - 0.5
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
