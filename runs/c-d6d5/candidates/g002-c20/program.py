"""Bi-lift annealing with an upward ladder, replacing the parent's random-restart lift search.

Changes from the parent (g001-c30):
- The C engine works on implicit bi-Cayley / bi-lift graphs over semidirect groups Z_m x| Z_k.
  Vertices are A_i(g) and B_j(x) for base size k in {1,2,3}. Neighbours are computed from
  a precomputed multiplication table, so no adjacency lists are stored during search.
- Diameter is checked exactly with 2k BFS runs from representatives, because left
  multiplication is an automorphism. Duplicate darts are penalised.
- The search climbs a ladder: it always targets a graph order just above the current best,
  across k = 1, 2, 3 and random groups, and keeps only explicitly verified graphs.
- Any failure falls back to the best valid graph found so far, which starts from the
  Python constructions (W(q), PG(2,q), Araujo-Lopez, K_{d,d}).
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

#define MAXV 4096
#define MAXW (MAXV / 64)
#define MAXDEG 32
#define MAXG 1024
#define MAXK 3
#define MAXL 32
#define PEN 30L

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXDEG];
    unsigned char side[MAXV];
} Graph;

static int d, D;
static double t_end;
static Graph best, cand;
static uint64_t RA[MAXV * MAXW], RB[MAXV * MAXW];

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
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
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
static void swap_int(int *a, int *b) { int t = *a; *a = *b; *b = t; }

/* ------------------------------------------------------------ explicit graphs */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void complete_bip(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Exact check: simple, bipartite, max degree <= d, every pair within distance D. */
static int diam_ok(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        if (c != n) return 0;
    }
    return 1;
}

static int verify(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXV) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
            int back = 0;
            for (int k = 0; k < g->deg[u]; k++)
                if (g->adj[u][k] == v) back = 1;
            if (!back) return 0;
        }
    }
    return diam_ok(g);
}

static int read_graph(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXV || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= MAXDEG || g->deg[v] >= MAXDEG) return 0;
        add_edge(g, u, v);
    }
    static int qu[MAXV];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        qu[tail++] = s;
        while (head < tail) {
            int v = qu[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    qu[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    return 0;
                }
            }
        }
    }
    return verify(g);
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

/* ------------------------------------------------------------ groups */

/* Z_GM x| Z_GK, element a*GK + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int GM = 1, GK = 1, GG = 1;
static int rp[MAXG];
static int MTab[MAXG * MAXG];
static int INV[MAXG];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < GG; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GG; y++) {
            int c = y / k, e = y % k;
            int za = (int)(((long)a + (long)rp[b] * c) % m);
            MTab[x * GG + y] = za * k + (b + e) % k;
        }
    }
    for (int x = 0; x < GG; x++)
        for (int y = 0; y < GG; y++)
            if (MTab[x * GG + y] == 0) { INV[x] = y; break; }
}

/* Uniform random valid (m, k, r) with m*k = G, gcd(r,m)=1, r^k = 1 mod m. */
static void pick_group(int G, int *pm, int *pk, int *pr) {
    int count = 0, bm = 1, bk = G, br = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k = G / m;
        if (m == 1) {
            count++;
            if (rndint(count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint(count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    *pm = bm;
    *pk = bk;
    *pr = br;
}

/* ------------------------------------------------------------ bi-lift search */

/* Base: BK A-vertices and BK B-vertices. Layer t has permutation perm[t] (A_i -> B_perm[t][i])
 * and voltages vol[t][i]: dart joins A_i(g) to B_j(g * vol). Each A and each B has degree NL. */
static int BK = 1, NL = 1;
static int perm[MAXL][MAXK], vol[MAXL][MAXK], binv[MAXL][MAXK];
static int bperm[MAXL][MAXK], bvol[MAXL][MAXK];
static int lvis[MAXV], lq[MAXV];
static int stampc = 0;

static int reach_count(int src) {
    if (++stampc == 0x7fffffff) { memset(lvis, 0, sizeof lvis); stampc = 1; }
    int head = 0, tail = 0;
    int AN = BK * GG;
    lvis[src] = stampc;
    lq[tail++] = src;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = lq[head++];
            if (v < AN) {
                int i = v / GG, g = v - i * GG;
                for (int t = 0; t < NL; t++) {
                    int w = (BK + perm[t][i]) * GG + MTab[g * GG + vol[t][i]];
                    if (lvis[w] != stampc) { lvis[w] = stampc; lq[tail++] = w; }
                }
            } else {
                int u = v - AN;
                int j = u / GG, x = u - j * GG;
                for (int t = 0; t < NL; t++) {
                    int i = binv[t][j];
                    int w = i * GG + MTab[x * GG + INV[vol[t][i]]];
                    if (lvis[w] != stampc) { lvis[w] = stampc; lq[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (representative, vertex) pairs plus a penalty for duplicate darts. 0 = valid lift. */
static long lift_cost(void) {
    long pen = 0;
    for (int t = 0; t < NL; t++)
        for (int i = 0; i < BK; i++)
            for (int t2 = t + 1; t2 < NL; t2++)
                if (perm[t][i] == perm[t2][i] && vol[t][i] == vol[t2][i]) pen++;
    for (int t = 0; t < NL; t++)
        for (int i = 0; i < BK; i++) binv[t][perm[t][i]] = i;
    int N = 2 * BK * GG;
    long total = 0;
    for (int r = 0; r < 2 * BK; r++) total += N - reach_count(r * GG);
    return total + PEN * pen;
}

static void random_state(void) {
    for (int t = 0; t < NL; t++) {
        for (int i = 0; i < BK; i++) perm[t][i] = i;
        for (int i = BK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            swap_int(&perm[t][i], &perm[t][j]);
        }
        for (int i = 0; i < BK; i++) vol[t][i] = rndint(GG);
    }
}

static void save_state(void) {
    memcpy(bperm, perm, sizeof perm);
    memcpy(bvol, vol, sizeof vol);
}
static void restore_state(void) {
    memcpy(perm, bperm, sizeof perm);
    memcpy(vol, bvol, sizeof vol);
}

/* Simulated annealing from a random state. Returns 1 with the zero-cost state restored. */
static int anneal(int iters, double deadline) {
    random_state();
    long cost = lift_cost();
    long bestc = cost;
    save_state();
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 127) == 0 && now() > deadline) break;
        double T = 2.0 * (1.0 - (double)it / iters) + 0.15;
        int t = rndint(NL), i = rndint(BK);
        if (BK > 1 && rndint(4) == 0) {
            int i2 = rndint(BK);
            if (i2 == i) continue;
            swap_int(&perm[t][i], &perm[t][i2]);
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else swap_int(&perm[t][i], &perm[t][i2]);
        } else {
            int old = vol[t][i];
            int nv = rndint(GG);
            if (nv == old) continue;
            vol[t][i] = nv;
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else vol[t][i] = old;
        }
        if (cost < bestc) { bestc = cost; save_state(); }
    }
    if (bestc == 0) {
        restore_state();
        return 1;
    }
    return 0;
}

static void build_explicit(Graph *g) {
    int AN = BK * GG, N = 2 * AN;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= AN); }
    for (int t = 0; t < NL; t++)
        for (int i = 0; i < BK; i++) {
            int j = perm[t][i];
            for (int x = 0; x < GG; x++) {
                int a = i * GG + x;
                int b = (BK + j) * GG + MTab[x * GG + vol[t][i]];
                add_edge(g, a, b);
            }
        }
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || D < 1 || d > MAXDEG) {
        printf("1 0\n");
        return 0;
    }
    if (D == 1) {
        printf("2 1\n0 1\n");
        return 0;
    }

    if (!read_graph(&best)) complete_bip(&best);
    if (!verify(&best)) complete_bip(&best);

    if (d >= 3 && D >= 2) {
        long moore = moore_bound();
        while (now() < t_end) {
            int bestN = best.n;
            int r = rndint(10);
            int k = r < 5 ? 1 : (r < 8 ? 2 : 3);
            long G = bestN / (2L * k) + 1;
            if (rndint(3) == 0) G += rndint(3);
            if (G < d) G = d;
            if (2L * k * G > moore || 2L * k * G > MAXV || G > MAXG) {
                k = 1;
                G = bestN / 2 + 1;
                if (G < d) G = d;
                if (2L * G > moore || 2L * G > MAXV || G > MAXG || 2L * G <= bestN) break;
            }
            int gm, gk, gr;
            pick_group((int)G, &gm, &gk, &gr);
            set_group(gm, gk, gr);
            BK = k;
            NL = d;
            double dl = now() + 6.0;
            if (dl > t_end) dl = t_end;
            if (anneal(80000, dl)) {
                build_explicit(&cand);
                if (cand.n > best.n && verify(&cand)) best = cand;
            }
        }
    }
    print_graph(&best);
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _cycle(n):
    return n, [(i, (i + 1) % n) for i in range(n)]


def _candidates(d, D):
    """Algebraic starting graphs for (d, D); each is checked with lib.is_valid later."""
    out = [lib.haar_graph(d, range(d))]          # K_{d,d}: valid for D >= 2
    if d == 2:
        out.append(_cycle(2 * D))                # Moore graph for d = 2
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            out.append(pg)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            out.append(gq)
    return out


def _best_valid(cands, d, D):
    best = None
    for n, e in cands:
        if (best is None or n > best[0]) and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    best = _best_valid(_candidates(d, D), d, D)
    if best is None:
        best = lib.haar_graph(d, range(d))

    moore = lib.moore_bound(d, D)
    if d < 3 or D < 2 or best[0] >= moore:
        return best

    remaining = time_limit * 0.9 - (time.monotonic() - t0) - 3.0
    if remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass
    return best
