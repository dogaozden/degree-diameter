"""Bi-Cayley search program. Python builds the best algebraic start (PG(2,q), W(q),
Araujo-Pardo-Lopez, or K_{d,d}) and checks it with lib.is_valid. The C engine then searches a
different family from that start: bi-Cayley graphs over every semidirect product Z_m x|_r Z_k of
order N, with connection set S of size d.

Why this family: a bi-Cayley graph has A_x ~ B_{xs} for s in S. Left multiplication acts
transitively on each side, so diameter <= D only needs two BFS runs (from A_e and B_e). That makes
exhaustive search over S cheap for N around 80-120. Groups and connection sets are enumerated, not
hill-climbed, and the largest valid order found is returned.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search over semidirect products Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit [min_vertices]   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found (or the start graph).
 *
 * Vertices: A_x = x, B_y = N + y, with x in Z_m x|_r Z_k (element a*k+b).
 * Edges:    A_x ~ B_{x s} for s in S, |S| = d, identity in S (WLOG by relabelling B).
 * Validity: left multiplication is an automorphism transitive on each side, so diameter <= D
 *           iff BFS from A_e and from B_e reaches all 2N vertices within D steps.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXG 512

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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* Exact validity: bipartite sides, degree <= d, no duplicates, all pairs within D. */
static int graph_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    static int dist[MAXN], q[MAXN];
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        q[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int v = q[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    q[t++] = u;
                }
            }
        }
        if (t != n) return 0;
    }
    return 1;
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

/* Returns 1 if the start graph is read and valid, else 0. */
static int read_start(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
        add_edge(g, u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int h = 0, t = 0;
        g->side[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = 1 - g->side[v];
                    q[t++] = u;
                } else if (g->side[u] == g->side[v]) {
                    return 0;
                }
            }
        }
    }
    return graph_valid(g);
}

/* ---------------- semidirect group tables ---------------- */

static int GN;                 /* current group order */
static int gtab[MAXG][MAXG];   /* multiplication table */
static int ginv[MAXG];         /* inverses */

/* Element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Needs r^k = 1 mod m. */
static void build_group(int m, int k, int r) {
    GN = m * k;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, e = y % k;
            gtab[x][y] = (int)((((long)a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (gtab[x][y] == 0) { ginv[x] = y; break; }
}

/* ---------------- bi-Cayley search ---------------- */

static int S[MAXD], Sinv[MAXD];
static int dist_[2 * MAXG], qu[2 * MAXG];

/* Two BFS runs (from A_e and B_e) must reach all 2N vertices within D steps. */
static int bc_ok(void) {
    int N2 = 2 * GN;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? GN : 0;
        for (int v = 0; v < N2; v++) dist_[v] = -1;
        int h = 0, t = 0;
        qu[t++] = s0;
        dist_[s0] = 0;
        while (h < t) {
            int v = qu[h++];
            if (dist_[v] >= D) continue;
            if (v < GN) {
                for (int i = 0; i < d; i++) {
                    int u = GN + gtab[v][S[i]];
                    if (dist_[u] < 0) {
                        dist_[u] = dist_[v] + 1;
                        qu[t++] = u;
                    }
                }
            } else {
                int y = v - GN;
                for (int i = 0; i < d; i++) {
                    int u = gtab[y][Sinv[i]];
                    if (dist_[u] < 0) {
                        dist_[u] = dist_[v] + 1;
                        qu[t++] = u;
                    }
                }
            }
        }
        if (t != N2) return 0;
    }
    return 1;
}

static int set_ok(void) {
    for (int i = 0; i < d; i++) Sinv[i] = ginv[S[i]];
    return bc_ok();
}

/* Search connection sets S = {0} + (d-1) further elements in the current group.
 * Exhaustive when the count is small, otherwise random sampling. */
static int search_group(void) {
    int need = d - 1;
    if (need > GN - 1) return 0;
    double combos = 1.0;
    for (int i = 0; i < need; i++)
        combos = combos * (double)(GN - 1 - i) / (double)(i + 1);
    S[0] = 0;
    if (combos <= 40000.0) {
        int c[MAXD];
        for (int i = 0; i < need; i++) c[i] = i + 1;
        for (;;) {
            if (now() > t_end) return 0;
            for (int i = 0; i < need; i++) S[i + 1] = c[i];
            if (set_ok()) return 1;
            int i = need - 1;
            while (i >= 0 && c[i] == GN - need + i) i--;
            if (i < 0) return 0;
            c[i]++;
            for (int j = i + 1; j < need; j++) c[j] = c[j - 1] + 1;
        }
    }
    for (int it = 0; it < 40000; it++) {
        if ((it & 255) == 0 && now() > t_end) return 0;
        for (int i = 0; i < need; i++) {
            for (;;) {
                int v = 1 + rndint(GN - 1), dup = 0;
                for (int j = 1; j <= i; j++)
                    if (S[j] == v) { dup = 1; break; }
                if (!dup) { S[i + 1] = v; break; }
            }
        }
        if (set_ok()) return 1;
    }
    return 0;
}

static int found = 0;
static int bN, bm, bk, br;
static int bS[MAXD];
static Graph start, out;

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_vertices] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long min_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("1 0\n");
        return 0;
    }
    int have = read_start(&start);
    long moore = moore_bound();
    int startn = have ? start.n : 0;

    int Nlo = startn / 2 + 1;
    if ((min_n + 1) / 2 > Nlo) Nlo = (int)((min_n + 1) / 2);
    long Nhi_l = moore / 2;
    if (Nhi_l > MAXG) Nhi_l = MAXG;
    int Nhi = (int)Nhi_l;

    for (int N = Nlo; N <= Nhi && now() < t_end; N++) {
        int got = 0;
        for (int m = 1; m <= N && !got; m++) {
            if (N % m) continue;
            if (now() > t_end) break;
            int k = N / m;
            int rmin = m == 1 ? 0 : 1;
            int rmax = m == 1 ? 1 : m;
            for (int r = rmin; r < rmax && !got; r++) {
                if (m > 1 && gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                if (now() > t_end) break;
                build_group(m, k, r);
                if (search_group()) {
                    got = 1;
                    found = 1;
                    bN = N;
                    bm = m;
                    bk = k;
                    br = r;
                    memcpy(bS, S, sizeof(int) * (size_t)d);
                }
            }
        }
    }

    if (found) {
        build_group(bm, bk, br);
        out.n = 2 * bN;
        for (int v = 0; v < out.n; v++) {
            out.deg[v] = 0;
            out.side[v] = v >= bN;
        }
        for (int x = 0; x < bN; x++)
            for (int i = 0; i < d; i++)
                add_edge(&out, x, bN + gtab[x][bS[i]]);
        if (graph_valid(&out)) {
            print_graph(&out);
            return 0;
        }
    }

    if (have) {
        print_graph(&start);
        return 0;
    }
    /* No usable start: K_{d,d}, valid for D >= 2. */
    Graph kg;
    kg.n = 2 * d;
    for (int v = 0; v < kg.n; v++) {
        kg.deg[v] = 0;
        kg.side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(&kg, a, d + b);
    print_graph(&kg);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


# Minimum order the C search should aim for, per case (beyond the start graph).
MIN_HINT = {(4, 5): 164}


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.2:
        return best
    min_n = max(best[0] + 2, MIN_HINT.get((d, D), 0))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, min_n],
                         stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
