"""Two-arm search for bipartite graphs with max degree d and diameter <= D.

Arm A (new): bi-Cayley graphs over PSL(2,p) and PGL(2,p). Vertices are (g,0) and (g,1) for g in G,
with (g,0) ~ (g*s,1) for s in S, |S| = d. Left translation is an automorphism, so the diameter
condition reduces to two BFS runs, from (1,0) and (1,1). A C simulated annealing search swaps
elements of S to cover every vertex within distance D. The group order is chosen by a bisection
over candidate primes, aiming near 0.27 of the Moore bound.

Arm B (fallback): the previous voltage-lift search plus C grow-by-two, run on the remaining time.

Every returned graph is checked with lib.is_valid. K_{d,d} and the exact constructions are the floor.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_BI = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 5000
#define MAXD 32
#define PATIENCE 40000L

static int P, KIND, DD, D, G, IDN;
static int mats[MAXG][4];
static int *idxof, *invtab, *INV, *vis, *queue;
static uint16_t *MT;
static int S[MAXD], Sinv[MAXD];
static char inS[MAXG];
static int stampc = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pmod(long x) {
    x %= P;
    if (x < 0) x += P;
    return (int)x;
}

static long powmod(long b, long e) {
    long r = 1;
    b %= P;
    if (b < 0) b += P;
    while (e > 0) {
        if (e & 1) r = r * b % P;
        b = b * b % P;
        e >>= 1;
    }
    return r;
}

static int code4(int a, int b, int c, int e) { return ((a * P + b) * P + c) * P + e; }

/* Canonical code of the projective class of matrix (a b; c e).
 * KIND 0 (PSL): SL2 modulo +-I, so take min(M, -M). KIND 1 (PGL): scale first nonzero entry to 1. */
static int canon(long a, long b, long c, long e) {
    int x0 = pmod(a), x1 = pmod(b), x2 = pmod(c), x3 = pmod(e);
    if (KIND == 1) {
        int f = x0 ? x0 : (x1 ? x1 : (x2 ? x2 : x3));
        int iv = invtab[f];
        x0 = x0 * iv % P;
        x1 = x1 * iv % P;
        x2 = x2 * iv % P;
        x3 = x3 * iv % P;
        return code4(x0, x1, x2, x3);
    }
    int c1 = code4(x0, x1, x2, x3);
    int c2 = code4(pmod(-(long)x0), pmod(-(long)x1), pmod(-(long)x2), pmod(-(long)x3));
    return c1 < c2 ? c1 : c2;
}

static void decode(int code, int m[4]) {
    m[3] = code % P;
    code /= P;
    m[2] = code % P;
    code /= P;
    m[1] = code % P;
    code /= P;
    m[0] = code;
}

static int build_group(void) {
    long N4 = (long)P * P * P * P;
    idxof = malloc(sizeof(int) * (size_t)N4);
    if (!idxof) return 0;
    for (long i = 0; i < N4; i++) idxof[i] = -1;
    G = 0;
    for (int a = 0; a < P; a++)
        for (int b = 0; b < P; b++)
            for (int c = 0; c < P; c++)
                for (int e = 0; e < P; e++) {
                    int det = pmod((long)a * e - (long)b * c);
                    if (KIND == 0 && det != 1) continue;
                    if (KIND == 1 && det == 0) continue;
                    int cd = canon(a, b, c, e);
                    if (idxof[cd] >= 0) continue;
                    if (G >= MAXG) return 0;
                    idxof[cd] = G;
                    decode(cd, mats[G]);
                    G++;
                }
    return 1;
}

static int setup(void) {
    invtab = malloc(sizeof(int) * P);
    if (!invtab) return 0;
    invtab[0] = 0;
    for (int x = 1; x < P; x++) invtab[x] = (int)powmod(x, P - 2);
    if (!build_group()) return 0;
    INV = malloc(sizeof(int) * G);
    MT = malloc(sizeof(uint16_t) * (size_t)G * G);
    vis = calloc((size_t)2 * G, sizeof(int));
    queue = malloc(sizeof(int) * (size_t)2 * G);
    if (!INV || !MT || !vis || !queue) return 0;
    for (int i = 0; i < G; i++) {
        int *m = mats[i];
        INV[i] = idxof[canon(m[3], -(long)m[1], -(long)m[2], m[0])];
    }
    for (int i = 0; i < G; i++)
        for (int j = 0; j < G; j++) {
            int *x = mats[i], *y = mats[j];
            long a = (long)x[0] * y[0] + (long)x[1] * y[2];
            long b = (long)x[0] * y[1] + (long)x[1] * y[3];
            long c = (long)x[2] * y[0] + (long)x[3] * y[2];
            long e = (long)x[2] * y[1] + (long)x[3] * y[3];
            MT[(size_t)i * G + j] = (uint16_t)idxof[canon(a, b, c, e)];
        }
    return 1;
}

/* BFS from src within Dl steps; returns number of vertices reached (including src). */
static int bfs(int src, int Dl) {
    stampc++;
    int head = 0, tail = 0;
    queue[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < Dl && head < tail; lvl++) {
        int lend = tail;
        while (head < lend) {
            int v = queue[head++];
            if (v < G) {
                const uint16_t *row = MT + (size_t)v * G;
                for (int k = 0; k < DD; k++) {
                    int u = G + row[S[k]];
                    if (vis[u] != stampc) {
                        vis[u] = stampc;
                        queue[tail++] = u;
                    }
                }
            } else {
                const uint16_t *row = MT + (size_t)(v - G) * G;
                for (int k = 0; k < DD; k++) {
                    int u = row[Sinv[k]];
                    if (vis[u] != stampc) {
                        vis[u] = stampc;
                        queue[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Left translation is an automorphism, so two sources suffice. */
static int eval_cost(void) {
    int c0 = bfs(IDN, D);
    int c1 = bfs(G + IDN, D);
    return (2 * G - c0) + (2 * G - c1);
}

static void print_graph(void) {
    printf("%d %d\n", 2 * G, G * DD);
    for (int g = 0; g < G; g++)
        for (int k = 0; k < DD; k++)
            printf("%d %d\n", g, G + (int)MT[(size_t)g * G + S[k]]);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog p kind d D seed time_limit\n");
        return 2;
    }
    P = atoi(argv[1]);
    KIND = atoi(argv[2]);
    DD = atoi(argv[3]);
    D = atoi(argv[4]);
    long seed = atol(argv[5]);
    double limit = atof(argv[6]);
    double tend = now() + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (P < 3 || P > 40 || (KIND != 0 && KIND != 1) || DD < 1 || DD > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    if (!setup() || G < DD) {
        printf("0 0\n");
        return 0;
    }
    IDN = idxof[canon(1, 0, 0, 1)];

    long iter = 0;
    while (1) {
        memset(inS, 0, sizeof(inS));
        for (int k = 0; k < DD; k++) {
            int x;
            do x = rndint(G);
            while (inS[x]);
            inS[x] = 1;
            S[k] = x;
            Sinv[k] = INV[x];
        }
        int cost = eval_cost();
        int bestc = cost;
        long since = 0;
        double T = 2.0;
        while (cost > 0) {
            if ((++iter & 31) == 0 && now() > tend) {
                printf("0 0\n");
                return 0;
            }
            if (++since > PATIENCE) break;
            int k = rndint(DD);
            int x = rndint(G);
            if (inS[x]) continue;
            int old = S[k];
            inS[old] = 0;
            inS[x] = 1;
            S[k] = x;
            Sinv[k] = INV[x];
            int nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                if (cost < bestc) {
                    bestc = cost;
                    since = 0;
                }
            } else {
                inS[x] = 0;
                inS[old] = 1;
                S[k] = old;
                Sinv[k] = INV[old];
            }
            T *= 0.9995;
            if (T < 0.3) T = 2.0;
        }
        if (cost == 0) {
            print_graph();
            return 0;
        }
    }
    return 0;
}
'''


C_SOURCE = r'''
/* Grow-by-two search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
 *
 * Each step inserts one vertex on each side, using the spare degree freed by d-1 deleted
 * edges, then anneals degree-preserving edge swaps until every pair is within distance D.
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
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* Number of unordered pairs at distance > D; also sets badv[v]. */
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
        badv[v] = n - c;
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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

static double t_end;
static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;

/* One grow-by-two attempt starting from best; on success work holds n+2 valid vertices. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
    }
}

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
    t_end = t0 + limit * 0.9 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    grow_search(t_end);
    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# Arm A: bi-Cayley graphs over PSL(2,p) / PGL(2,p).
# ----------------------------------------------------------------------------

def _prime_list(limit):
    return [p for p in range(5, limit) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def _bicayley_arm(d, D, seed, deadline, best_n, consider):
    """Bisection over group orders; each step runs C_BI for a time slice."""
    moore = lib.moore_bound(d, D)
    cands = []
    for p in _prime_list(40):
        for kind in (0, 1):
            G = (p ** 3 - p) // 2 if kind == 0 else p ** 3 - p
            n = 2 * G
            if G <= 5000 and d <= G and best_n < n <= moore:
                cands.append((n, p, kind))
    if not cands:
        return
    cands.sort()
    target = 0.27 * moore
    t = 0
    for i, c in enumerate(cands):
        if c[0] <= target:
            t = i
    lo, hi = 0, len(cands)
    mid = t
    while lo < hi:
        left = deadline - time.monotonic()
        if left < 3.0:
            break
        n, p, kind = cands[mid]
        slice_ = min(left, max(4.0, 0.45 * left))
        ok = False
        try:
            text = lib.run_c(C_BI, [p, kind, d, D, seed + mid, round(slice_, 2)],
                             timeout=slice_ + 20)
            gn, ge = lib.parse_graph_text(text)
            if gn > 0 and consider(gn, ge):
                ok = True
        except Exception:
            ok = False
        if ok:
            lo = mid + 1
        else:
            hi = mid
        mid = (lo + hi) // 2


# ----------------------------------------------------------------------------
# Arm B (fallback): Z_m x| Z_k2 bi-Cayley lift search, then C grow-by-two.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) with Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when block representative b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def _legacy_build(d, D, seed, time_limit):
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

    lift_frac = 0.6 if best_n > 3000 else 0.75
    lift_deadline = t0 + lift_frac * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < lift_deadline:
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    remaining = final - time.monotonic() - 2.0
    if remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    hard = t0 + max(2.0, 0.9 * time_limit - 1.0)
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

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
    if D == 4 and time.monotonic() < hard:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Arm A (bold): bi-Cayley over PSL/PGL, using about 60% of the budget.
    a_deadline = t0 + 0.6 * (hard - t0)
    try:
        _bicayley_arm(d, D, seed, a_deadline, best_n, consider)
    except Exception:
        pass

    # Arm B (fallback): the previous lift search and C grow on whatever time is left.
    left = hard - time.monotonic()
    if left > 4.0:
        try:
            res = _legacy_build(d, D, seed, (left + 1.5) / 0.85)
            consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
