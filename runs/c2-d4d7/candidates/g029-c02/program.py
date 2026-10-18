"""Bi-Cayley repair search for the weakest target (d=4, D=7).

Change from the parent: the C engine no longer lifts over PSL/PGL products. It is a new, compact core.

1. For each order N = |G| (starting just above the best verified start), pick a random metacyclic group
   G = Z_m x| Z_k of order N. Take d distinct voltages and form the bi-Cayley graph on A=G, B=G with
   edges A_x ~ B_{x*g}. Left multiplication is an automorphism, so the diameter test only needs BFS from
   A_e and B_e (orbit-reduced). Hill-climb the voltages to zero unreached pairs.
2. If the climb stalls, keep the near-valid lift with the fewest unreached pairs. Repair it with
   degree- and bipartite-preserving 2-switches, annealing on the exact all-pairs bad count.
3. Every accepted graph passes an exact full check. If nothing verifies, the Python side returns the
   best verified start (H(3) incidence, 728 vertices, or a smaller algebraic graph).

Not benchmarked here. The design is intended to explore a different family from the parent's lifts.
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

#define MAXN 2048
#define MAXD 16
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* Metacyclic group Z_m x| Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int GM, GK;
static int rp[MAXN];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int aa = (int)(((long)a + (long)rp[b] * c) % GM);
    return aa * GK + (b + e) % GK;
}

static int random_group(int N, int *pm, int *pk, int *pr) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cnt++;
            if (rndint(cnt) == 0) { *pm = 1; *pk = k; *pr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1) continue;
            cnt++;
            if (rndint(cnt) == 0) { *pm = m; *pk = k; *pr = r; }
        }
    }
    return cnt > 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
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

static void copy_graph(Graph *dst, const Graph *src) { memcpy(dst, src, sizeof(Graph)); }

/* Bi-Cayley graph: A_x (index x) ~ B_{x*g} (index N + x*g) for each voltage g. */
static void build_bc(Graph *g, const int *volt, int N) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + gmul(x, volt[t]));
}

static int dist_buf[MAXN], queue_buf[MAXN];

static long bfs_unreached(const Graph *g, int src) {
    int n = g->n, h = 0, t = 0;
    for (int v = 0; v < n; v++) dist_buf[v] = -1;
    dist_buf[src] = 0;
    queue_buf[t++] = src;
    while (h < t) {
        int v = queue_buf[h++];
        if (dist_buf[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (dist_buf[u] < 0) {
                dist_buf[u] = dist_buf[v] + 1;
                queue_buf[t++] = u;
            }
        }
    }
    return n - t;
}

/* Orbit-reduced: left multiplication is an automorphism, so every vertex is equivalent to
 * A_e (index 0) or B_e (index N). Zero iff the lift has diameter <= D. */
static long orbit_bad(const Graph *g, int N) {
    return bfs_unreached(g, 0) + bfs_unreached(g, N);
}

static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];

/* Exact number of unordered pairs at distance > D. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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

static int valid_full(const Graph *g, int N) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || (v < N) == (u < N)) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* Hill-climb on the voltages of the current group. Returns the best orbit-bad count found. */
static long climb(int N, int *volt, Graph *g, long steps) {
    int bv[MAXD];
    memcpy(bv, volt, sizeof(int) * d);
    build_bc(g, volt, N);
    long ob = orbit_bad(g, N), bob = ob;
    for (long s = 0; s < steps && ob > 0; s++) {
        int t = rndint(d), old = volt[t], ng = rndint(N);
        int clash = 0;
        for (int i = 0; i < d; i++)
            if (volt[i] == ng) { clash = 1; break; }
        if (clash) continue;
        volt[t] = ng;
        build_bc(g, volt, N);
        long nb = orbit_bad(g, N);
        if (nb <= ob || rnd01() < 0.01) {
            ob = nb;
            if (ob < bob) {
                bob = ob;
                memcpy(bv, volt, sizeof(int) * d);
            }
        } else {
            volt[t] = old;
        }
    }
    memcpy(volt, bv, sizeof(int) * d);
    build_bc(g, volt, N);
    return bob;
}

/* Degree-preserving bipartite 2-switches, annealed on the exact bad-pair count. */
static int anneal(Graph *g, int N, double until) {
    long bad = bad_pairs(g);
    double T = 0.6;
    while (bad > 0) {
        if (now() >= until) break;
        int v = rndint(N), u = g->adj[v][rndint(g->deg[v])];
        int w = rndint(N), z = g->adj[w][rndint(g->deg[w])];
        if (w == v || z == u || has_edge(g, v, z) || has_edge(g, w, u)) continue;
        del_edge(g, v, u);
        del_edge(g, w, z);
        add_edge(g, v, z);
        add_edge(g, w, u);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(g, v, z);
            del_edge(g, w, u);
            add_edge(g, v, u);
            add_edge(g, w, z);
        }
        T *= 0.9995;
        if (T < 0.05) T = 0.6;
    }
    return bad == 0 && valid_full(g, N);
}

/* Try to find a valid bi-Cayley graph with 2N vertices. */
static int solve_N(int N, Graph *res, double until) {
    static Graph g, near;
    long nearbad = -1;
    double ts = now() + 0.35 * (until - now());
    if (ts - now() > 10.0) ts = now() + 10.0;
    int volt[MAXD];
    while (now() < ts) {
        int m, k, r;
        if (!random_group(N, &m, &k, &r)) return 0;
        set_group(m, k, r);
        for (int i = 0; i < d; i++) {
            int c, dup;
            do {
                c = rndint(N);
                dup = 0;
                for (int j = 0; j < i; j++)
                    if (volt[j] == c) dup = 1;
            } while (dup);
            volt[i] = c;
        }
        long ob = climb(N, volt, &g, 4000);
        if (ob == 0) {
            if (valid_full(&g, N)) {
                copy_graph(res, &g);
                return 1;
            }
        } else if (nearbad < 0 || ob < nearbad) {
            nearbad = ob;
            copy_graph(&near, &g);
        }
    }
    if (nearbad < 0) return 0;
    if (anneal(&near, N, now() + 0.7 * (until - now()))) {
        copy_graph(res, &near);
        return 1;
    }
    return 0;
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

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit N0\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int N0 = atoi(argv[5]);
    double t0 = now(), tend = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    static Graph res, best;
    int have = 0;
    int N = N0 < d ? d : N0;
    while (now() < tend && 2L * N <= moore && 2 * N <= MAXN) {
        if (!solve_N(N, &res, tend)) break;
        copy_graph(&best, &res);
        have = 1;
        N++;
    }
    if (!have) printf("0 0\n");
    else print_graph(&best);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 5.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0] // 2 + 1],
                         stdin_graph=None, timeout=budget + 5.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
