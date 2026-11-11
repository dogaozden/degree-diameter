"""Bi-coset search over projective linear groups PSL(2,p) and PGL(2,p), with a parent fallback.

New construction: a bi-Cayley lift over a non-metacyclic group. The group is PSL(2,p) or
PGL(2,p) for a prime p, as 2x2 matrices over Z_p. A base with s fibres per side and d darts per
fibre gives a graph on 2sN vertices, with N = |G|. Each dart is a group element, and A-vertex x
joins B-vertex x*g. Left multiplication is an automorphism, so the diameter test needs only BFS
from the identity of each fibre. The group sizes give orders that the metacyclic family could not
reach. For d=4, D=8 the orders are 2640 (PGL(2,11), PSL(2,11) with s=2), 4368 (PGL(2,13), s=1),
and so on, against the record 2184 and the Moore bound 6560.

Python builds the best algebraic start, then runs the C engine once per candidate group, smallest
order first. Each run returns a graph only if it is valid and strictly larger. Every result is
rechecked with lib.is_valid, and the best valid graph is always kept.
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

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 3
#define MAXDART (MAXD * MAXP)
#define MAXG 2600

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long MOORE;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (bitset ball expansion). */
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

/* ---------- group: PGL(2,p) or PSL(2,p) as a multiplication table ---------- */

static int GN = 0, GE = 0;
static int GT[MAXG * MAXG];

static inline int gmul(int x, int y) { return GT[x * GN + y]; }

static int pmod(long x, int p) {
    x %= p;
    if (x < 0) x += p;
    return (int)x;
}

/* Elements are normalized matrices (first nonzero entry 1), with det != 0 (and a square
 * det for PSL). Returns the order, or 0 on failure. */
static int build_group(int p, int psl) {
    static int code2idx[17 * 17 * 17 * 17];
    static int elem[MAXG][4];
    static int invp[32];
    int isq[32];
    GN = 0;
    if (p < 3 || p > 17) return 0;
    int P4 = p * p * p * p;
    memset(isq, 0, sizeof isq);
    for (int x = 1; x < p; x++) isq[(x * x) % p] = 1;
    for (int x = 1; x < p; x++)
        for (int y = 1; y < p; y++)
            if ((x * y) % p == 1) invp[x] = y;
    int N = 0;
    for (int c = 0; c < P4; c++) code2idx[c] = -1;
    for (int c = 0; c < P4; c++) {
        int v[4];
        int t = c;
        for (int k = 3; k >= 0; k--) { v[k] = t % p; t /= p; }
        int f = 0;
        for (int k = 0; k < 4; k++)
            if (v[k]) { f = v[k]; break; }
        if (f != 1) continue;
        int det = pmod((long)v[0] * v[3] - (long)v[1] * v[2], p);
        if (det == 0) continue;
        if (psl && !isq[det]) continue;
        if (N >= MAXG) return 0;
        code2idx[c] = N;
        for (int k = 0; k < 4; k++) elem[N][k] = v[k];
        N++;
    }
    int expect = p * (p * p - 1) / (psl ? 2 : 1);
    if (N != expect) return 0;
    GE = code2idx[p * p * p + 1];
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            int a1 = elem[i][0], b1 = elem[i][1], c1 = elem[i][2], e1 = elem[i][3];
            int a2 = elem[j][0], b2 = elem[j][1], c2 = elem[j][2], e2 = elem[j][3];
            int r[4];
            r[0] = pmod((long)a1 * a2 + (long)b1 * c2, p);
            r[1] = pmod((long)a1 * b2 + (long)b1 * e2, p);
            r[2] = pmod((long)c1 * a2 + (long)e1 * c2, p);
            r[3] = pmod((long)c1 * b2 + (long)e1 * e2, p);
            int f = 0;
            for (int k = 0; k < 4; k++)
                if (r[k]) { f = r[k]; break; }
            if (!f) return 0;
            int s = invp[f];
            int code = 0;
            for (int k = 0; k < 4; k++) code = code * p + (r[k] * s) % p;
            int idx = code2idx[code];
            if (idx < 0) return 0;
            GT[i * N + j] = idx;
        }
    }
    if (GE < 0) return 0;
    GN = N;
    return N;
}

/* ---------- bi-coset lift over the group ---------- */

static int di[MAXDART], dj[MAXDART], dg[MAXDART];

/* Base multigraph on p + p vertices, d-regular: d random permutations, one dart per fibre each. */
static void make_darts(int p) {
    int nd = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < p; i++) { di[nd] = i; dj[nd] = perm[i]; nd++; }
    }
}

/* True if voltage g on dart t would duplicate another dart's voltage on the same fibre pair. */
static int clashes(int t, int g, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

/* A-fibre i element x -> i*GN + x; B-fibre j element x -> (p+j)*GN + x. */
static void build_lift(Graph *g, int p, int nd) {
    int S = p * GN;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < GN; x++)
            add_edge(g, di[t] * GN + x, S + dj[t] * GN + gmul(x, dg[t]));
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication is a regular automorphism on each fibre, so the diameter is at most D iff
 * BFS from the identity of every fibre (2p sources) reaches everything within D. */
static long orbit_bad(const Graph *g, int p) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * GN + GE;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Simulated annealing on the voltages of the current darts. Leaves dg and g consistent. */
static long anneal(Graph *g, int p, int nd, int maxit, double until) {
    build_lift(g, p, nd);
    long bad = orbit_bad(g, p);
    double T = 1.0;
    for (int it = 0; it < maxit && bad > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(GN);
        if (ng == old || clashes(t, ng, nd)) continue;
        dg[t] = ng;
        build_lift(g, p, nd);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dg[t] = old;
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    build_lift(g, p, nd);
    return bad;
}

/* Coordinate polish: for each dart, sample candidate voltages and keep the best one. */
static long polish(Graph *g, int p, int nd, long bad, double until) {
    for (int sweep = 0; sweep < 3 && bad > 0; sweep++) {
        int improved = 0;
        for (int t = 0; t < nd && bad > 0; t++) {
            if (now() > until) break;
            int old = dg[t], bestg = old;
            long bestb = bad;
            for (int k = 0; k < 40; k++) {
                int ng = rndint(GN);
                if (ng == old || clashes(t, ng, nd)) continue;
                dg[t] = ng;
                build_lift(g, p, nd);
                long nb = orbit_bad(g, p);
                if (nb < bestb) { bestb = nb; bestg = ng; }
            }
            dg[t] = bestg;
            build_lift(g, p, nd);
            bad = orbit_bad(g, p);
            if (bestg != old) improved = 1;
        }
        if (!improved) break;
    }
    build_lift(g, p, nd);
    return bad;
}

/* Repeated random bases and voltages at the current group until the deadline. */
static int attempt_family(Graph *best, int p, double until) {
    static Graph cand;
    int nd = p * d;
    while (now() < until) {
        make_darts(p);
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(GN); } while (clashes(t, g, nd));
            dg[t] = g;
        }
        long bad = anneal(&cand, p, nd, 20000, until);
        if (bad > 0) bad = polish(&cand, p, nd, bad, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return 1;
        }
    }
    return 0;
}

/* argv: d D seed time_limit [prime psl shape]. Without a prime, the start graph is returned. */
int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [prime psl shape] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int prime = argc >= 6 ? atoi(argv[5]) : 0;
    int psl = argc >= 7 ? atoi(argv[6]) : 0;
    int shape = argc >= 8 ? atoi(argv[7]) : 1;
    double t0 = now();
    double t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (prime > 0 && D >= 2 && shape >= 1 && shape <= MAXP) {
        int N = build_group(prime, psl);
        long V = 2L * shape * N;
        if (N >= d && V <= MOORE && V <= MAXN && V > best.n) {
            attempt_family(&best, shape, t_end);
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
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


def group_candidates(d, D, n_cur):
    """(order, prime, psl, shape) for PGL/PSL(2,p) lifts with n_cur < order <= Moore bound, smallest first."""
    moore = lib.moore_bound(d, D)
    out = []
    for q in (5, 7, 11, 13, 17):
        for psl in (1, 0):
            N = q * (q * q - 1) // (2 if psl else 1)
            if N > 2600 or N < d:
                continue
            for s in (1, 2, 3):
                V = 2 * s * N
                if n_cur < V <= moore and V <= 8192:
                    out.append((V, q, psl, s))
    out.sort()
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    deadline = t0 + 0.85 * time_limit - 1.5
    tried = set()
    rnd = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        todo = [c for c in group_candidates(d, D, best[0]) if c[1:] not in tried]
        if not todo:
            break
        _, q, psl, s = todo[0]
        tried.add((q, psl, s))
        budget = min(remaining, max(3.0, remaining * 0.35))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + rnd, budget, q, psl, s],
                             stdin_graph=best, timeout=budget + 10)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
        rnd += 1
    return best
