"""Bi-Cayley (Haar-type) lift search over explicit groups, then a C grow-by-two stage.

Change from the parent: the C engine no longer searches voltage lifts. The lift search moves to
Python, where it targets vertex-transitive-on-each-side Haar graphs H(G,S) of explicit groups:
PSL(2,5) x Z_k, PSL(2,7) x Z_k and metacyclic Z_m x|_r Z_k. Vertices are a_g and b_g for g in G,
with a_g ~ b_{gs} for s in S, |S| = d. Left multiplication is an automorphism that is transitive on
each side, so diameter <= D is checked exactly by BFS from a_e and b_e only. The annealing objective
is the excess distance, sum of max(0, dist - D) with unreached vertices charged 2. Every candidate is
re-checked with lib.is_valid. The C stage is the parent's grow-by-two annealing, which starts from the
best valid graph. If nothing beats the start, the start (at least the known algebraic graphs or
K_{d,d}) is returned.

This is a high-risk change: the parent's C voltage-lift search over small non-cyclic bases is removed,
so the outcome on d=4, D=7 depends on whether the Haar search finds a lift above the start. No
result is guaranteed, but every returned graph is valid.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Grow-by-two engine for bipartite degree-diameter graphs.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXW (MAXN / 64)

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* ---------------------------------------------------------------- grow by two */
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
    static int used[MAXN];
    static int stamp = 0;
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

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    if (D >= 2) grow_search(&best, t_end);
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


# ------------------------------------------------------- explicit groups (tables)

def _psl_table(p):
    """Multiplication table of PSL(2,p) (p prime) acting on P^1(F_p); identity has index 0."""
    inf = p

    def t(x):
        return inf if x == inf else (x + 1) % p

    def s(x):
        if x == inf:
            return 0
        if x == 0:
            return inf
        return (-pow(x, p - 2, p)) % p

    gens = [tuple(t(x) for x in range(p + 1)), tuple(s(x) for x in range(p + 1))]
    ident = tuple(range(p + 1))
    elems = [ident]
    index = {ident: 0}
    for g in elems:  # appending while iterating is intended: closure under right multiplication
        for h in gens:
            k = tuple(g[h[x]] for x in range(p + 1))
            if k not in index:
                index[k] = len(elems)
                elems.append(k)
    n = len(elems)
    tab = [[index[tuple(elems[a][elems[b][x]] for x in range(p + 1))] for b in range(n)]
           for a in range(n)]
    return n, tab


def _product_table(bt, n0, k):
    """Direct product of a group with table bt (order n0) and Z_k; element g*k + c."""
    N = n0 * k
    tab = [[0] * N for _ in range(N)]
    for g in range(n0):
        for c in range(k):
            row = tab[g * k + c]
            for h in range(n0):
                gh = bt[g][h] * k
                base = h * k
                for e in range(k):
                    row[base + e] = gh + (c + e) % k
    return N, tab


def _group_candidates(lo, hi):
    """Group specifications with order in [lo, hi]."""
    out = []
    for N in range(lo, hi + 1):
        if N % 60 == 0:
            out.append(("psl", 5, N // 60))
        if N % 168 == 0:
            out.append(("psl", 7, N // 168))
        for m in range(2, N + 1):
            if N % m == 0 and N // m >= 2:
                out.append(("sd", m, N // m))
    return out


def _make_group(spec, rng):
    """Return (order, table) for a group spec, or None if no valid parameters exist."""
    if spec[0] == "psl":
        n0, bt = _psl_table(spec[1])
        return _product_table(bt, n0, spec[2])
    _, m, k = spec
    opts = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not opts:
        return None
    r = rng.choice(opts)
    N, mul, _ = lib.semidirect_group(m, k, r)
    tab = [[mul(x, y) for y in range(N)] for x in range(N)]
    return N, tab


# ------------------------------------------------------- Haar lift search (Python)

def _excess(N, tab, inv, S, D):
    """Excess distance of H(G,S) from a_e and b_e: sum of max(0, dist - D), unreached counted as 2."""
    invS = [inv[s] for s in S]
    nv = 2 * N
    total = 0
    for src in (0, N):
        dist = [-1] * nv
        dist[src] = 0
        q = [src]
        for v in q:
            dv = dist[v] + 1
            if v < N:
                row = tab[v]
                nb = [N + row[s] for s in S]
            else:
                row = tab[v - N]
                nb = [row[t] for t in invS]
            for u in nb:
                if dist[u] < 0:
                    dist[u] = dv
                    q.append(u)
        for dd in dist:
            if dd < 0:
                total += 2
            elif dd > D:
                total += dd - D
    return total


def _anneal_haar(N, tab, d, D, rng, until):
    """Anneal the connection set S (|S| = d) until the excess is zero. Returns S or None."""
    if N < d:
        return None
    inv = [row.index(0) for row in tab]
    S = rng.sample(range(N), d)
    cur = _excess(N, tab, inv, S, D)
    best_e = cur
    T = 2.0
    stall = 0
    while cur > 0:
        if time.monotonic() >= until:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        e2 = _excess(N, tab, inv, S2, D)
        if e2 <= cur or rng.random() < math.exp(-(e2 - cur) / T):
            S, cur = S2, e2
        if cur < best_e:
            best_e = cur
            stall = 0
        else:
            stall += 1
            if stall > 400:
                S = rng.sample(range(N), d)
                cur = _excess(N, tab, inv, S, D)
                best_e = cur
                T = 2.0
                stall = 0
                continue
        T = max(0.3, T * 0.997)
    return S


def _search_haar_lifts(d, D, n0, rng, until):
    """Search Haar graphs of explicit groups for a valid graph with more than n0 vertices.

    Returns the largest valid (n, edges) found, or None.
    """
    moore = lib.moore_bound(d, D)
    best = None
    cur_n = n0
    while time.monotonic() < until:
        lo = max(d, cur_n // 2 + 1)
        hi = min(moore // 2, lo + 120)
        if hi < lo:
            break
        cands = _group_candidates(lo, hi)
        if not cands:
            break
        spec = rng.choice(cands)
        grp = _make_group(spec, rng)
        if grp is None:
            continue
        N, tab = grp
        slice_end = min(until, time.monotonic() + 8.0)
        S = _anneal_haar(N, tab, d, D, rng, slice_end)
        if S is None:
            continue
        edges = [(g, N + tab[g][s]) for g in range(N) for s in S]
        if 2 * N > cur_n and lib.is_valid(2 * N, edges, d, D):
            best = (2 * N, edges)
            cur_n = 2 * N
    return best


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
    try:
        for n, e in known_starts(d, D):
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    except Exception:
        pass

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    total = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
    if total <= 0.5:
        return best

    rng = random.Random(1000003 * (seed + 1) + 97 * d + D)
    try:
        cand = _search_haar_lifts(d, D, best[0], rng, time.monotonic() + 0.5 * total)
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                             stdin_graph=best, timeout=budget + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
