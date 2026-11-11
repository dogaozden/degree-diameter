"""Bold change for the weakest target (d=4, D=7): start from the split Cayley hexagon H(3), which has
diameter 6 and so leaves one unit of diameter slack for D=7, then grow it in C by inserting vertex
pairs and annealing degree-preserving swaps. Random bi-Cayley / voltage lifts over semidirect groups
Z_m x|_r Z_k (for 1 or 2 base vertices per side) run first for a short slice and can replace the start
if they produce a larger valid graph. Every returned graph is checked with lib.is_valid, and the best
valid graph found so far is always the fallback.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Grow-by-two annealing engine for bipartite degree-diameter graphs.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (must be a valid bipartite graph), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 * Each round inserts one vertex per side joined to each other, attaches them by d-1 degree-
 * preserving edge splits, then anneals degree-preserving swaps to remove all bad pairs.
 */
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
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (bitset BFS). Fills badv[] per vertex. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
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

static int qbuf[MAXN];

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        qbuf[tail++] = s;
        while (head < tail) {
            int v = qbuf[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = 1 - g->side[v];
                    qbuf[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

/* Insert two vertices x (side 0) and y (side 1), joined to each other, and attach them by
 * splitting edges (a,b) with a on side 0 and b on side 1 into (x,b) and (y,a). Then anneal
 * degree-preserving swaps until no bad pairs remain or the deadline passes. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = stamp;
    used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 200000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = stamp;
        used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (s == v || work->side[s] != work->side[v] || work->deg[s] == 0) continue;
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

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD - 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double tend = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, work;
    read_start(&best);
    if (best.n == 0) {
        printf("0 0\n");
        return 0;
    }
    while (now() < tend && best.n + 2 <= moore_bound() && best.n + 2 <= MAXN) {
        double left = tend - now();
        double slice = left / 4.0;
        if (slice < 3.0) slice = left;
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
    }
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

    Returns None if no sign convention yields a graph that passes lib.is_valid with diameter 6.
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
    """Algebraic candidate graphs valid for diameter D (may be empty)."""
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


def _connected(M, p):
    """Is the bipartite multigraph on p+p base vertices with multiplicities M connected?"""
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for u in range(2 * p):
            if u in seen:
                continue
            if v < p and u >= p:
                linked = M[v][u - p] > 0
            elif v >= p and u < p:
                linked = M[u][v - p] > 0
            else:
                linked = False
            if linked:
                seen.add(u)
                stack.append(u)
    return len(seen) == 2 * p


def _random_group(rng, lo, hi):
    """Random lift setting: p base vertices per side and a semidirect group Z_m x|_r Z_k of order N,
    with 2*p*N in [lo, hi]. Returns (p, N, mul) or None."""
    p = rng.choice((1, 2))
    step = 2 * p
    Nlo = max(2, -(-lo // step))
    Nhi = hi // step
    if Nlo > Nhi:
        return None
    N = rng.randint(Nlo, Nhi)
    divs = [m for m in range(1, N + 1) if N % m == 0]
    m = rng.choice(divs)
    k = N // m
    r = 1 if m <= 2 else rng.randrange(1, m)
    try:
        _order, mul, _inv = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    return p, N, mul


def _lift_try(p, N, mul, d, D, rng, steps, deadline):
    """Voltage lift over a group of order N with p base vertices per side and d darts per base
    vertex. Hill-climbs the voltages using a fibre-representative BFS (the group acts by left
    multiplication, so BFS from the 2p fibre identities suffices). Returns (n, edges) or None."""
    n = 2 * p * N
    if N < d:
        return None
    M = None
    for _ in range(100):
        cand = [[0] * p for _ in range(p)]
        for _t in range(d):
            perm = list(range(p))
            rng.shuffle(perm)
            for i in range(p):
                cand[i][perm[i]] += 1
        if _connected(cand, p):
            M = cand
            break
    if M is None:
        return None
    darts = []
    for i in range(p):
        for j in range(p):
            picked = []
            for _ in range(M[i][j]):
                g = rng.randrange(N)
                while g in picked:
                    g = rng.randrange(N)
                picked.append(g)
                darts.append([i, j, g])
    reps = [b * N for b in range(2 * p)]

    def build_adj():
        adj = [[] for _ in range(n)]
        for i, j, g in darts:
            base_b = (p + j) * N
            for x in range(N):
                a = i * N + x
                b = base_b + mul(x, g)
                adj[a].append(b)
                adj[b].append(a)
        return adj

    def unreached(adj):
        total = 0
        for s in reps:
            seen = [False] * n
            seen[s] = True
            frontier = [s]
            cnt = 1
            for _ in range(D):
                nxt = []
                for v in frontier:
                    for u in adj[v]:
                        if not seen[u]:
                            seen[u] = True
                            cnt += 1
                            nxt.append(u)
                if not nxt:
                    break
                frontier = nxt
            total += n - cnt
        return total

    adj = build_adj()
    bad = unreached(adj)
    while bad > 0 and steps > 0:
        if time.monotonic() > deadline:
            return None
        steps -= 1
        t = rng.randrange(len(darts))
        i, j, old = darts[t]
        g = rng.randrange(N)
        if any(q[0] == i and q[1] == j and q[2] == g for q in darts):
            continue
        darts[t][2] = g
        adj2 = build_adj()
        nb = unreached(adj2)
        if nb <= bad:
            bad = nb
            adj = adj2
        else:
            darts[t][2] = old
    if bad > 0:
        return None
    edges = sorted({(min(a, b), max(a, b)) for a in range(n) for b in adj[a]})
    if not lib.is_valid(n, edges, d, D):
        return None
    return n, edges


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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 15 or best[0] >= moore:
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best

    # Short phase of random group lifts; a lift replaces the start only if it is larger and valid.
    rng = random.Random(seed * 1000003 + d * 101 + D)
    lift_end = time.monotonic() + 0.3 * budget
    hi = min(moore, 1200)
    try:
        while time.monotonic() < lift_end:
            lo = best[0] + 2
            if lo > hi:
                break
            g = _random_group(rng, lo, hi)
            if g is None:
                continue
            p, N, mul = g
            res = _lift_try(p, N, mul, d, D, rng, 60, lift_end)
            if res is not None and res[0] > best[0]:
                best = res
    except Exception:
        pass

    # Grow-by-two annealing in C from the best valid graph found so far.
    c_budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if c_budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, c_budget],
                             stdin_graph=best, timeout=c_budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
