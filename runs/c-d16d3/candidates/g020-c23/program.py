"""Combined diameter-3 search: best structured start, then C augmentation and grow-by-two annealing.

Python builds several valid starts: the Moore graph or Araujo-Pardo-Lopez record when available,
the conic blow-up of PG(2,q), arc-extended projective plane incidence graphs, and the generalized
quadrangle for D >= 4. It keeps the largest valid one.

The C engine alternates two moves. (1) Vertex augmentation: add one vertex on a random side,
joined to a greedy set cover T of spare vertices on the other side, accepted only if every
vertex lies within D-1 of T. (2) Grow-by-two: insert one vertex per side using stolen edges,
then anneal degree-preserving edge swaps until the diameter bound holds. A failed grow is rolled
back from a snapshot. Python re-checks everything with lib.is_valid and keeps a valid fallback.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 64
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int side[MAXN];
} Graph;

static Graph G, SNAP;
static int d, D;          /* degree bound and diameter bound */
static int R;             /* covering radius for augmentation: D - 1 */
static double t_end;
static uint64_t ball[MAXN][MAXW];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int mstamp = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ------------------------------------------------------------ graph basics */

static int has_edge(int u, int v) {
    for (int i = 0; i < G.deg[u]; i++)
        if (G.adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    G.adj[u][G.deg[u]++] = v;
    G.adj[v][G.deg[v]++] = u;
}

static void del_half(int u, int v) {
    for (int i = 0; i < G.deg[u]; i++)
        if (G.adj[u][i] == v) {
            G.adj[u][i] = G.adj[u][--G.deg[u]];
            return;
        }
}

static void del_edge(int u, int v) {
    del_half(u, v);
    del_half(v, u);
}

/* Bitset of vertices within distance r of src. */
static void ball_of(int src, int r, uint64_t *bits, int W) {
    int head = 0, t = 0;
    mstamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = mstamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < G.deg[u]; k++) {
            int v = G.adj[u][k];
            if (mark[v] != mstamp) {
                mark[v] = mstamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    int W = (G.n + 63) / 64;
    for (int v = 0; v < G.n; v++) ball_of(v, R, ball[v], W);
}

/* Number of unordered pairs at distance > D; also fills badv[v]. */
static long bad_pairs(void) {
    int n = G.n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < G.deg[v]; i++) {
                const uint64_t *s = cur + (size_t)G.adj[v][i] * W;
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
        for (int w = 0; w < W; w++) c += popc(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(void) {
    int n = G.n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (G.deg[v] > d) return 0;
        for (int i = 0; i < G.deg[v]; i++) {
            int u = G.adj[v][i];
            if (u < 0 || u >= n || u == v || G.side[u] == G.side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (G.adj[v][j] == u) return 0;
        }
    }
    return bad_pairs() == 0;
}

/* ------------------------------------------------------------ input / output */

static void read_start(void) {
    int n, m;
    G.n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    G.n = n;
    for (int v = 0; v < n; v++) {
        G.deg[v] = 0;
        G.side[v] = -1;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            G.deg[u] >= MAXDEG || G.deg[v] >= MAXDEG) {
            G.n = 0;
            return;
        }
        add_edge(u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (G.side[s] >= 0) continue;
        int head = 0, tail = 0;
        G.side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < G.deg[v]; i++) {
                int u = G.adj[v][i];
                if (G.side[u] < 0) {
                    G.side[u] = 1 - G.side[v];
                    queue[tail++] = u;
                }
            }
        }
    }
    if (!is_valid()) G.n = 0;
}

static void print_graph(void) {
    long m = 0;
    for (int u = 0; u < G.n; u++)
        for (int i = 0; i < G.deg[u]; i++)
            if (u < G.adj[u][i]) m++;
    printf("%d %ld\n", G.n, m);
    for (int u = 0; u < G.n; u++)
        for (int i = 0; i < G.deg[u]; i++)
            if (u < G.adj[u][i]) printf("%d %d\n", u, G.adj[u][i]);
}

/* K_{d,d}: valid for every D >= 2. */
static void complete_bipartite(void) {
    G.n = 2 * d;
    for (int v = 0; v < G.n; v++) {
        G.deg[v] = 0;
        G.side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(a, d + b);
}

/* ------------------------------------------------------------ augmentation */

/* Add one vertex on side X joined to a greedy cover T (other side, spare degree),
 * where every existing vertex must lie within R = D-1 of T. Returns 1 on success. */
static int try_add(int X) {
    int n = G.n;
    if (n + 1 >= MAXN) return 0;
    int W = (n + 63) / 64;
    uint64_t U[MAXW];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
    memset(sel, 0, sizeof(int) * (size_t)n);
    while (nt < d) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < n; v++) {
            if (G.side[v] == X || G.deg[v] >= d || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = n;
    G.side[x] = X;
    G.deg[x] = 0;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        G.adj[x][G.deg[x]++] = t;
        G.adj[t][G.deg[t]++] = x;
    }
    G.n = n + 1;
    recompute_balls();
    return 1;
}

/* ------------------------------------------------------------ grow by two */

/* Insert one vertex per side (degree d each) by stealing d-1 edges, then anneal
 * degree-preserving 2-switches until the diameter bound holds. Returns is_valid(). */
static int grow_once(double until) {
    int n = G.n;
    if (n + 2 > MAXN - 2) return 0;
    int x = n, y = n + 1;
    G.n = n + 2;
    G.deg[x] = 0;
    G.deg[y] = 0;
    G.side[x] = 0;
    G.side[y] = 1;
    add_edge(x, y);
    static int used[MAXN];
    static int ustamp = 0;
    ustamp++;
    used[x] = used[y] = ustamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (G.side[a] != 0 || used[a] == ustamp || G.deg[a] == 0) continue;
        int b = G.adj[a][rndint(G.deg[a])];
        if (b >= n || used[b] == ustamp) continue;
        del_edge(a, b);
        add_edge(x, b);
        add_edge(y, a);
        used[a] = used[b] = ustamp;
        k++;
    }

    long bad = bad_pairs();
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(G.n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(G.n);
        if (G.deg[v] == 0) continue;
        int u = G.adj[v][rndint(G.deg[v])];
        int s = rndint(G.n);
        if (s == v || G.side[s] != G.side[v] || G.deg[s] == 0) continue;
        int t = G.adj[s][rndint(G.deg[s])];
        if (t == u || has_edge(v, t) || has_edge(s, u)) continue;
        del_edge(v, u);
        del_edge(s, t);
        add_edge(v, t);
        add_edge(s, u);
        long nb = bad_pairs();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(v, t);
            del_edge(s, u);
            add_edge(v, u);
            add_edge(s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid();
}

/* ------------------------------------------------------------ driver */

static void search(void) {
    recompute_balls();
    int fails = 0;
    while (now() < t_end) {
        if (fails < 200 && G.n + 1 < MAXN) {
            if (try_add(rndint(2))) fails = 0;
            else fails++;
            continue;
        }
        if (G.n + 2 > MAXN - 2) break;
        double left = t_end - now();
        if (left <= 0.0) break;
        double slice = left < 4.0 ? left : 4.0;
        memcpy(&SNAP, &G, sizeof(Graph));
        if (grow_once(now() + slice)) recompute_balls();
        else memcpy(&G, &SNAP, sizeof(Graph));
        fails = 0;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 1 || d > 60 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    t_end = now() + budget;
    R = D - 1;
    read_start();
    if (G.n == 0) complete_bipartite();
    search();
    if (!is_valid()) complete_bipartite();
    print_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts for diameter 3 (and a generalized quadrangle for D >= 4).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy point set S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q) with q = d-3 odd, using a conic and a dual conic.

    Gives 2(q^2+q+1) + 2(q+1) vertices, which is 394 for q = 13 (d = 16).
    """
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def known_start(d, D):
    """Best directly constructed graph for D = 3, or None."""
    if D != 3:
        return None
    if lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record construction
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) for the largest prime power q <= min(d-1, 7), for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    cands = []
    for make in (lambda: known_start(d, D), lambda: conic_blowup(d, D)):
        try:
            g = make()
        except Exception:
            g = None
        if g is not None:
            cands.append(g)
    if D >= 3:
        try:
            cands.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
        except Exception:
            pass
    if D >= 4:
        try:
            g = _best_gq(d)
            if g is not None:
                cands.append(g)
        except Exception:
            pass

    best = fallback
    for g in sorted(cands, key=lambda g: -g[0]):
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g
            break

    # Nothing can beat a Moore graph.
    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
    if remaining >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                             stdin_graph=best, timeout=remaining + 5.0)
            n1, e1 = lib.parse_graph_text(text)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass  # keep the valid structured start

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
