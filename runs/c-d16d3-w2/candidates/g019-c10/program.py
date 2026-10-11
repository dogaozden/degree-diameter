import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: iterated local search that grows a valid bipartite graph by
# "dominating-vertex insertion".
#
# A new vertex x on side s with neighbour set N (all on the other side, each
# with spare degree) keeps diameter <= D iff every existing vertex v is within
# distance D-1 of N in the current graph. Old pairs can only get closer, so the
# check is exact enough and never breaks validity. Each insertion is found by a
# randomized greedy cover of the vertices by spare-degree neighbours.
#
# Perturbation: delete 1-2 random vertices (keep the graph only if its diameter
# is still <= D), then regrow greedily. Accept growth or equal-size plateau
# moves; otherwise roll back. The best graph seen is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 3000
#define MAXDEG 256
#define INF 65535

typedef struct { int n; int *deg; int *side; int *adj; } Snap;

static int d_, D_, n;
static int deg[MAXN];
static int side_[MAXN];
static int adj[MAXN * MAXDEG];
static uint16_t dist[MAXN * MAXN];
static int qbuf[MAXN];
static int bd[MAXN];
static int dxv[MAXN];
static int chosen[MAXDEG];
static char usedc[MAXN];

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rndint(int m) { return (int)(rnd() % (unsigned long long)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void compute_dist(void) {
    for (int s = 0; s < n; s++) {
        uint16_t *ds = dist + (size_t)s * MAXN;
        for (int v = 0; v < n; v++) ds[v] = INF;
        int h = 0, t = 0;
        qbuf[t++] = s;
        ds[s] = 0;
        while (h < t) {
            int u = qbuf[h++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u * d_ + k];
                if (ds[w] == INF) {
                    ds[w] = (uint16_t)(ds[u] + 1);
                    qbuf[t++] = w;
                }
            }
        }
    }
}

static int diam_ok(void) {
    compute_dist();
    for (int s = 0; s < n; s++) {
        const uint16_t *ds = dist + (size_t)s * MAXN;
        for (int v = 0; v < n; v++)
            if (ds[v] > D_) return 0;
    }
    return 1;
}

static void remove_vertex(int x) {
    for (int k = 0; k < deg[x]; k++) {
        int u = adj[x * d_ + k];
        for (int j = 0; j < deg[u]; j++) {
            if (adj[u * d_ + j] == x) {
                adj[u * d_ + j] = adj[u * d_ + deg[u] - 1];
                deg[u]--;
                break;
            }
        }
    }
    deg[x] = 0;
    int L = n - 1;
    if (x != L) {
        for (int k = 0; k < deg[L]; k++) {
            int w = adj[L * d_ + k];
            for (int j = 0; j < deg[w]; j++) {
                if (adj[w * d_ + j] == L) { adj[w * d_ + j] = x; break; }
            }
        }
        for (int k = 0; k < deg[L]; k++) adj[x * d_ + k] = adj[L * d_ + k];
        deg[x] = deg[L];
        side_[x] = side_[L];
    }
    deg[L] = 0;
    n--;
}

static void snap_save(Snap *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->side, side_, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(int) * (size_t)n * d_);
}

static void snap_load(const Snap *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(side_, s->side, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(int) * (size_t)n * d_);
    compute_dist();
}

/* Add vertex x = n on side ns, adjacent to chosen[0..cnt-1]; bd[] holds the
   distance from each old vertex to the chosen set. Updates dist exactly. */
static void add_vertex(int ns, int cnt) {
    int x = n;
    side_[x] = ns;
    deg[x] = 0;
    for (int i = 0; i < cnt; i++) {
        int u = chosen[i];
        adj[x * d_ + deg[x]++] = u;
        adj[u * d_ + deg[u]++] = x;
    }
    for (int v = 0; v < n; v++) dxv[v] = 1 + bd[v];
    n++;
    for (int v = 0; v < x; v++) {
        dist[(size_t)x * MAXN + v] = (uint16_t)dxv[v];
        dist[(size_t)v * MAXN + x] = (uint16_t)dxv[v];
    }
    dist[(size_t)x * MAXN + x] = 0;
    for (int v = 0; v < x; v++) {
        uint16_t *dv = dist + (size_t)v * MAXN;
        for (int w = 0; w < x; w++) {
            int c = dxv[v] + dxv[w];
            if (c < (int)dv[w]) dv[w] = (uint16_t)c;
        }
    }
}

/* Try to add one vertex on side ns by greedy cover with spare-degree neighbours. */
static int try_add(int ns) {
    if (n >= MAXN - 1) return 0;
    int cnt = 0, U = n;
    for (int v = 0; v < n; v++) bd[v] = INF;
    while (U > 0 && cnt < d_) {
        int bestu = -1;
        double bestsc = -1.0;
        for (int u = 0; u < n; u++) {
            if (side_[u] == ns || deg[u] >= d_ || usedc[u]) continue;
            const uint16_t *du = dist + (size_t)u * MAXN;
            int g = 0;
            for (int v = 0; v < n; v++)
                if (bd[v] > D_ - 1 && (int)du[v] <= D_ - 1) g++;
            if (g == 0) continue;
            double sc = g + 0.9 * rnd01();
            if (sc > bestsc) { bestsc = sc; bestu = u; }
        }
        if (bestu < 0) break;
        chosen[cnt++] = bestu;
        usedc[bestu] = 1;
        const uint16_t *du = dist + (size_t)bestu * MAXN;
        U = 0;
        for (int v = 0; v < n; v++) {
            if ((int)du[v] < bd[v]) bd[v] = (int)du[v];
            if (bd[v] > D_ - 1) U++;
        }
    }
    int ok = (U == 0 && cnt > 0);
    if (ok) add_vertex(ns, cnt);
    for (int i = 0; i < cnt; i++) usedc[chosen[i]] = 0;
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d_ < 1 || d_ > MAXDEG || D_ < 1) { printf("0 0\n"); return 0; }

    int nn = 0, mm = 0;
    if (scanf("%d %d", &nn, &mm) != 2) nn = 0;
    int ok = (nn >= 1 && nn < MAXN - 1 && mm >= 0);
    n = ok ? nn : 0;
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (int i = 0; i < mm && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (deg[u] >= d_ || deg[v] >= d_) { ok = 0; break; }
        for (int k = 0; k < deg[u]; k++)
            if (adj[u * d_ + k] == v) { ok = 0; break; }
        if (!ok) break;
        adj[u * d_ + deg[u]++] = v;
        adj[v * d_ + deg[v]++] = u;
    }

    if (ok) {
        for (int i = 0; i < n; i++) side_[i] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (side_[s] != -1) continue;
            side_[s] = 0;
            int h = 0, t = 0;
            qbuf[t++] = s;
            while (h < t && ok) {
                int u = qbuf[h++];
                for (int k = 0; k < deg[u]; k++) {
                    int w = adj[u * d_ + k];
                    if (side_[w] == -1) { side_[w] = 1 - side_[u]; qbuf[t++] = w; }
                    else if (side_[w] == side_[u]) { ok = 0; break; }
                }
            }
        }
    }
    if (ok && !diam_ok()) ok = 0;
    if (!ok) { printf("0 0\n"); return 0; }

    Snap bk, bs;
    bk.deg = malloc(sizeof(int) * MAXN);
    bk.side = malloc(sizeof(int) * MAXN);
    bk.adj = malloc(sizeof(int) * (size_t)MAXN * d_);
    bs.deg = malloc(sizeof(int) * MAXN);
    bs.side = malloc(sizeof(int) * MAXN);
    bs.adj = malloc(sizeof(int) * (size_t)MAXN * d_);

    snap_save(&bs);
    int best_n = n;
    double t0 = cpu_now();

    while (cpu_now() - t0 < tl) {
        snap_save(&bk);
        int n0 = n;
        int r = 1 + rndint(2);
        for (int i = 0; i < r && n > 4; i++) remove_vertex(rndint(n));
        if (!diam_ok()) { snap_load(&bk); continue; }

        int fails = 0;
        while (fails < 2) {
            int ns = rndint(2);
            if (try_add(ns)) fails = 0;
            else if (try_add(1 - ns)) fails = 0;
            else fails++;
        }

        if (!(n > n0 || (n == n0 && rnd01() < 0.5))) snap_load(&bk);
        if (n > best_n) {
            best_n = n;
            snap_save(&bs);
        }
    }

    int bn = bs.n;
    long m2 = 0;
    for (int v = 0; v < bn; v++) m2 += bs.deg[v];
    printf("%d %ld\n", bn, m2 / 2);
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < bs.deg[v]; k++) {
            int w = bs.adj[v * d_ + k];
            if (v < w) printf("%d %d\n", v, w);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q). A-vertices (one per point in SA) join the q+1 lines
# through their point; each line may carry at most s = d-q-1 A-vertices.
# B-vertices (one per line in SB) are symmetric. Order 2(q^2+q+1) + |SA| + |SB|.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy load-constrained set."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau / improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build: best algebraic start, then C iterated local search grows it.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C iterated local search: insert dominating vertices, perturb by deletion.
    elapsed = time.monotonic() - start
    budget = 0.85 * time_limit - elapsed - 2.0
    if budget >= 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 15.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
