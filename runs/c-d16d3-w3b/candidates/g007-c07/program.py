import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite graphs with bad-pair cost.
#
# State: a bipartite graph with max degree d. Cost = number of unordered vertex
# pairs at distance > D (unreachable counts). Growth adds one vertex that takes
# d opposite-side neighbours, removing one edge at any saturated neighbour to make
# room. Moves: add a cross edge (never increases cost), or a 2-switch that keeps
# all degrees (Metropolis). The best valid graph is always kept, and the engine
# restores it when a size stalls.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 40
#define MAXW (MAXN / 64)

static int n, d, D, W, nmax;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t ball[MAXN][MAXW];
static uint64_t tmpb[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int bn = 0;
static int bdeg[MAXN];
static int badj[MAXN][MAXD];
static int bcol[MAXN];

static int ax, ay, sa_, sb_, sc_, se_;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int m) { return (int)((rnd64() >> 11) % (uint64_t)m); }

static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

static long long cost(void) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) ball[v][w] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) tmpb[v][w] = ball[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) tmpb[v][w] |= ball[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) ball[v][w] = tmpb[v][w];
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(ball[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int bip_ok(void) {
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (col[adj[u][i]] == col[u]) return 0;
    return 1;
}

static void save_best(void) {
    bn = n;
    memcpy(bdeg, deg, sizeof(deg));
    memcpy(badj, adj, sizeof(adj));
    memcpy(bcol, col, sizeof(col));
}

static void restore_best(void) {
    n = bn;
    memcpy(deg, bdeg, sizeof(deg));
    memcpy(adj, badj, sizeof(adj));
    memcpy(col, bcol, sizeof(col));
}

static void grow(int side) {
    static int sp[MAXN], sat[MAXN];
    int ns = 0, nt = 0;
    for (int u = 0; u < n; u++) {
        if (col[u] == side) continue;
        if (deg[u] < d) sp[ns++] = u;
        else sat[nt++] = u;
    }
    for (int i = ns - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = sp[i]; sp[i] = sp[j]; sp[j] = t;
    }
    for (int i = nt - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = sat[i]; sat[i] = sat[j]; sat[j] = t;
    }
    int w = n++;
    col[w] = side;
    deg[w] = 0;
    int k = 0;
    for (int i = 0; i < ns && k < d; i++) {
        add_edge(sp[i], w);
        k++;
    }
    for (int i = 0; i < nt && k < d; i++) {
        int t = sat[i];
        int x = adj[t][rndi(deg[t])];
        del_edge(t, x);
        add_edge(t, w);
        k++;
    }
}

static int try_add(void) {
    for (int t = 0; t < 80; t++) {
        int x = rndi(n), y = rndi(n);
        if (col[x] == col[y] || deg[x] >= d || deg[y] >= d || has_edge(x, y)) continue;
        ax = x;
        ay = y;
        add_edge(x, y);
        return 1;
    }
    return 0;
}

static int try_switch(void) {
    int a = rndi(n);
    if (deg[a] == 0) return 0;
    int b = adj[a][rndi(deg[a])];
    int c = -1;
    for (int t = 0; t < 40; t++) {
        int x = rndi(n);
        if (x != a && col[x] == col[a] && deg[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    int e = adj[c][rndi(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    sa_ = a; sb_ = b; sc_ = c; se_ = e;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    return 1;
}

static void undo_switch(void) {
    del_edge(sa_, se_);
    del_edge(sc_, sb_);
    add_edge(sa_, sb_);
    add_edge(sc_, se_);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    nmax = (argc > 5) ? atoi(argv[5]) : MAXN;
    if (nmax > MAXN) nmax = MAXN;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                }
            }
        }
    }
    if (!bip_ok()) { printf("0 0\n"); return 0; }

    double t_end = elapsed() + budget;
    long long c = cost();
    int fails = 0;
    const long long PHASE = 15000;

    while (elapsed() < t_end) {
        if (c == 0) {
            save_best();
            if (n >= nmax) break;
            grow(rndi(2));
            c = cost();
            fails = 0;
            continue;
        }
        int fcap = fails < 20 ? fails : 20;
        long long iters = PHASE * (1 + fcap);
        for (long long it = 0; it < iters && c > 0; it++) {
            if ((it & 127) == 0 && elapsed() > t_end) break;
            double frac = (double)it / (double)iters;
            double T = 3.0 * (1.0 - frac) + 0.2;
            if (rndu() < 0.2) {
                if (!try_add()) continue;
                long long nc = cost();
                if (nc <= c) c = nc;
                else del_edge(ax, ay);
            } else {
                if (!try_switch()) continue;
                long long nc = cost();
                if (nc <= c || rndu() < exp(-(double)(nc - c) / T)) c = nc;
                else undo_switch();
            }
        }
        if (c > 0) {
            fails++;
            if (bn > 0) {
                restore_best();
                c = cost();
            }
        }
    }
    if (c == 0) save_best();
    if (bn <= 0) { printf("0 0\n"); return 0; }

    int m2 = 0;
    for (int u = 0; u < bn; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) m2++;
    printf("%d %d\n", bn, m2);
    for (int u = 0; u < bn; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) printf("%d %d\n", u, badj[u][i]);
    return 0;
}
"""


def _c_search(graph, d, D, seed, budget, nmax):
    """Run the C annealing engine from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nmax],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so every target is hit by <= s chosen elements."""
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
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


def _arc_candidates(d, deadline, rng):
    """Return (n, edges) candidates from PG(2, q) for prime powers q with q + 1 <= d."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    for q in qs[:3]:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)

        SA = _greedy_side(m, s, point_lines, rng, 60, deadline)
        SB = _greedy_side(m, s, line_points, rng, 60, deadline)
        if s >= 2:
            F = lib.GF(q)
            pts = lib.projective_points(q)
            index = {p: i for i, p in enumerate(pts)}
            cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
            if q % 2 == 0:
                cs.append(index[(0, 1, 0)])
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, 15000)
        SB = _local_search(m, s, line_points, SB, rng, deadline, 15000)
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: best start graph from constructions, then C annealing with growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or not lib.is_valid(best[0], best[1], d, D):
        return best

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        cands = _arc_candidates(d, start + 0.12 * time_limit,
                                random.Random(seed * 7919 + d))
    else:
        g = _best_gq(d)
        cands = [g] if g is not None else []
    for g in sorted(cands, key=lambda t: -t[0])[:2]:
        consider(g)

    budget = 0.80 * time_limit - el()
    if budget >= 1.0:
        consider(_c_search(best, d, D, seed, budget, lib.moore_bound(d, D)))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
