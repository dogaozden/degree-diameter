import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: greedy vertex insertion with ball-cover certificates (diameter D).
#
# Let R = D-1. A new vertex w joined to a set N of opposite-colour vertices is
# within distance D of every old vertex x that lies in the R-ball of some u in N.
# Adding vertices and cross edges never increases old distances, so validity is
# preserved. Each round:
#   1. compute R-balls as bitsets,
#   2. for each colour class, greedily cover all vertices with spare-degree
#      neighbours (randomized tie-breaks) and insert a vertex on success,
#   3. on failure add a random spare cross edge to change the spare pattern.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

static int try_insert(int side) {
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    static int used[MAXN];
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    W = (n + 63) >> 6;
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

    clock_t t0 = clock();
    int fails = 0;
    const int maxfails = 400;
    while (fails < maxfails && n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = (int)(rnd() % (uint32_t)n);
            int v = (int)(rnd() % (uint32_t)n);
            if (u == v || col[u] == col[v]) continue;
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            break;
        }
    }

    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (new): tabu load-packing for one side of the arc extension.
#
# Bipartite graph with left vertices 0..nL-1 and right vertices nL..N-1.
# Choose a left set S maximizing |S| such that every right vertex has at most
# s neighbours in S. Moves insert a random left vertex and evict the (at most
# two) members that block it; evicted vertices are tabu for a short while.
# Stalls restart from the best set found so far.
# Input: "N M" then M edges "a b" (a left, b right with b >= nL).
# Argv: nL s seed budget. Output: "k" then the k chosen left indices.
# ----------------------------------------------------------------------------

C_PACK = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXV 1100
#define MAXDEG 128

static int nL, nR, s;
static int dl[MAXV], al[MAXV][MAXDEG];
static int dr[MAXV], ar[MAXV][MAXDEG];
static int inS[MAXV], load[MAXV], bestS[MAXV];
static long tabu[MAXV];
static uint64_t rs = 2463534242ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 11);
}

static int rr(int k) { return (int)(rnd() % (uint32_t)k); }

static int adjacent(int l, int r) {
    for (int i = 0; i < dl[l]; i++) if (al[l][i] == r) return 1;
    return 0;
}

static void put(int l) {
    inS[l] = 1;
    for (int i = 0; i < dl[l]; i++) load[al[l][i]]++;
}

static void take(int l) {
    inS[l] = 0;
    for (int i = 0; i < dl[l]; i++) load[al[l][i]]--;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0\n\n"); return 0; }
    nL = atoi(argv[1]);
    s = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    int N, M;
    if (scanf("%d %d", &N, &M) != 2) { printf("0\n\n"); return 0; }
    if (nL < 1 || nL >= N || nL > MAXV || N - nL > MAXV) { printf("0\n\n"); return 0; }
    nR = N - nL;
    for (int i = 0; i < M; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a > b) { int t = a; a = b; b = t; }
        if (a < 0 || a >= nL || b < nL || b >= N) continue;
        int l = a, r = b - nL;
        if (dl[l] >= MAXDEG || dr[r] >= MAXDEG) continue;
        al[l][dl[l]++] = r;
        ar[r][dr[r]++] = l;
    }

    static int order[MAXV];
    for (int l = 0; l < nL; l++) order[l] = l;
    for (int i = nL - 1; i > 0; i--) {
        int j = rr(i + 1);
        int t = order[i]; order[i] = order[j]; order[j] = t;
    }
    int size = 0;
    for (int i = 0; i < nL; i++) {
        int l = order[i], ok = 1;
        for (int k = 0; k < dl[l] && ok; k++) if (load[al[l][k]] >= s) ok = 0;
        if (ok) { put(l); size++; }
    }
    int best = size;
    memcpy(bestS, inS, sizeof(int) * MAXV);

    clock_t t0 = clock();
    long it = 0, last = 0;
    int rem[4];
    while (1) {
        if ((it & 255) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        int l = rr(nL);
        if (inS[l] || tabu[l] > it) continue;
        int remn = 0, ok = 1;
        for (int k = 0; k < dl[l] && ok; k++) {
            int r = al[l][k];
            if (load[r] < s) continue;
            int covered = 0;
            for (int j = 0; j < remn; j++) if (adjacent(rem[j], r)) { covered = 1; break; }
            if (covered) continue;
            int cand[MAXDEG], nc = 0;
            for (int q = 0; q < dr[r]; q++) {
                int y = ar[r][q];
                if (inS[y] && tabu[y] <= it) cand[nc++] = y;
            }
            if (nc == 0) {
                for (int q = 0; q < dr[r]; q++) {
                    int y = ar[r][q];
                    if (inS[y]) cand[nc++] = y;
                }
            }
            if (nc == 0) { ok = 0; break; }
            if (remn >= 2) { ok = 0; break; }
            rem[remn++] = cand[rr(nc)];
        }
        if (!ok) continue;
        if (remn == 2 && rr(8) != 0) continue;
        for (int j = 0; j < remn; j++) {
            take(rem[j]);
            tabu[rem[j]] = it + 5 + rr(10);
        }
        put(l);
        size += 1 - remn;
        if (size > best) {
            best = size;
            memcpy(bestS, inS, sizeof(int) * MAXV);
            last = it;
        }
        if (it - last > 30000) {
            for (int v = 0; v < nL; v++) if (inS[v]) take(v);
            for (int v = 0; v < nL; v++) tabu[v] = 0;
            size = 0;
            for (int v = 0; v < nL; v++) {
                if (bestS[v]) { put(v); size++; }
            }
            last = it;
        }
    }

    printf("%d\n", best);
    int first = 1;
    for (int v = 0; v < nL; v++) {
        if (bestS[v]) {
            printf(first ? "%d" : " %d", v);
            first = 0;
        }
    }
    printf("\n");
    (void)nR;
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
    """Run the C insertion engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


def _pack_side(m, pairs, s, seed, budget):
    """Choose left vertices (0..m-1) with at most s chosen neighbours per right vertex, via C tabu."""
    if budget < 0.3 or s < 1:
        return []
    edges = [(a, m + b) for a, b in pairs]
    try:
        out = lib.run_c(C_PACK, [m, s, seed, round(budget, 2)],
                        stdin_graph=(2 * m, edges), timeout=budget + 5.0)
        toks = out.split()
        k = int(toks[0])
        return [int(t) for t in toks[1:1 + k]]
    except Exception:
        return []


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
# A-side: a set SA of points; each SA point gets a new vertex joined to its
#         q+1 lines; each line holds <= s points of SA.
# B-side: a set SB of lines; each gets a new vertex joined to its q+1 points;
#         each point lies on <= s lines of SB.
# Diameter stays 3 for any SA, SB.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


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


def _saturate(n, edges, col, d, seed):
    """Greedily add spare edges between opposite colour classes. Only shortens paths, so validity is kept."""
    rng = random.Random(seed)
    deg = [0] * n
    es = set()
    for u, v in edges:
        es.add((min(u, v), max(u, v)))
        deg[u] += 1
        deg[v] += 1
    A = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    B = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in A for b in B]
    rng.shuffle(pairs)
    E = list(edges)
    for a, b in pairs:
        if deg[a] >= d or deg[b] >= d:
            continue
        key = (min(a, b), max(a, b))
        if key in es:
            continue
        es.add(key)
        deg[a] += 1
        deg[b] += 1
        E.append(key)
    return n, E


def _arc_bound(q, d):
    s = d - q - 1
    mm = q * q + q + 1
    return 2 * mm + 2 * s * mm // (q + 1)


def _arc_pack(q, d, seed, budget):
    """Arc-extended PG(2,q) graph with SA, SB chosen by C tabu (plus conic candidate), then saturated."""
    s = d - q - 1
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    if s >= 1:
        SA = _pack_side(m, [(p, L) for p in range(m) for L in point_lines[p]], s, seed, budget / 2)
        SB = _pack_side(m, [(L, p) for L in range(m) for p in line_points[L]], s, seed + 1, budget / 2)
    else:
        SA, SB = [], []
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
            SA = cs
        if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
            SB = cs
    if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
        return None
    n, E = _arc_graph(m, edges, point_lines, line_points, SA, SB)
    col = [0] * m + [1] * m + [0] * len(SA) + [1] * len(SB)
    return _saturate(n, E, col, d, seed)


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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver. Time plan (fractions of time_limit):
#   D = 3: arc graphs for the top prime powers q (tabu packing in C), with the
#          largest-budget share on the best bound; saturation adds spare edges.
#          Then C insertion on the two best graphs until 0.88.
#   D >= 4: GQ baseline, then C insertion on the fallback until 0.85.
# Fallback is K_{d,d}, which has diameter 2 and is valid for every D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        qs = sorted([q for q in range(2, d) if lib.is_prime_power(q)],
                    key=lambda q: -_arc_bound(q, d))[:3]
        fracs = [0.6, 0.2, 0.2]
        graphs = []
        for idx, q in enumerate(qs):
            if el() > 0.33 * time_limit:
                break
            budget = fracs[idx] * 0.33 * time_limit
            g = _arc_pack(q, d, seed + 31 * idx, budget)
            if g is not None:
                graphs.append(g)
        graphs.sort(key=lambda g: -g[0])
        for g in graphs:
            consider(g)
        for k, g in enumerate(graphs[:2]):
            rem = 0.88 * time_limit - el()
            if rem < 0.5:
                break
            share = rem / (2 - k)
            consider(_c_augment(g, d, D, seed + 17 * k, share))
    else:
        if D >= 4:
            consider(_best_gq(d))
        rem = 0.85 * time_limit - el()
        if rem >= 0.5:
            consider(_c_augment(best, d, D, seed, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
