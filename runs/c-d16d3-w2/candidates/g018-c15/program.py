import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: ruin-and-recreate local search with exact validity certificates.
#
# State: a bipartite graph on slots 0..cap-1. Some slots are active (vertices),
# the rest are free. Invariants kept after every accepted move:
#   * max degree <= d, every edge joins the two colour classes,
#   * every pair of active vertices is at distance <= D (checked with bitsets).
#
# Insertion certificate: a new vertex w of colour s joined to a set S of
# opposite-colour vertices is within distance D of every active x whenever x
# lies in the (D-1)-ball of some u in S. Adding vertices and cross edges never
# increases distances, so insertions keep validity.
#
# Moves:
#   * random cross edge plus greedy growth (valid by the certificate),
#   * local ruin: remove a BFS-local cluster of k vertices, then greedily
#     reinsert as many as possible. Accept if the vertex count does not drop
#     and the graph is still valid, otherwise restore a snapshot.
# The best state seen is printed (compacted to 0..n-1).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXS 1024
#define MAXD 64
#define MAXW (MAXS / 64)
#define MAXE 16384

static int cap, W, d, D;
static int deg[MAXS];
static int adj[MAXS][MAXD];
static int col[MAXS];
static int act[MAXS];
static uint64_t rb[MAXS][MAXW];
static uint64_t rf[MAXS][MAXW];
static uint64_t nxb[MAXS][MAXW];
static uint64_t amask[MAXW];

static int sdeg[MAXS], scol[MAXS], sact[MAXS];
static int sadj[MAXS][MAXD];
static int bdeg[MAXS], bact[MAXS];
static int badj[MAXS][MAXD];
static int bn;

static int eu[MAXE], ev[MAXE], ku[MAXE], kv[MAXE];
static int bfsq[MAXS];

static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void drop_half(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void remove_vertex(int x) {
    for (int i = 0; i < deg[x]; i++) drop_half(adj[x][i], x);
    deg[x] = 0;
    act[x] = 0;
}

static int n_active(void) {
    int c = 0;
    for (int v = 0; v < cap; v++) if (act[v]) c++;
    return c;
}

static void rebuild_amask(void) {
    for (int w = 0; w < W; w++) amask[w] = 0;
    for (int v = 0; v < cap; v++)
        if (act[v]) amask[v >> 6] |= 1ULL << (v & 63);
}

static void compute_balls(int R, uint64_t out[][MAXW]) {
    for (int v = 0; v < cap; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < cap; v++) {
            for (int w = 0; w < W; w++) nxb[v][w] = out[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxb[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < cap; v++)
            for (int w = 0; w < W; w++) out[v][w] = nxb[v][w];
    }
}

static int covers(const uint64_t *cov) {
    for (int w = 0; w < W; w++)
        if ((cov[w] & amask[w]) != amask[w]) return 0;
    return 1;
}

static int is_valid_state(void) {
    compute_balls(D, rf);
    for (int v = 0; v < cap; v++) {
        if (!act[v]) continue;
        for (int w = 0; w < W; w++)
            if ((rf[v][w] & amask[w]) != amask[w]) return 0;
    }
    return 1;
}

/* Insert one vertex; rb must hold the (D-1)-balls of the current graph. */
static int try_insert(void) {
    int slot = -1;
    for (int v = 0; v < cap; v++) if (!act[v]) { slot = v; break; }
    if (slot < 0) return 0;
    int s0 = (int)(rnd() & 1u);
    for (int k = 0; k < 2; k++) {
        int s = s0 ^ k;
        int cand[MAXS];
        int nc = 0;
        for (int u = 0; u < cap; u++)
            if (act[u] && col[u] == 1 - s && deg[u] < d) cand[nc++] = u;
        if (nc == 0) continue;
        for (int i = nc - 1; i > 0; i--) {
            int j = (int)(rnd() % (uint32_t)(i + 1));
            int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
        }
        unsigned char taken[MAXS];
        memset(taken, 0, sizeof taken);
        uint64_t cov[MAXW];
        for (int w = 0; w < W; w++) cov[w] = 0;
        int chosen[MAXD];
        int nch = 0;
        while (nch < d && !covers(cov)) {
            int bi = -1, bg = 0;
            for (int i = 0; i < nc; i++) {
                if (taken[i]) continue;
                int u = cand[i];
                int g = 0;
                for (int w = 0; w < W; w++)
                    g += popc64(rb[u][w] & amask[w] & ~cov[w]);
                if (g > bg) { bg = g; bi = i; }
            }
            if (bi < 0) break;
            taken[bi] = 1;
            chosen[nch++] = cand[bi];
            for (int w = 0; w < W; w++) cov[w] |= rb[cand[bi]][w];
        }
        if (!covers(cov)) continue;
        act[slot] = 1;
        col[slot] = s;
        deg[slot] = 0;
        for (int i = 0; i < nch; i++) add_edge(chosen[i], slot);
        rebuild_amask();
        return 1;
    }
    return 0;
}

static void grow(int maxins) {
    for (int t = 0; t < maxins; t++) {
        compute_balls(D - 1, rb);
        if (!try_insert()) break;
    }
}

static int random_active(void) {
    for (int t = 0; t < 100000; t++) {
        int v = (int)(rnd() % (uint32_t)cap);
        if (act[v]) return v;
    }
    return -1;
}

static int try_random_edge(void) {
    for (int t = 0; t < 60; t++) {
        int u = (int)(rnd() % (uint32_t)cap);
        int v = (int)(rnd() % (uint32_t)cap);
        if (!act[u] || !act[v] || col[u] == col[v]) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
        return 1;
    }
    return 0;
}

/* Remove a BFS-local cluster of up to k active vertices around a random vertex. */
static int ruin_local(int k) {
    static unsigned char seen[MAXS];
    static int out[MAXS];
    int x = random_active();
    if (x < 0) return 0;
    memset(seen, 0, sizeof seen);
    int qh = 0, qt = 0, cnt = 0;
    bfsq[qt++] = x;
    seen[x] = 1;
    while (qh < qt && cnt < k) {
        int u = bfsq[qh++];
        out[cnt++] = u;
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (!seen[v]) { seen[v] = 1; bfsq[qt++] = v; }
        }
    }
    for (int i = 0; i < cnt; i++) remove_vertex(out[i]);
    rebuild_amask();
    return cnt;
}

static void snapshot(void) {
    memcpy(sdeg, deg, sizeof(int) * cap);
    memcpy(sadj, adj, sizeof(int) * MAXD * cap);
    memcpy(scol, col, sizeof(int) * cap);
    memcpy(sact, act, sizeof(int) * cap);
}

static void restore(void) {
    memcpy(deg, sdeg, sizeof(int) * cap);
    memcpy(adj, sadj, sizeof(int) * MAXD * cap);
    memcpy(col, scol, sizeof(int) * cap);
    memcpy(act, sact, sizeof(int) * cap);
    rebuild_amask();
}

static void store_best(void) {
    memcpy(bdeg, deg, sizeof(int) * cap);
    memcpy(badj, adj, sizeof(int) * MAXD * cap);
    memcpy(bact, act, sizeof(int) * cap);
    bn = n_active();
}

static void print_best(void) {
    static int idx[MAXS];
    int n = 0, m = 0;
    for (int v = 0; v < cap; v++) {
        if (bact[v]) idx[v] = n++;
        else idx[v] = -1;
    }
    for (int u = 0; u < cap; u++) {
        if (!bact[u]) continue;
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) m++;
    }
    printf("%d %d\n", n, m);
    for (int u = 0; u < cap; u++) {
        if (!bact[u]) continue;
        for (int i = 0; i < bdeg[u]; i++) {
            int v = badj[u][i];
            if (v > u) printf("%d %d\n", idx[u], idx[v]);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXS - 16) { printf("0 0\n"); return 0; }

    int ne = 0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (ne < MAXE) { eu[ne] = u; ev[ne] = v; ne++; }
    }

    cap = N0 + 48;
    if (cap > MAXS) cap = MAXS;
    W = (cap + 63) >> 6;

    for (int v = 0; v < cap; v++) { deg[v] = 0; col[v] = -1; act[v] = 0; }
    for (int i = 0; i < ne; i++) {
        int u = eu[i], v = ev[i];
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    for (int s = 0; s < N0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        bfsq[qt++] = s;
        while (qh < qt) {
            int u = bfsq[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    bfsq[qt++] = v;
                }
            }
        }
    }
    int nk = 0;
    for (int u = 0; u < N0; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (u < v && col[u] != col[v] && nk < MAXE) {
                ku[nk] = u; kv[nk] = v; nk++;
            }
        }
    for (int u = 0; u < N0; u++) deg[u] = 0;
    for (int i = 0; i < nk; i++) add_edge(ku[i], kv[i]);
    for (int v = 0; v < cap; v++) {
        if (v < N0) { act[v] = 1; if (col[v] < 0) col[v] = 0; }
        else { act[v] = 0; col[v] = 0; }
    }
    rebuild_amask();
    if (!is_valid_state()) { printf("0 0\n"); return 0; }

    store_best();
    clock_t t0 = clock();
    while (1) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        snapshot();
        int nold = n_active();
        if (rnd() % 100 < 15) {
            try_random_edge();
            grow(2);
            if (!is_valid_state()) restore();
        } else {
            int k = 1 + (int)(rnd() % 4u);
            int r = ruin_local(k);
            grow(r + 1);
            int nnew = n_active();
            if (nnew < nold || !is_valid_state()) restore();
        }
        if (n_active() > bn) store_best();
    }
    print_best();
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
    """Run the C ruin-and-recreate engine from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d < 2 or d > 64 or D < 2:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1.
#
# A-side: a set SA of points; each P in SA gets a new vertex joined to the q+1
# lines through P. Every line may hold at most s points of SA.
# B-side: a set SB of lines; each j in SB gets a new vertex joined to the q+1
# points on j. Every point may lie on at most s lines of SB.
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


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nx = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nx.append(v)
            count += len(nx)
            frontier = nx
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver. Time plan (fractions of time_limit):
#   0.00-0.10  arc-extended PG graphs (A and B sets chosen independently)
#   0.10-0.55  C ruin-and-recreate search from the best graph so far
#   0.55-0.72  generalized quadrangle baseline and annealed group lifts (D >= 4)
#   0.72-0.88  second C search round from the best graph
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def at(frac):
        return start + frac * time_limit

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, at(0.10), random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs:
            consider(g)

    if D >= 2:
        consider(_c_augment(best, d, D, seed, at(0.55) - time.monotonic() - 1.0))

    if D >= 4 and time.monotonic() < at(0.55):
        consider(_best_gq(d))

    if D >= 4:
        anneal_end = at(0.72)
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

    if D >= 2:
        consider(_c_augment(best, d, D, seed + 1, at(0.88) - time.monotonic() - 1.0))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
