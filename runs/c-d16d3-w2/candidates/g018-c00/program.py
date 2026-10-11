import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: fixed-size repair by simulated annealing, plus greedy vertex growth.
#
# The cost is the number of unordered vertex pairs at distance > D. Growth step:
#   1. attach a new vertex greedily (ball-cover heuristic, radius D-1 balls),
#   2. anneal with degree-preserving double-edge swaps and spare-edge additions
#      until the cost is zero,
#   3. on success keep the larger graph, on failure restore the snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t tmpb[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static double budget_s;
static clock_t t0;
static State best_s, snap_s;
static int un_cnt;
static int un_v[4], un_deg[4];
static int un_row[4][MAXD];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 11);
}

static double rndu(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static int time_up(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC > budget_s;
}

static int popc(uint64_t x) {
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

static void replace_nb(int a, int old, int nw) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == old) { adj[a][i] = nw; return; }
    }
}

static void compute_balls(int R) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) tmpb[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) tmpb[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = tmpb[v][w];
    }
}

static long bad_pairs(void) {
    compute_balls(D);
    long tot = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) tot += popc(reach[v][w]);
    return ((long)n * n - tot) / 2;
}

static void st_save(State *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(adj));
    memcpy(s->col, col, sizeof(int) * (size_t)n);
}

static void st_load(const State *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(adj));
    memcpy(col, s->col, sizeof(int) * (size_t)n);
}

static void un_save(int v) {
    un_v[un_cnt] = v;
    un_deg[un_cnt] = deg[v];
    memcpy(un_row[un_cnt], adj[v], sizeof(int) * MAXD);
    un_cnt++;
}

static void un_undo(void) {
    for (int k = un_cnt - 1; k >= 0; k--) {
        int v = un_v[k];
        deg[v] = un_deg[k];
        memcpy(adj[v], un_row[k], sizeof(int) * MAXD);
    }
    un_cnt = 0;
}

/* side-vertex picker: need_spare=1 wants deg<d, otherwise deg>0 */
static int pick_vertex(int side, int need_spare) {
    for (int t = 0; t < 64; t++) {
        int v = (int)(rnd() % (uint32_t)n);
        if (col[v] == side && (need_spare ? deg[v] < d : deg[v] > 0)) return v;
    }
    int cnt = 0, pick = -1;
    for (int v = 0; v < n; v++) {
        if (col[v] == side && (need_spare ? deg[v] < d : deg[v] > 0)) {
            cnt++;
            if (rnd() % (uint32_t)cnt == 0) pick = v;
        }
    }
    return pick;
}

/* double-edge swap: u-v, x-y  ->  u-y, x-v, with u,x on one side */
static int move_swap(void) {
    int side = (int)(rnd() & 1u);
    int u = pick_vertex(side, 0);
    if (u < 0) return 0;
    int v = adj[u][(int)(rnd() % (uint32_t)deg[u])];
    int x = pick_vertex(side, 0);
    if (x < 0 || x == u) return 0;
    int y = adj[x][(int)(rnd() % (uint32_t)deg[x])];
    if (v == y || has_edge(u, y) || has_edge(x, v)) return 0;
    un_cnt = 0;
    un_save(u); un_save(v); un_save(x); un_save(y);
    replace_nb(u, v, y);
    replace_nb(v, u, x);
    replace_nb(x, y, v);
    replace_nb(y, x, u);
    return 1;
}

/* add a cross edge between two spare vertices */
static int move_add(void) {
    int a = pick_vertex(0, 1);
    if (a < 0) return 0;
    int b = pick_vertex(1, 1);
    if (b < 0) return 0;
    if (has_edge(a, b)) return 0;
    un_cnt = 0;
    un_save(a); un_save(b);
    add_edge(a, b);
    return 1;
}

static int anneal(long maxit, double T0, double T1) {
    long cur = bad_pairs();
    if (cur == 0) return 1;
    for (long it = 0; it < maxit; it++) {
        if ((it & 31) == 0 && time_up()) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);
        int ok = ((rnd() % 100u) < 20u) ? move_add() : move_swap();
        if (!ok) continue;
        long c2 = bad_pairs();
        long delta = c2 - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            un_undo();
        }
    }
    return 0;
}

/* greedy attach of a new vertex on `side`; neighbours chosen by ball cover */
static int greedy_attach(int side) {
    if (n + 1 > MAXN - 2) return 0;
    compute_balls(D - 1);
    static int cand[MAXN];
    static int used[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++) {
        used[u] = 0;
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    }
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(cov));
    int chosen[MAXD];
    int nch = 0;
    while (nch < d) {
        int bestu = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; bestu = u; }
        }
        if (bestu < 0) break;
        used[bestu] = 1;
        chosen[nch++] = bestu;
        for (int w = 0; w < W; w++) cov[w] |= reach[bestu][w];
    }
    for (int i = 0; i < nc && nch < d; i++) {
        int u = cand[i];
        if (!used[u]) { used[u] = 1; chosen[nch++] = u; }
    }
    if (nch == 0) return 0;
    int w = n;
    n++;
    W = (n + 63) >> 6;
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
    budget_s = atof(argv[4]);
    long iters = (argc > 5) ? atol(argv[5]) : 1500;
    if (iters < 10) iters = 10;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd();
    t0 = clock();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0 = 0, M0 = 0;
    if (scanf("%d %d", &N0, &M0) != 2) { N0 = 0; M0 = 0; }
    if (N0 < 1 || N0 > MAXN - 2) { printf("0 0\n"); return 0; }
    n = N0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* bipartition by BFS; reject non-bipartite input */
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
                if (col[v] < 0) { col[v] = 1 - col[u]; queue[qt++] = v; }
            }
        }
    }
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (col[adj[u][i]] == col[u]) { printf("0 0\n"); return 0; }

    /* repair the start graph to cost zero if needed */
    if (!anneal(2000000L, 1.0, 0.05)) { printf("0 0\n"); return 0; }
    st_save(&best_s);

    int fails = 0;
    while (!time_up() && fails < 30 && n < MAXN - 2) {
        st_save(&snap_s);
        int side = (int)(rnd() & 1u);
        int added = greedy_attach(side);
        if (!added) added = greedy_attach(1 - side);
        if (!added) break;
        if (anneal(iters, 1.0, 0.05)) {
            st_save(&best_s);
            fails = 0;
        } else {
            st_load(&snap_s);
            fails++;
        }
    }

    int m2 = 0;
    for (int u = 0; u < best_s.n; u++)
        for (int i = 0; i < best_s.deg[u]; i++)
            if (best_s.adj[u][i] > u) m2++;
    printf("%d %d\n", best_s.n, m2);
    for (int u = 0; u < best_s.n; u++)
        for (int i = 0; i < best_s.deg[u]; i++)
            if (best_s.adj[u][i] > u) printf("%d %d\n", u, best_s.adj[u][i]);
    return 0;
}
"""


def _c_engine(graph, d, D, seed, budget):
    """Run the C repair/growth engine from graph; return (n, edges) or None on failure."""
    if graph is None or budget < 0.5 or d > 32:
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit <= s times."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc."""
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 5).
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


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
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
#   D == 2          : K_{d,d}
#   D == 3          : arc-extended PG graphs (best one is the C start)
#   D == 4          : generalized quadrangle W(q)
#   D >= 5          : voltage-lift annealing up to 0.35
#   D >= 3          : C repair/growth engine from the best graph up to 0.85
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

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit,
                               random.Random(seed * 7919 + d))
        for g in arcs:
            consider(g)

    if D == 4 and elapsed() < 0.10 * time_limit:
        consider(_best_gq(d))

    if D >= 5:
        anneal_end = start + 0.35 * time_limit
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal_lift(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

    if D >= 3:
        budget = 0.85 * time_limit - elapsed()
        if budget > 1.0:
            consider(_c_engine(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
