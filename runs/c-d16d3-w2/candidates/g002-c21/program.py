import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on a bipartite graph with fixed sides.
#
# Cost = number of unordered vertex pairs at distance > D. Moves keep max degree
# <= d and bipartiteness: rewire (a-b -> a-w), add edge, remove edge.
# Whenever cost reaches 0 the current graph is saved and a new vertex is grown
# and attached greedily (each step picks the neighbour that minimises the cost).
# If the search stagnates, it restores the best saved graph and grows again.
# It always prints its best valid graph; Python re-checks it with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18
#define DCAP 32
#define MAXE (MAXN * 16 + 16)

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestU[MAXE], bestV[MAXE], bestSide[MAXN];
static int best_n = 0, best_m = 0;
static uint64_t rs = 1;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

static long bad_pairs(void) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(RA[v]));
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur; cur = nxt; nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        bestSide[u] = side[u];
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (v > u && m < MAXE) { bestU[m] = u; bestV[m] = v; m++; }
        }
    }
    best_n = n; best_m = m;
}

static void restore_best(void) {
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) adjm[u][nb[u][i]] = 0;
        deg[u] = 0;
    }
    n = best_n;
    for (int v = 0; v < n; v++) side[v] = bestSide[v];
    for (int i = 0; i < best_m; i++) add_edge(bestU[i], bestV[i]);
}

/* Add a new vertex on a random side, attached greedily: each step adds the
   opposite-side neighbour that gives the smallest cost. */
static int grow_vertex(void) {
    if (n >= MAXN - 2) return 0;
    int w = n++;
    side[w] = rint_(2);
    deg[w] = 0;
    int off = rint_(n - 1);
    for (int k = 0; k < d; k++) {
        long bb = -1;
        int bc = -1;
        int evald = 0;
        for (int t = 0; t < n - 1 && evald < 80; t++) {
            int c = (t + off) % (n - 1);
            if (side[c] == side[w] || deg[c] >= d || adjm[w][c]) continue;
            add_edge(w, c);
            long b = bad_pairs();
            del_edge(w, c);
            evald++;
            if (bc < 0 || b < bb) { bb = b; bc = c; }
        }
        if (bc < 0) break;
        add_edge(w, bc);
    }
    return 1;
}

static int pick_nonisolated(void) {
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (deg[c] > 0) return c;
    }
    return -1;
}

/* a-b becomes a-w, where w is on the same side as b. */
static int move_rewire(int *ua, int *ub, int *uw) {
    int a = pick_nonisolated();
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    int w = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != b && side[c] == side[b] && deg[c] < d && !adjm[a][c]) { w = c; break; }
    }
    if (w < 0) return 0;
    del_edge(a, b);
    add_edge(a, w);
    *ua = a; *ub = b; *uw = w;
    return 1;
}

static int move_add(int *ua, int *ub) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (deg[c] < d) { x = c; break; }
    }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *ua = x; *ub = y;
    return 1;
}

static int move_remove(int *ua, int *ub) {
    int a = pick_nonisolated();
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    *ua = a; *ub = b;
    return 1;
}

static int color_and_clean(void) {
    static int q[MAXN];
    static int vis[MAXN];
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; q[qt++] = v; }
            }
        }
    }
    /* drop any edge that joins equal sides (only if the input was not bipartite) */
    for (int u = 0; u < n; u++) {
        int again = 1;
        while (again) {
            again = 0;
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (side[v] == side[u]) { del_edge(u, v); again = 1; break; }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    clock_t t0 = clock();

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || n < 1 || m0 < 0 || n > MAXN - 64 ||
        d < 1 || d > DCAP || D < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (adjm[u][v] || deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }
    color_and_clean();

    long bad = bad_pairs();
    int have_best = 0;
    if (bad == 0) { save_best(); have_best = 1; }

    const long PH = 30000, STAG = 40000;
    long it = 0, last_imp = 0;
    for (;;) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (bad == 0) {
            save_best(); have_best = 1; last_imp = it;
            if (n >= MAXN - 2) break;
            grow_vertex();
            bad = bad_pairs();
            continue;
        }
        if (have_best && it - last_imp > STAG) {
            restore_best();
            bad = bad_pairs();
            last_imp = it;
            continue;
        }

        double phase = (double)(it % PH) / (double)PH;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);

        int kind, ua = 0, ub = 0, uw = 0, ok;
        int r = rint_(100);
        if (r < 55) { kind = 0; ok = move_rewire(&ua, &ub, &uw); }
        else if (r < 90) { kind = 1; ok = move_add(&ua, &ub); }
        else { kind = 2; ok = move_remove(&ua, &ub); }
        if (!ok) continue;

        long nbad = bad_pairs();
        long delta = nbad - bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            bad = nbad;
        } else {
            if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
            else if (kind == 1) { del_edge(ua, ub); }
            else { add_edge(ua, ub); }
        }
    }

    if (!have_best) save_best();
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. With d >= q+1 each vertex has spare capacity
# s = d - q - 1. Choose SA (points) so each line holds <= s points of SA, and
# SB (lines) so each point lies on <= s lines of SB. Add one A-vertex per P in SA
# (joined to the q+1 lines through P) and one B-vertex per line j in SB (joined
# to the q+1 points on j). SA and SB are chosen independently.
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


def _loads_ok(S, s, nbr, m):
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so every target is hit at most s times; returns the largest found."""
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
    """PG incidence plus one A-vertex per SA point and one B-vertex per SB line."""
    na, nb_ = len(SA), len(SB)
    n = 2 * m + na + nb_
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
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 30, deadline)
        SB = _greedy_side(m, s, line_points, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, point_lines, m):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, line_points, m):
                SB = cs
        if not (_loads_ok(SA, s, point_lines, m) and _loads_ok(SB, s, line_points, m)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
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
# C wrapper and build.
# ----------------------------------------------------------------------------

def _c_grow(graph, d, D, seed, budget):
    """Run the C annealer from graph; return (n, edges) or None on failure."""
    if graph is None or budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 4.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit - 1.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    try:
        if D == 3:
            for g in _arc_extensions(d, t0 + 0.12 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    # Voltage-lift annealing for D >= 4 (a share of the budget).
    if D >= 4 and time.monotonic() < end:
        vend = time.monotonic() + 0.35 * (end - time.monotonic())
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < vend:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, vend, iters=400)
            if res is not None:
                consider(res)

    # Grow the best valid graph with the C engine (skip if already at Moore bound).
    budget = end - time.monotonic()
    if budget >= 1.0 and best[0] < lib.moore_bound(d, D):
        consider(_c_grow(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
