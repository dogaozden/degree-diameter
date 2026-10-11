import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion, then ruin-and-recreate local search.
#
# Insertion rule: a new vertex w joined to a set N of opposite-colour vertices
# is within distance D of every alive vertex x lying in the (D-1)-ball of some
# u in N. Adding edges never increases distances, so greedy insertion keeps a
# valid graph valid.
#
# Ruin-and-recreate (new in this version): remove 1 or 2 random alive vertices,
# then try to re-insert one more vertex than were removed. The move is kept only
# if the whole graph is still valid (exact check with D-balls as bitsets) and the
# vertex count does not drop. Otherwise the saved state is restored. Plateau
# moves (equal count) let the search drift between different spare-degree
# patterns, which the pure greedy insertion cannot do.
# Vertices are kept in fixed slots; removed slots are reused for insertions.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define MAXW (MAXN / 64)

typedef struct {
    int S, nalive;
    int alive[MAXN];
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Snap;

static int S, nalive, d, D, W;
static int alive[MAXN];
static int col[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t amask[MAXW];
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static double budget;
static Snap cur_snap, best_snap;

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

static double elapsed(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_from(int u, int x) {
    for (int j = 0; j < deg[u]; j++) {
        if (adj[u][j] == x) {
            adj[u][j] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void mask_set(int w) { amask[w >> 6] |= 1ULL << (w & 63); }
static void mask_clear(int w) { amask[w >> 6] &= ~(1ULL << (w & 63)); }

static void mask_build(void) {
    memset(amask, 0, sizeof amask);
    for (int v = 0; v < S; v++) if (alive[v]) mask_set(v);
}

static void compute_balls(int R) {
    W = (S + 63) >> 6;
    for (int v = 0; v < S; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < S; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < S; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static int covers(const uint64_t *cov) {
    for (int w = 0; w < W; w++)
        if ((cov[w] & amask[w]) != amask[w]) return 0;
    return 1;
}

static int try_insert(int side) {
    static int cand[MAXN];
    static char used[MAXN];
    static int chosen[MAXD];
    uint64_t cov[MAXW];
    int nc = 0;
    W = (S + 63) >> 6;
    for (int u = 0; u < S; u++)
        if (alive[u] && col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < nc; i++) used[cand[i]] = 0;
    for (int w = 0; w < W; w++) cov[w] = 0;
    int nch = 0;
    while (nch < d && !covers(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++)
                g += popc(reach[u][w] & amask[w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers(cov)) return 0;
    int w = -1;
    for (int i = 0; i < S; i++) if (!alive[i]) { w = i; break; }
    if (w < 0) {
        if (S >= MAXN) return 0;
        w = S;
        S++;
    }
    alive[w] = 1;
    col[w] = side;
    deg[w] = 0;
    nalive++;
    mask_set(w);
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static void remove_vertex(int x) {
    for (int i = 0; i < deg[x]; i++) del_from(adj[x][i], x);
    deg[x] = 0;
    alive[x] = 0;
    nalive--;
    mask_clear(x);
}

static void random_edge(void) {
    for (int t = 0; t < 50; t++) {
        int u = (int)(rnd() % (uint32_t)S);
        int v = (int)(rnd() % (uint32_t)S);
        if (u == v || !alive[u] || !alive[v] || col[u] == col[v]) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
        return;
    }
}

static void snap_save(Snap *s) {
    s->S = S;
    s->nalive = nalive;
    memcpy(s->alive, alive, sizeof(int) * S);
    memcpy(s->col, col, sizeof(int) * S);
    memcpy(s->deg, deg, sizeof(int) * S);
    memcpy(s->adj, adj, sizeof(int) * MAXD * S);
}

static void snap_load(const Snap *s) {
    S = s->S;
    nalive = s->nalive;
    memcpy(alive, s->alive, sizeof(int) * S);
    memcpy(col, s->col, sizeof(int) * S);
    memcpy(deg, s->deg, sizeof(int) * S);
    memcpy(adj, s->adj, sizeof(int) * MAXD * S);
    mask_build();
}

static int full_valid(void) {
    compute_balls(D);
    for (int v = 0; v < S; v++) {
        if (!alive[v]) continue;
        for (int w = 0; w < W; w++)
            if ((reach[v][w] & amask[w]) != amask[w]) return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    S = N0;
    nalive = N0;
    for (int i = 0; i < N0; i++) { alive[i] = 1; deg[i] = 0; }
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < S; s++) col[s] = -1;
    for (int s = 0; s < S; s++) {
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
    mask_build();

    t0 = clock();

    /* Phase 1: greedy insertion with random spare-edge perturbation. */
    int fails = 0;
    while (fails < 200 && elapsed() < 0.30 * budget) {
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        random_edge();
    }

    /* Phase 2: ruin-and-recreate with exact validity check. */
    snap_save(&best_snap);
    int best_n = nalive;
    while (elapsed() < budget) {
        if (nalive < 3) break;
        if (rnd() % 4u == 0) random_edge();
        snap_save(&cur_snap);
        int before = nalive;
        int k = 1 + (int)(rnd() % 2u);
        for (int r = 0; r < k; r++) {
            int x = -1;
            for (int t = 0; t < 100000; t++) {
                int c = (int)(rnd() % (uint32_t)S);
                if (alive[c]) { x = c; break; }
            }
            if (x >= 0) remove_vertex(x);
        }
        for (int a = 0; a < k + 1; a++) {
            compute_balls(D - 1);
            int side = (int)(rnd() & 1u);
            if (!try_insert(side))
                if (!try_insert(1 - side)) break;
        }
        if (nalive >= before && full_valid()) {
            if (nalive > best_n) {
                best_n = nalive;
                snap_save(&best_snap);
            }
        } else {
            snap_load(&cur_snap);
        }
    }

    /* Output the best valid state with compacted labels. */
    Snap *b = &best_snap;
    static int mp[MAXN];
    int n2 = 0, m2 = 0;
    for (int v = 0; v < b->S; v++) mp[v] = b->alive[v] ? n2++ : -1;
    for (int v = 0; v < b->S; v++) {
        if (!b->alive[v]) continue;
        for (int i = 0; i < b->deg[v]; i++)
            if (b->adj[v][i] > v) m2++;
    }
    printf("%d %d\n", n2, m2);
    for (int v = 0; v < b->S; v++) {
        if (!b->alive[v]) continue;
        for (int i = 0; i < b->deg[v]; i++) {
            int u = b->adj[v][i];
            if (u > v) printf("%d %d\n", mp[v], mp[u]);
        }
    }
    return 0;
}
"""


def _c_search(graph, d, D, seed, budget):
    """Run the C engine on graph; return (n, edges) or None on any failure."""
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
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
#   0.10-0.30  generalized quadrangle baseline (D >= 4) and, for D >= 4, annealed lifts
#   0.30-0.45  annealed group voltage lifts (D >= 4 only)
#   0.45-0.90  C engine: greedy insertion, then ruin-and-recreate on the best graph
# For D = 3 the annealing is skipped so the C search gets the time.
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

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs:
            consider(g)

    if D >= 4 and elapsed() < 0.30 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if D >= 4:
        anneal_end = start + 0.45 * time_limit
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

    if D >= 3:
        rem = 0.90 * time_limit - 2.0 - elapsed()
        if rem >= 0.5:
            consider(_c_search(best, d, D, seed, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
