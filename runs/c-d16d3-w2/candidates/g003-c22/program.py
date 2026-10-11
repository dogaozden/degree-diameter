import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion plus ruin-and-recreate.
#
# Insertion: a new vertex w on one colour class, joined to a set N of vertices
# on the other class, keeps the graph valid when the (D-1)-balls of N cover
# every vertex. Adding edges between colour classes never increases distances,
# so validity is preserved by these moves.
#
# Ruin-and-recreate (new in this version): remove 1-2 random vertices. The
# removal can break pairs that were only linked through them. Repair greedily
# adds cross edges between vertices with spare degree, keeping an edge only if
# the number of bad (distance > D) pairs drops. If the graph is valid again,
# fill it with insertions. Accept if the vertex count grows, or ties by a coin
# flip (this lets the structure drift on plateaus). The best graph is printed.
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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

static State cur, saved, best, tmp;
static int d, D, W;
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

static int has_edge(const State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(State *s, int u, int v) {
    s->adj[u][s->deg[u]++] = v;
    s->adj[v][s->deg[v]++] = u;
}

static void del_arc(State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) {
        if (s->adj[u][i] == v) {
            s->adj[u][i] = s->adj[u][--s->deg[u]];
            return;
        }
    }
}

static void remove_edge(State *s, int u, int v) {
    del_arc(s, u, v);
    del_arc(s, v, u);
}

static void copy_state(State *dst, const State *src) {
    int n = src->n;
    dst->n = n;
    memcpy(dst->deg, src->deg, sizeof(int) * n);
    memcpy(dst->col, src->col, sizeof(int) * n);
    for (int i = 0; i < n; i++)
        memcpy(dst->adj[i], src->adj[i], sizeof(int) * src->deg[i]);
}

static void compute_balls(int R) {
    int n = cur.n;
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < cur.deg[v]; i++) {
                int u = cur.adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

/* Number of ordered-or-unordered-free bad pairs: sum over v of vertices not within D. */
static long bad_count(void) {
    compute_balls(D);
    int n = cur.n;
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(reach[v][w]);
        bad += n - c;
    }
    return bad;
}

static int covers_all(const uint64_t *cov) {
    int n = cur.n;
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

/* Requires reach computed with R = D-1 for the current graph. */
static int try_insert(int side) {
    static int cand[MAXN], used[MAXN];
    int n = cur.n, nc = 0;
    for (int u = 0; u < n; u++)
        if (cur.col[u] == 1 - side && cur.deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    int chosen[MAXD], nch = 0;
    while (nch < d && !covers_all(cov)) {
        int bu = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; bu = u; }
        }
        if (bu < 0) break;
        used[bu] = 1;
        chosen[nch++] = bu;
        for (int w = 0; w < W; w++) cov[w] |= reach[bu][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    cur.n = n + 1;
    cur.col[w] = side;
    cur.deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(&cur, chosen[i], w);
    return 1;
}

static void fill(int maxfails) {
    int fails = 0;
    while (fails < maxfails && cur.n < MAXN - 1) {
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int n = cur.n;
            int u = (int)(rnd() % (uint32_t)n);
            int v = (int)(rnd() % (uint32_t)n);
            if (u == v || cur.col[u] == cur.col[v]) continue;
            if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(&cur, u, v)) continue;
            add_edge(&cur, u, v);
            break;
        }
    }
}

/* Delete the vertices flagged in gone[] from cur, renumbering the rest. */
static void remove_set(const int *gone) {
    static int map[MAXN];
    int n = cur.n, k = 0;
    for (int i = 0; i < n; i++) map[i] = gone[i] ? -1 : k++;
    tmp.n = k;
    for (int i = 0; i < n; i++) {
        int j = map[i];
        if (j < 0) continue;
        tmp.col[j] = cur.col[i];
        tmp.deg[j] = 0;
        for (int e = 0; e < cur.deg[i]; e++) {
            int u = cur.adj[i][e];
            if (map[u] >= 0) tmp.adj[j][tmp.deg[j]++] = map[u];
        }
    }
    copy_state(&cur, &tmp);
}

static void output_state(const State *s) {
    int m2 = 0;
    for (int u = 0; u < s->n; u++)
        for (int i = 0; i < s->deg[u]; i++)
            if (s->adj[u][i] > u) m2++;
    printf("%d %d\n", s->n, m2);
    for (int u = 0; u < s->n; u++)
        for (int i = 0; i < s->deg[u]; i++)
            if (s->adj[u][i] > u) printf("%d %d\n", u, s->adj[u][i]);
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
    if (N0 < 1 || N0 > MAXN - 1) { printf("0 0\n"); return 0; }
    cur.n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(&cur, u, v)) continue;
        add_edge(&cur, u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < N0; s++) cur.col[s] = -1;
    for (int s = 0; s < N0; s++) {
        if (cur.col[s] >= 0) continue;
        cur.col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < cur.deg[u]; i++) {
                int v = cur.adj[u][i];
                if (cur.col[v] < 0) {
                    cur.col[v] = 1 - cur.col[u];
                    queue[qt++] = v;
                }
            }
        }
    }

    if (bad_count() != 0) { output_state(&cur); return 0; }

    fill(200);
    copy_state(&saved, &cur);
    copy_state(&best, &cur);

    static int gone[MAXN], spare[MAXN];
    clock_t t0 = clock();
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < budget) {
        copy_state(&cur, &saved);
        int n = cur.n;
        if (n < 8) break;

        /* Ruin: remove one or two random vertices. */
        for (int i = 0; i < n; i++) gone[i] = 0;
        int r = 1 + (int)(rnd() % 2u);
        for (int k = 0; k < r; k++) gone[rnd() % (uint32_t)n] = 1;
        remove_set(gone);

        /* Repair: greedily add spare-degree cross edges while bad pairs drop. */
        long bad = bad_count();
        for (int tries = 0; bad > 0 && tries < 120; tries++) {
            int ns = 0;
            for (int i = 0; i < cur.n; i++)
                if (cur.deg[i] < d) spare[ns++] = i;
            if (ns < 2) break;
            int u = spare[rnd() % (uint32_t)ns];
            int v = spare[rnd() % (uint32_t)ns];
            if (u == v || cur.col[u] == cur.col[v] || has_edge(&cur, u, v)) continue;
            add_edge(&cur, u, v);
            long nb = bad_count();
            if (nb < bad) bad = nb;
            else remove_edge(&cur, u, v);
        }

        /* Recreate: if valid again, refill with insertions and accept if not worse. */
        if (bad == 0) {
            fill(30);
            if (bad_count() == 0) {
                int better = cur.n > saved.n || (cur.n == saved.n && (rnd() & 1u));
                if (better) {
                    copy_state(&saved, &cur);
                    if (cur.n > best.n) copy_state(&best, &cur);
                }
            }
        }
    }

    output_state(&best);
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
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
#   0.10-0.40  generalized quadrangle baseline (D >= 4)
#   up to 0.86 (D = 3) or 0.55 (D >= 4): C insertion + ruin-and-recreate
#   D >= 4 only: annealed group voltage lifts until 0.86
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

    if D >= 4 and elapsed() < 0.40 * time_limit:
        consider(_best_gq(d))

    # Ruin-and-recreate / insertion engine on the best graph so far.
    c_end = (0.86 if D == 3 else 0.55) * time_limit
    rem = c_end - elapsed() - 0.5
    if rem >= 0.5:
        consider(_c_augment(best, d, D, seed, rem))

    if D >= 4:
        anneal_end = start + 0.86 * time_limit
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
