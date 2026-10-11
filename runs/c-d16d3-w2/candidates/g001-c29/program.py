import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex insertion with annealed repair.
#
# Starting from a valid bipartite graph, add one vertex on a random side,
# attach it greedily, then anneal over degree-preserving rewires (move one end
# of an edge to another vertex on the same side) and free-capacity edge
# additions until the number of pairs at distance > D is zero. Each success
# becomes the new base; a failed attempt is discarded and restarted from the
# base. Cost is computed exactly with bitset ball expansion, so every output
# graph is valid by construction. Python re-checks it with lib.is_valid anyway.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define WMAX 18
#define MAXDEG 31
#define EMAX 17100
#define ITERS 20000

typedef struct {
    int n;
    int m;
    int side[MAXN];
    int eu[EMAX];
    int ev[EMAX];
} Snap;

static int N, DCAP, DIAM;
static int side[MAXN];
static int deg[MAXN];
static int adjl[MAXN][MAXDEG];
static unsigned char A[MAXN][MAXN];
static uint64_t RB[2][MAXN][WMAX];
static uint64_t rs = 88172645463325252ULL;
static Snap base_s;
static double deadline_sec = 1e9;
static int queue_buf[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_sec(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM (unreachable counts). */
static long long cost_fn(void) {
    int W = (N + 63) / 64;
    int cur = 0;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) RB[0][v][w] = 0;
        RB[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        int nx = cur ^ 1;
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) {
                uint64_t x = RB[cur][v][w];
                for (int k = 0; k < deg[v]; k++) x |= RB[cur][adjl[v][k]][w];
                RB[nx][v][w] = x;
            }
        }
        cur = nx;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(RB[cur][v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void add_edge(int u, int v) {
    adjl[u][deg[u]++] = v;
    adjl[v][deg[v]++] = u;
    A[u][v] = 1;
    A[v][u] = 1;
}

static void drop_half(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adjl[u][k] == v) {
            adjl[u][k] = adjl[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    drop_half(u, v);
    drop_half(v, u);
    A[u][v] = 0;
    A[v][u] = 0;
}

static void take_snapshot(Snap *s) {
    s->n = N;
    s->m = 0;
    for (int u = 0; u < N; u++) {
        s->side[u] = side[u];
        for (int k = 0; k < deg[u]; k++) {
            int v = adjl[u][k];
            if (u < v && s->m < EMAX) {
                s->eu[s->m] = u;
                s->ev[s->m] = v;
                s->m++;
            }
        }
    }
}

static void load_snap(const Snap *s) {
    N = s->n;
    for (int u = 0; u < N; u++) {
        side[u] = s->side[u];
        deg[u] = 0;
        memset(A[u], 0, (size_t)N);
    }
    for (int i = 0; i < s->m; i++) add_edge(s->eu[i], s->ev[i]);
}

/* Append one vertex on a random side and attach it greedily to the other side. */
static void add_vertex(void) {
    int x = N;
    N++;
    side[x] = rndint(2);
    deg[x] = 0;
    for (int y = 0; y < x; y++) {
        A[x][y] = 0;
        A[y][x] = 0;
    }
    int tries = 0;
    while (deg[x] < DCAP && tries < 4000) {
        tries++;
        int y = rndint(x);
        if (side[y] == side[x] || deg[y] >= DCAP || A[x][y]) continue;
        add_edge(x, y);
    }
}

/* Simulated annealing on the current graph. Returns the final cost (0 = valid). */
static long long anneal(long long iters, double T0, double T1) {
    long long cur = cost_fn();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now_sec() > deadline_sec) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);

        if (rnd01() < 0.1) {
            /* Free-capacity edge addition never increases the cost. */
            int u = rndint(N);
            if (deg[u] >= DCAP) continue;
            int w = -1;
            for (int t = 0; t < 40; t++) {
                int c = rndint(N);
                if (side[c] != side[u] && c != u && deg[c] < DCAP && !A[u][c]) {
                    w = c;
                    break;
                }
            }
            if (w < 0) continue;
            add_edge(u, w);
            cur = cost_fn();
            continue;
        }

        /* Rewire: edge (u,v) becomes (u,w), with w on v's side. */
        int u = rndint(N);
        if (deg[u] == 0) continue;
        int v = adjl[u][rndint(deg[u])];
        int w = -1;
        for (int t = 0; t < 40; t++) {
            int c = rndint(N);
            if (side[c] == side[v] && c != v && deg[c] < DCAP && !A[u][c]) {
                w = c;
                break;
            }
        }
        if (w < 0) continue;
        del_edge(u, v);
        add_edge(u, w);
        long long c2 = cost_fn();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            del_edge(u, w);
            add_edge(u, v);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DCAP = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    deadline_sec = atof(argv[4]);
    if (DCAP < 1 || DCAP > 30 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = 0;
    if (n0 < 1 || n0 > MAXN - 100) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int u = 0; u < N; u++) {
        deg[u] = 0;
        memset(A[u], 0, (size_t)N);
    }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (A[u][v] || deg[u] >= DCAP || deg[v] >= DCAP) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS; the engine needs a bipartite start graph. */
    for (int u = 0; u < N; u++) side[u] = -1;
    int ok = 1;
    for (int s0 = 0; s0 < N && ok; s0++) {
        if (side[s0] != -1) continue;
        side[s0] = 0;
        int qh = 0, qt = 0;
        queue_buf[qt++] = s0;
        while (qh < qt && ok) {
            int x = queue_buf[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adjl[x][k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    queue_buf[qt++] = y;
                } else if (side[y] == side[x]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    take_snapshot(&base_s);
    int valid = (cost_fn() == 0);
    if (!valid) {
        valid = (anneal(ITERS, 1.0, 0.05) == 0);
    }
    if (valid) {
        take_snapshot(&base_s);
    } else {
        printf("%d %d\n", base_s.n, base_s.m);
        for (int i = 0; i < base_s.m; i++) printf("%d %d\n", base_s.eu[i], base_s.ev[i]);
        return 0;
    }

    while (now_sec() < deadline_sec && N + 2 < MAXN) {
        load_snap(&base_s);
        add_vertex();
        long long cc = anneal(ITERS, 1.2, 0.05);
        if (cc == 0) take_snapshot(&base_s);
    }

    printf("%d %d\n", base_s.n, base_s.m);
    for (int i = 0; i < base_s.m; i++) printf("%d %d\n", base_s.eu[i], base_s.ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line contains at most s points of S and every point lies on
# at most s lines indexed by S. For each P in S add a new A-vertex joined to
# all q+1 lines through P; for each j in S add a new B-vertex joined to all
# q+1 points on line j. Diameter stays 3.
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
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3). Greedy cover-type vertices, each checked
# with lib.is_valid so the result is always valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


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
# C repair-and-insert search (any D >= 3, d <= 30).
# ----------------------------------------------------------------------------

def _run_c_extend(d, D, graph, budget, seed):
    """Run the C engine from `graph` for about `budget` CPU seconds. Returns (n, edges) or None."""
    n, edges = graph
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed % 1000003, f"{budget:.2f}"],
                        stdin_graph=(n, edges), timeout=budget + 60.0)
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None


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

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    # Greedy spare-degree fill (diameter 3), validity checked per addition.
    if D >= 3 and best_n > 2:
        n_f, e_f = _fill(best_n, best[1], d, D, start + 0.25 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

    # D >= 4: generalized quadrangle baseline and voltage-lift annealing.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        group_deadline = start + 0.35 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < group_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, group_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Vertex insertion with annealed repair from the best graph found so far.
    # Skipped when the Moore bound is already met (calibration cases return fast).
    if D >= 3 and 2 <= d <= 30 and best_n < lib.moore_bound(d, D):
        budget = start + 0.8 * time_limit - time.monotonic() - 1.0
        if budget > 1.0:
            res = _run_c_extend(d, D, best, budget, seed)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
