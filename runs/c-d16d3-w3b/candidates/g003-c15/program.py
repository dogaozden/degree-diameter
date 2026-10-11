import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to all q+1 lines through P; for each j in S
# add a new B-vertex joined to all q+1 points on line j. Diameter stays 3.
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
# Spare-capacity fill (diameter 3), exact-checked with lib.is_valid.
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
# C engine: bitset-based simulated annealing that grows a valid bipartite
# graph. State is always bipartite with degree <= d. Moves are degree-
# preserving 2-switches, cross-edge additions and removals. The cost is the
# number of ordered vertex pairs at distance > D (computed with bitsets).
# When cost reaches 0 the graph is saved and a new vertex is attached to
# spare-degree vertices of the opposite side; SA then tries to repair it.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define DMAX 64
#define WMAX 64

static int dd, DD, n;
static int col[MAXN], deg[MAXN], adj[MAXN][DMAX];
static uint64_t bufA[MAXN * WMAX], bufB[MAXN * WMAX];
static int bn, bcol[MAXN], bdeg[MAXN], badj[MAXN][DMAX], have_best;
static uint64_t rs;
static clock_t t0;
static double budget;
static int mv_type, ua, ub, uc, ue;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
}
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

/* Number of ordered pairs (v,u) with dist(v,u) > DD. Zero means diameter <= DD. */
static long long cost(void) {
    int W = (n + 63) / 64;
    uint64_t *c = bufA, *x = bufB;
    for (int v = 0; v < n; v++) {
        memset(c + v * WMAX, 0, sizeof(uint64_t) * (size_t)W);
        c[v * WMAX + v / 64] |= 1ULL << (v % 64);
    }
    for (int t = 0; t < DD; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *xv = x + v * WMAX;
            const uint64_t *cv = c + v * WMAX;
            for (int w = 0; w < W; w++) xv[w] = cv[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *cu = c + adj[v][i] * WMAX;
                for (int w = 0; w < W; w++) xv[w] |= cu[w];
            }
        }
        uint64_t *tmp = c; c = x; x = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += pc64(c[v * WMAX + w]);
        bad += n - pc;
    }
    return bad;
}

static int pick_side(int side) {
    for (int tr = 0; tr < 400; tr++) {
        int v = rndi(n);
        if (col[v] == side && deg[v] > 0) return v;
    }
    return -1;
}

static int pick_spare(int side) {
    for (int tr = 0; tr < 400; tr++) {
        int v = rndi(n);
        if (col[v] == side && deg[v] < dd) return v;
    }
    return -1;
}

/* Apply a random move. Returns 0 if no move was possible (nothing applied). */
static int propose(void) {
    int r = rndi(100);
    if (r < 65) {
        int a = pick_side(0), c = pick_side(0);
        if (a < 0 || c < 0 || a == c) return 0;
        int b = adj[a][rndi(deg[a])];
        int e = adj[c][rndi(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) return 0;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        ua = a; ub = b; uc = c; ue = e; mv_type = 1;
        return 1;
    } else if (r < 92) {
        int a = pick_spare(0), b = pick_spare(1);
        if (a < 0 || b < 0 || has_edge(a, b)) return 0;
        add_edge(a, b);
        ua = a; ub = b; mv_type = 2;
        return 1;
    } else {
        int a = pick_side(0);
        if (a < 0) return 0;
        int b = adj[a][rndi(deg[a])];
        del_edge(a, b);
        ua = a; ub = b; mv_type = 3;
        return 1;
    }
}

static void undo(void) {
    if (mv_type == 1) {
        del_edge(ua, ue);
        del_edge(uc, ub);
        add_edge(ua, ub);
        add_edge(uc, ue);
    } else if (mv_type == 2) {
        del_edge(ua, ub);
    } else if (mv_type == 3) {
        add_edge(ua, ub);
    }
}

/* Attach a new vertex (index n) to up to dd spare-degree vertices of the opposite side. */
static int add_vertex(void) {
    if (n >= MAXN - 1) return 0;
    static int cand[MAXN];
    int first = rndi(2);
    for (int s = 0; s < 2; s++) {
        int c = (first + s) & 1;
        int k = 0;
        for (int v = 0; v < n; v++)
            if (col[v] == 1 - c && deg[v] < dd) cand[k++] = v;
        if (k == 0) continue;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
        }
        int take = k < dd ? k : dd;
        col[n] = c;
        deg[n] = 0;
        for (int i = 0; i < take; i++) add_edge(n, cand[i]);
        n++;
        return 1;
    }
    return 0;
}

static void save_best(void) {
    bn = n;
    memcpy(bcol, col, sizeof(int) * (size_t)n);
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) memcpy(badj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    have_best = 1;
}

static void restore_best(void) {
    n = bn;
    memcpy(col, bcol, sizeof(int) * (size_t)n);
    memcpy(deg, bdeg, sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) memcpy(adj[v], badj[v], sizeof(int) * (size_t)deg[v]);
}

static int bipartition(void) {
    static int stack[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    stack[sp++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int load_input(void) {
    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 0 || n0 > MAXN - 2 || m0 < 0) return 0;
    n = n0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) return 0;
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) return 0;
        if (deg[a] >= dd || deg[b] >= dd || has_edge(a, b)) return 0;
        add_edge(a, b);
    }
    return bipartition();
}

static void make_complete(void) {
    n = 2 * dd;
    for (int v = 0; v < n; v++) { deg[v] = 0; col[v] = v < dd ? 0 : 1; }
    for (int a = 0; a < dd; a++)
        for (int b = dd; b < 2 * dd; b++) add_edge(a, b);
}

static void print_best(void) {
    if (!have_best) { printf("0 0\n"); return; }
    long long m = 0;
    for (int v = 0; v < bn; v++) m += bdeg[v];
    m /= 2;
    printf("%d %lld\n", bn, m);
    for (int v = 0; v < bn; v++)
        for (int i = 0; i < bdeg[v]; i++) {
            int u = badj[v][i];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    t0 = clock();
    if (dd < 1 || dd > DMAX || DD < 2 || 2 * dd > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    if (!load_input()) make_complete();
    long long cc = cost();
    have_best = 0;
    long long epoch_best = cc;
    long long since = 0;
    const long long STUCK = 20000;
    const double T_HI = 4.0, T_LO = 0.2;
    long long iter = 0;

    for (;;) {
        if ((iter & 63) == 0 && elapsed() > budget) break;
        iter++;
        if (cc == 0) {
            save_best();
            if (!add_vertex()) break;
            cc = cost();
            epoch_best = cc;
            since = 0;
            continue;
        }
        if (!propose()) continue;
        long long c2 = cost();
        long long delta = c2 - cc;
        double frac = (double)since / (double)STUCK;
        if (frac > 1.0) frac = 1.0;
        double T = T_HI * pow(T_LO / T_HI, frac);
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cc = c2;
        } else {
            undo();
        }
        if (cc < epoch_best) { epoch_best = cc; since = 0; }
        else since++;
        if (since > STUCK) {
            if (have_best) restore_best();
            if (!add_vertex()) break;
            cc = cost();
            epoch_best = cc;
            since = 0;
        }
    }
    print_best();
    return 0;
}
"""


def _c_augment(d, D, best, seconds, seed):
    """Run the C annealer from `best` for about `seconds`; return (n, edges) or None."""
    if seconds < 3 or d < 2 or d > 64:
        return None
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}"], stdin_graph=best,
                     timeout=seconds + 5)
    return lib.parse_graph_text(text)


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

    # Stage 1: arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Stage 2: quick greedy neighbourhood fill (exact-checked).
    if D >= 3 and best_n > 2:
        n_f, e_f = _fill(best_n, best[1], d, D, start + 0.1 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

    # Stage 3: C simulated annealing that grows the best valid graph.
    # Diameter 3 gets most of the budget; other diameters keep time for lifts.
    c_end = start + (0.8 if D == 3 else 0.5) * time_limit
    secs = c_end - time.monotonic() - 2.0
    try:
        res = _c_augment(d, D, best, secs, seed)
        if res is not None:
            consider(res[0], res[1])
    except Exception:
        pass

    # Stage 4: generalized quadrangle and voltage-lift search for D >= 4.
    if D >= 4 and time.monotonic() < start + 0.5 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        deadline = start + 0.8 * time_limit
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
