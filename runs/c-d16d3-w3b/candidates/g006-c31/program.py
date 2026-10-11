import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair simulated annealing.
#
# Keeps a bipartite graph with max degree d. Cost = number of vertex pairs at
# distance > D, computed exactly by bit-parallel ball expansion. Moves are
# degree-preserving 2-switches, endpoint rewires, and edge additions into spare
# degree. When cost reaches 0 the graph is saved and a new vertex is added with
# d edges, stealing one edge from each saturated neighbour. Failed phases roll
# back to the best valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW 32

static int N, d, D, W;
static int deg[MAXN], side[MAXN];
static int nb[MAXN][MAXD];
static unsigned char adj[MAXN][MAXN];
static uint64_t ra[MAXN][MAXW], rb[MAXN][MAXW];

static int hasbest, bN;
static int bside[MAXN], bdeg[MAXN];
static int bnb[MAXN][MAXD];

static uint64_t rs = 1;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D. */
static long cost_eval(void) {
    int i, j, k, t;
    W = (N + 63) >> 6;
    for (i = 0; i < N; i++) {
        memset(ra[i], 0, sizeof(uint64_t) * (size_t)W);
        ra[i][i >> 6] |= 1ULL << (i & 63);
    }
    for (t = 0; t < D; t++) {
        for (i = 0; i < N; i++) {
            uint64_t *dst = rb[i];
            memcpy(dst, ra[i], sizeof(uint64_t) * (size_t)W);
            for (k = 0; k < deg[i]; k++) {
                const uint64_t *src = ra[nb[i][k]];
                for (j = 0; j < W; j++) dst[j] |= src[j];
            }
        }
        for (i = 0; i < N; i++) memcpy(ra[i], rb[i], sizeof(uint64_t) * (size_t)W);
    }
    long bad = 0;
    for (i = 0; i < N; i++) {
        int c = 0;
        for (j = 0; j < W; j++) c += pc64(ra[i][j]);
        bad += N - c;
    }
    return bad / 2;
}

static void add_edge(int a, int b) {
    adj[a][b] = 1;
    adj[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void rem_nb(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    adj[a][b] = 0;
    adj[b][a] = 0;
    rem_nb(a, b);
    rem_nb(b, a);
}

/* Random vertex on side s; need_spare: deg < d; need_nz: deg > 0. Returns -1 on failure. */
static int pick(int s, int need_spare, int need_nz) {
    for (int t = 0; t < 2000; t++) {
        int v = rndi(N);
        if (side[v] != s) continue;
        if (need_spare && deg[v] >= d) continue;
        if (need_nz && deg[v] == 0) continue;
        return v;
    }
    return -1;
}

typedef struct {
    int nd, na;
    int da[2], db[2], aa[2], ab[2];
} Move;

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nd; i++) del_edge(m->da[i], m->db[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->aa[i], m->ab[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->aa[i], m->ab[i]);
    for (int i = 0; i < m->nd; i++) add_edge(m->da[i], m->db[i]);
}

static int gen_move(Move *m) {
    double r = rndu();
    m->nd = 0;
    m->na = 0;
    if (r < 0.6) {
        /* degree-preserving 2-switch: (u,v),(u2,v2) -> (u,v2),(u2,v) */
        int u = pick(0, 0, 1), u2 = pick(0, 0, 1);
        if (u < 0 || u2 < 0 || u == u2) return 0;
        int v = nb[u][rndi(deg[u])], v2 = nb[u2][rndi(deg[u2])];
        if (v == v2) return 0;
        if (adj[u][v2] || adj[u2][v]) return 0;
        m->nd = 2; m->da[0] = u; m->db[0] = v; m->da[1] = u2; m->db[1] = v2;
        m->na = 2; m->aa[0] = u; m->ab[0] = v2; m->aa[1] = u2; m->ab[1] = v;
        return 1;
    } else if (r < 0.8) {
        /* rewire endpoint: (u,v) -> (u,v2) with v2 spare */
        int u = pick(0, 0, 1);
        if (u < 0) return 0;
        int v = nb[u][rndi(deg[u])];
        int v2 = pick(1, 1, 0);
        if (v2 < 0 || v2 == v || adj[u][v2]) return 0;
        m->nd = 1; m->da[0] = u; m->db[0] = v;
        m->na = 1; m->aa[0] = u; m->ab[0] = v2;
        return 1;
    } else {
        /* add edge between spare vertices */
        int u = pick(0, 1, 0), v = pick(1, 1, 0);
        if (u < 0 || v < 0 || adj[u][v]) return 0;
        m->na = 1; m->aa[0] = u; m->ab[0] = v;
        return 1;
    }
}

/* Append a new vertex with up to d edges, stealing one edge from each saturated neighbour. */
static void grow(void) {
    int x = N++;
    deg[x] = 0;
    side[x] = rndi(2);
    int c = side[x];
    int tries = 0;
    while (deg[x] < d && tries < 50 * N) {
        tries++;
        int v = rndi(x);
        if (side[v] == c || adj[x][v]) continue;
        if (deg[v] >= d) {
            if (deg[v] == 0) continue;
            int w = nb[v][rndi(deg[v])];
            del_edge(v, w);
        }
        add_edge(x, v);
    }
}

static void save_best(void) {
    bN = N;
    hasbest = 1;
    for (int i = 0; i < N; i++) {
        bside[i] = side[i];
        bdeg[i] = deg[i];
        memcpy(bnb[i], nb[i], sizeof(int) * (size_t)deg[i]);
    }
}

static void restore_best(void) {
    for (int i = 0; i < N; i++) {
        for (int k = 0; k < deg[i]; k++) adj[i][nb[i][k]] = 0;
        deg[i] = 0;
    }
    N = bN;
    for (int i = 0; i < N; i++) {
        side[i] = bside[i];
        deg[i] = bdeg[i];
        memcpy(nb[i], bnb[i], sizeof(int) * (size_t)deg[i]);
    }
    for (int i = 0; i < N; i++)
        for (int k = 0; k < deg[i]; k++) adj[i][nb[i][k]] = 1;
}

static int bip_sides(void) {
    static int q[MAXN];
    for (int i = 0; i < N; i++) side[i] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)atol(argv[3]) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double t0 = now();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (d < 1 || d >= MAXD || D < 1 || n < 0 || n > MAXN - 64 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    int ok = 1;
    for (int e = 0; e < m && ok; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || adj[u][v] ||
            deg[u] >= d || deg[v] >= d) { ok = 0; break; }
        add_edge(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    if (N == 0) {
        N = 2;
        side[0] = 0;
        side[1] = 1;
        add_edge(0, 1);
    } else if (!bip_sides()) {
        printf("0 0\n");
        return 0;
    }

    long cost = cost_eval();
    if (cost == 0) save_best();

    while (now() - t0 < budget && N + 1 < MAXN) {
        long iters = 12000;
        double T0 = 1.5, T1 = 0.1;
        for (long it = 0; it < iters; it++) {
            if (now() - t0 >= budget) break;
            if (cost == 0) {
                save_best();
                if (N + 1 >= MAXN) break;
                grow();
                cost = cost_eval();
                continue;
            }
            double T = T0 * pow(T1 / T0, (double)it / (double)iters);
            Move mv;
            if (!gen_move(&mv)) continue;
            apply_move(&mv);
            long c2 = cost_eval();
            long delta = c2 - cost;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
                cost = c2;
            } else {
                undo_move(&mv);
            }
        }
        if (cost != 0 && hasbest) {
            restore_best();
            cost = cost_eval();
        }
    }

    if (cost == 0) save_best();
    else if (hasbest) restore_best();
    else {
        printf("0 0\n");
        return 0;
    }
    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }
    long M = 0;
    for (int i = 0; i < N; i++) M += deg[i];
    M /= 2;
    printf("%d %ld\n", N, M);
    for (int i = 0; i < N; i++)
        for (int k = 0; k < deg[i]; k++)
            if (nb[i][k] > i) printf("%d %d\n", i, nb[i][k]);
    return 0;
}
"""


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
    for t, j in enumerate(S):
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
# Spare-capacity fill and cross-edge saturation (Python side).
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


def _cross_saturate(n, edges, d, n_new, rng):
    """Add random cross edges (touching a vertex >= n_new) while degree allows; return new edge list."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    col = _bipartition(n, adj)
    have = set()
    for u, v in edges:
        have.add((u, v) if col[u] == 0 else (v, u))
    L = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R
             if (a, b) not in have and (a >= n_new or b >= n_new)]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
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
# Python fallback: simulated annealing over bi-Cayley voltage lifts.
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


def _vcost(k, G, D, darts, perms):
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


def _vedges(k, G, darts, perms):
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
    cost = _vcost(k, G, D, darts, perms)

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
            c2 = _vcost(k, G, D, darts, perms)
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
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    tl = float(time_limit)
    hard_end = t0 + max(1.0, tl - max(1.0, 0.1 * tl))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured starts.
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.1 * tl, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

        if best_n > 2:
            n_arc = best_n
            n_f, e_f = _fill(best_n, best[1], d, D, t0 + 0.15 * tl,
                             random.Random(seed * 104729 + d))
            consider(n_f, e_f)

            trial_rng = random.Random(seed * 31337 + d)
            chain_deadline = t0 + 0.25 * tl
            while time.monotonic() < chain_deadline:
                n_b, e_b = best
                e_sat = _cross_saturate(n_b, e_b, d, n_arc, trial_rng)
                if len(e_sat) == len(e_b):
                    break
                n_s, e_s = _fill(n_b, e_sat, d, D, chain_deadline, trial_rng)
                consider(n_s, e_s)

    if D >= 4 and time.monotonic() < hard_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: C grow-and-repair annealing started from the best graph so far.
    ran_c = False
    c_end = hard_end - 1.0
    c_budget = c_end - time.monotonic() - 2.0
    if d >= 2 and c_budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                            stdin_graph=best, timeout=c_budget + 3.0)
            n_c, e_c = lib.parse_graph_text(out)
            if n_c > 0:
                ran_c = True
                consider(n_c, e_c)
        except (RuntimeError, ValueError):
            ran_c = False

    # Python fallback if the C engine did not run.
    if not ran_c:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < hard_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, hard_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
