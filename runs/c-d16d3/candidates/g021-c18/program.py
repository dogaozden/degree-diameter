import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex insertion by tabu set cover, with ILS-style kicks.
#
# A new vertex w on side c is joined to a set N of vertices on side 1-c, each
# with spare degree. w reaches every vertex within D exactly when that vertex
# lies in the (D-1)-ball of some u in N, so N must cover all vertices by
# (D-1)-balls. Adding a vertex never lengthens an old distance, so the graph
# stays valid. The cover is found by tabu search over swaps with bitset gains.
# Redundant neighbours are pruned, which keeps spare degree for later vertices.
# Kicks remove a random vertex and keep the result only if the graph is valid.
# The largest valid graph seen is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXDEG 128
#define ITERS 150
#define MAXFAIL 60

typedef uint64_t u64;

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int col[MAXN];
} Snap;

static int N = 0, dmax = 0, D = 0, W = 0;
static int degr[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static u64 ball[MAXN][MAXW];
static u64 tmpb[MAXN][MAXW];
static u64 rs = 88172645463325252ULL;
static Snap best_snap, bk_snap;
static int inset[MAXN];
static long tabu_until[MAXN];
static int chosen[MAXDEG];
static u64 fullm[MAXW], covm[MAXW], othm[MAXW], urm[MAXW];
static double deadline_cpu = 0.0;

static unsigned rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (unsigned)(rs >> 16);
}

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double now(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < degr[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][degr[u]++] = v;
    adj[v][degr[v]++] = u;
}

static int is_valid_now(void) {
    static int dist[MAXN];
    static int q[MAXN];
    for (int s = 0; s < N; s++) {
        for (int v = 0; v < N; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            if (dist[u] >= D) continue;
            for (int i = 0; i < degr[u]; i++) {
                int v = adj[u][i];
                if (dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    q[tail++] = v;
                }
            }
        }
        if (tail != N) return 0;
    }
    return 1;
}

static int colour_graph(void) {
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < degr[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[tail++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void compute_balls(void) {
    int R = D - 1;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) ball[v][w] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < R; step++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) tmpb[v][w] = ball[v][w];
            for (int i = 0; i < degr[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) tmpb[v][w] |= ball[u][w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) ball[v][w] = tmpb[v][w];
    }
}

static void make_full(void) {
    for (int w = 0; w < W; w++) fullm[w] = 0;
    for (int v = 0; v < N; v++) fullm[v >> 6] |= 1ULL << (v & 63);
}

/* Tabu search for k candidate balls covering all N vertices. Returns number of sets found (0 = failure). */
static int cover_search(const int *cand, int nc, int k, int iters, int *out) {
    if (nc <= 0 || k <= 0) return 0;
    if (k > nc) k = nc;
    if (k > MAXDEG) k = MAXDEG;
    for (int i = 0; i < nc; i++) {
        inset[i] = 0;
        tabu_until[i] = 0;
    }
    make_full();
    for (int w = 0; w < W; w++) covm[w] = 0;
    int kk = 0;
    while (kk < k) {
        int bi = -1, bg = -1, ties = 0;
        for (int i = 0; i < nc; i++) {
            if (inset[i]) continue;
            const u64 *b = ball[cand[i]];
            int g = 0;
            for (int w = 0; w < W; w++) g += pc(b[w] & ~covm[w]);
            if (g > bg) {
                bg = g;
                bi = i;
                ties = 1;
            } else if (g == bg) {
                ties++;
                if (rnd() % (unsigned)ties == 0) bi = i;
            }
        }
        if (bi < 0) break;
        inset[bi] = 1;
        chosen[kk++] = bi;
        for (int w = 0; w < W; w++) covm[w] |= ball[cand[bi]][w];
    }
    k = kk;
    if (k == 0) return 0;

    int bestseen = INT_MAX;
    for (int it = 0; it < iters; it++) {
        for (int w = 0; w < W; w++) covm[w] = 0;
        for (int i = 0; i < k; i++)
            for (int w = 0; w < W; w++) covm[w] |= ball[cand[chosen[i]]][w];
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc(covm[w]);
        int unc = N - cnt;
        if (unc < bestseen) bestseen = unc;
        if (unc == 0) {
            for (int i = 0; i < k; i++) out[i] = cand[chosen[i]];
            return k;
        }
        int bval = INT_MAX, bi = -1, ba = -1, ties = 0;
        for (int i = 0; i < k; i++) {
            for (int w = 0; w < W; w++) othm[w] = 0;
            for (int j = 0; j < k; j++) {
                if (j == i) continue;
                const u64 *b = ball[cand[chosen[j]]];
                for (int w = 0; w < W; w++) othm[w] |= b[w];
            }
            for (int w = 0; w < W; w++) urm[w] = fullm[w] & ~othm[w];
            for (int a = 0; a < nc; a++) {
                if (inset[a]) continue;
                const u64 *b = ball[cand[a]];
                int val = 0;
                for (int w = 0; w < W; w++) val += pc(urm[w] & ~b[w]);
                if (tabu_until[a] > it && val >= bestseen) continue;
                if (val < bval) {
                    bval = val;
                    bi = i;
                    ba = a;
                    ties = 1;
                } else if (val == bval) {
                    ties++;
                    if (rnd() % (unsigned)ties == 0) {
                        bi = i;
                        ba = a;
                    }
                }
            }
        }
        if (bi < 0) continue;
        int old = chosen[bi];
        inset[old] = 0;
        tabu_until[old] = (long)it + 5 + (long)(rnd() % 5u);
        chosen[bi] = ba;
        inset[ba] = 1;
    }
    return 0;
}

/* True if the balls of sel[j], j != skip, cover all N vertices. */
static int covers_except(const int *sel, int m, int skip) {
    for (int w = 0; w < W; w++) othm[w] = 0;
    for (int j = 0; j < m; j++) {
        if (j == skip) continue;
        const u64 *b = ball[sel[j]];
        for (int w = 0; w < W; w++) othm[w] |= b[w];
    }
    int cnt = 0;
    for (int w = 0; w < W; w++) cnt += pc(othm[w]);
    return cnt == N;
}

static void insert_vertex(int side, const int *sel, int m) {
    int w = N;
    N++;
    col[w] = side;
    degr[w] = 0;
    for (int i = 0; i < m; i++) {
        int u = sel[i];
        adj[w][degr[w]++] = u;
        adj[u][degr[u]++] = w;
    }
}

static void remove_vertex(int v) {
    for (int i = 0; i < degr[v]; i++) {
        int u = adj[v][i];
        for (int j = 0; j < degr[u]; j++) {
            if (adj[u][j] == v) {
                adj[u][j] = adj[u][degr[u] - 1];
                degr[u]--;
                break;
            }
        }
    }
    degr[v] = 0;
    int L = N - 1;
    if (v != L) {
        for (int i = 0; i < degr[L]; i++) {
            int u = adj[L][i];
            for (int j = 0; j < degr[u]; j++) {
                if (adj[u][j] == L) {
                    adj[u][j] = v;
                    break;
                }
            }
        }
        degr[v] = degr[L];
        memcpy(adj[v], adj[L], sizeof(int) * (size_t)degr[L]);
        col[v] = col[L];
    }
    N--;
}

static void snap_save(Snap *s) {
    s->n = N;
    for (int v = 0; v < N; v++) {
        s->deg[v] = degr[v];
        s->col[v] = col[v];
        memcpy(s->adj[v], adj[v], sizeof(int) * (size_t)degr[v]);
    }
}

static void snap_load(const Snap *s) {
    N = s->n;
    for (int v = 0; v < N; v++) {
        degr[v] = s->deg[v];
        col[v] = s->col[v];
        memcpy(adj[v], s->adj[v], sizeof(int) * (size_t)degr[v]);
    }
}

static void print_snap(const Snap *s) {
    long m = 0;
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++)
            if (v < s->adj[v][i]) m++;
    printf("%d %ld\n", s->n, m);
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++)
            if (v < s->adj[v][i]) printf("%d %d\n", v, s->adj[v][i]);
}

static void kick(void) {
    if (N <= 2) return;
    snap_save(&bk_snap);
    int v = (int)(rnd() % (unsigned)N);
    remove_vertex(v);
    if (!is_valid_now()) snap_load(&bk_snap);
    compute_balls();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)(atol(argv[3]) + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    deadline_cpu = budget * 0.95;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    int ok = (n >= 1 && n <= MAXN - 2 && m >= 0 && dmax >= 1 && dmax <= MAXDEG && D >= 2);
    if (ok) {
        N = n;
        for (int v = 0; v < N; v++) degr[v] = 0;
        for (int i = 0; i < m && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || u >= N || v < 0 || v >= N || u == v) ok = 0;
            else if (degr[u] >= dmax || degr[v] >= dmax || has_edge(u, v)) ok = 0;
            else add_edge(u, v);
        }
    }
    if (ok && (!colour_graph() || !is_valid_now())) ok = 0;
    if (!ok) {
        printf("1 0\n");
        return 0;
    }

    compute_balls();
    snap_save(&best_snap);
    int fails = 0;
    static int cand[MAXN];
    static int sel[MAXDEG];
    while (now() < deadline_cpu) {
        int side = (int)(rnd() & 1u);
        int nc = 0;
        for (int u = 0; u < N; u++)
            if (col[u] == 1 - side && degr[u] < dmax) cand[nc++] = u;
        int got = 0;
        if (nc > 0 && N < MAXN - 1) got = cover_search(cand, nc, dmax, ITERS, sel);
        if (got > 0) {
            int i = 0;
            while (i < got && got > 1) {
                if (covers_except(sel, got, i)) {
                    sel[i] = sel[got - 1];
                    got--;
                } else {
                    i++;
                }
            }
            insert_vertex(side, sel, got);
            compute_balls();
            fails = 0;
            if (N > best_snap.n) snap_save(&best_snap);
        } else if (++fails >= MAXFAIL) {
            kick();
            fails = 0;
        }
    }
    print_snap(&best_snap);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to the q+1 lines through P; for each j in S
# add a new B-vertex joined to the q+1 points on line j.
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Simulated annealing over bi-Cayley voltage lifts (D >= 4).
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
# Glue: C insertion search.
# ----------------------------------------------------------------------------

def _c_augment(n, edges, d, D, seed, budget):
    """Run the C tabu-cover insertion search for about `budget` seconds. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 4.0)
        return lib.parse_graph_text(out)
    except Exception:
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

    def elapsed():
        return time.monotonic() - start

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    # Generalized quadrangle baseline (D = 4).
    if D >= 4 and elapsed() < 0.30 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts (only for D >= 4; D = 3 time goes to C).
    if D >= 4:
        search_end = start + 0.55 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C tabu-cover insertion on the best graph found so far.
    if D >= 3:
        budget = min(0.88 * time_limit - elapsed(), time_limit - elapsed() - 6.0)
        if budget >= 2.0:
            res = _c_augment(best_n, best[1], d, D, seed, budget)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
