import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex insertion by ball covering, with spare-edge kicks.
#
# A new vertex w on one side, joined to a set N of vertices on the other side,
# is within distance D of every old vertex x exactly when x lies within
# distance D-1 of some u in N. Adding a vertex never lengthens an old path,
# so validity is preserved. The C search:
#   1. computes (D-1)-balls as bitsets,
#   2. finds a small neighbourhood N with spare capacity covering everything
#      (greedy set cover with random diversification; concurrent-line pencils
#      are found this way automatically),
#   3. when stuck, kicks the graph: adds a random spare cross edge (always valid)
#      or removes a random edge (kept only if the graph stays valid). This frees
#      capacity for the next cover attempt.
# The best valid graph seen is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 64

typedef uint64_t u64;

static int N = 0;
static int DMAX = 0;
static int DIAM = 0;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static u64 balls[MAXN][MAXW];
static u64 nxt[MAXN][MAXW];

static int bestN = 0;
static int best_deg[MAXN];
static int best_adj[MAXN][MAXD];
static int best_col[MAXN];

static int cand[MAXN];
static int pool[MAXN];
static int gain[MAXN];

static u64 rs = 1;
static clock_t t0;
static double budget_s = 1.0;

static u64 rnd64(void) {
    u64 z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static int rnd_int(int k) {
    if (k <= 1) return 0;
    return (int)(rnd64() % (u64)k);
}

static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int nwords(void) { return (N + 63) >> 6; }

static double elapsed(void) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int time_up(void) { return elapsed() > budget_s; }

static int has_adj(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void drop_index(int a, int k) {
    adj[a][k] = adj[a][--deg[a]];
}

static void link(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void unlink(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) { drop_index(a, k); break; }
    for (int k = 0; k < deg[b]; k++)
        if (adj[b][k] == a) { drop_index(b, k); break; }
}

/* balls[v] = bitset of vertices within distance R of v */
static void compute_balls(int R) {
    int W = nwords();
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) balls[v][w] = 0;
    for (int v = 0; v < N; v++)
        balls[v][v >> 6] |= 1ULL << (v & 63);
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = balls[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const u64 *src = balls[adj[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) balls[v][w] = nxt[v][w];
    }
}

/* Assumes balls hold DIAM-balls: true if every pair is within DIAM. */
static int covers_all(void) {
    int W = nwords();
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(balls[v][w]);
        if (c != N) return 0;
    }
    return 1;
}

static int graph_valid(void) {
    for (int v = 0; v < N; v++)
        if (deg[v] > DMAX) return 0;
    compute_balls(DIAM);
    return covers_all();
}

static int two_colour(void) {
    static int qu[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int v = qu[h++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                if (col[u] == -1) {
                    col[u] = 1 - col[v];
                    qu[t++] = u;
                } else if (col[u] == col[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Try to insert one vertex whose neighbourhood covers all current vertices within DIAM. */
static int try_insert(int attempts) {
    if (N >= MAXN - 1) return 0;
    compute_balls(DIAM - 1);
    int W = nwords();
    int first = rnd_int(2);
    for (int si = 0; si < 2; si++) {
        int side = (si == 0) ? first : 1 - first;
        int nc = 0;
        for (int u = 0; u < N; u++)
            if (col[u] != side && deg[u] < DMAX) cand[nc++] = u;
        if (nc == 0) continue;
        for (int at = 0; at < attempts; at++) {
            if (time_up()) return 0;
            for (int i = nc - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
            }
            u64 covered[MAXW];
            for (int w = 0; w < W; w++) covered[w] = 0;
            memcpy(pool, cand, sizeof(int) * nc);
            int np = nc;
            int chosen[MAXD];
            int nch = 0, ncov = 0;
            while (ncov < N && nch < DMAX && np > 0) {
                int bi = -1, bg = 0;
                for (int i = 0; i < np; i++) {
                    int u = pool[i], g = 0;
                    for (int w = 0; w < W; w++)
                        g += popc64(balls[u][w] & ~covered[w]);
                    gain[i] = g;
                    if (g > bg) { bg = g; bi = i; }
                }
                if (bi < 0) break;
                if (rnd_int(8) == 0) {
                    /* diversification: random candidate with positive gain */
                    int cnt = 0;
                    for (int i = 0; i < np; i++) if (gain[i] > 0) cnt++;
                    int pick = rnd_int(cnt);
                    for (int i = 0; i < np; i++) {
                        if (gain[i] > 0) {
                            if (pick == 0) { bi = i; break; }
                            pick--;
                        }
                    }
                    bg = gain[bi];
                }
                int u = pool[bi];
                pool[bi] = pool[--np];
                chosen[nch++] = u;
                for (int w = 0; w < W; w++) covered[w] |= balls[u][w];
                ncov += bg;
            }
            if (ncov == N) {
                int w = N++;
                deg[w] = 0;
                col[w] = side;
                for (int k = 0; k < nch; k++) link(w, chosen[k]);
                return 1;
            }
        }
    }
    return 0;
}

static int add_spare_edge(void) {
    if (N < 2) return 0;
    for (int t = 0; t < 40; t++) {
        int a = rnd_int(N);
        if (deg[a] >= DMAX) continue;
        int b = rnd_int(N);
        if (col[b] == col[a] || deg[b] >= DMAX || has_adj(a, b)) continue;
        link(a, b);
        return 1;
    }
    return 0;
}

static int remove_random_edge(int *ra, int *rb) {
    if (N < 2) return 0;
    for (int t = 0; t < 40; t++) {
        int a = rnd_int(N);
        if (deg[a] == 0) continue;
        int b = adj[a][rnd_int(deg[a])];
        *ra = a;
        *rb = b;
        unlink(a, b);
        return 1;
    }
    return 0;
}

static void save_best(void) {
    bestN = N;
    memcpy(best_deg, deg, sizeof(int) * N);
    memcpy(best_col, col, sizeof(int) * N);
    memcpy(best_adj, adj, sizeof(int) * MAXD * N);
}

static void load_best(void) {
    N = bestN;
    memcpy(deg, best_deg, sizeof(int) * N);
    memcpy(col, best_col, sizeof(int) * N);
    memcpy(adj, best_adj, sizeof(int) * MAXD * N);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], 0, 10);
    double tl = atof(argv[4]);
    t0 = clock();
    budget_s = tl * 0.93;
    rs = seed * 0x2545F4914F6CDD1DULL + 12345ULL;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 2 || n > MAXN - 2 || d < 1 || d > MAXD || D < 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    DMAX = d;
    DIAM = D;
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { bad = 1; break; }
        if (deg[u] >= DMAX || deg[v] >= DMAX || has_adj(u, v)) { bad = 1; break; }
        link(u, v);
    }
    if (bad || !two_colour() || !graph_valid()) {
        printf("0 0\n");
        return 0;
    }

    save_best();
    int since = 0;
    while (!time_up()) {
        while (try_insert(3)) {
            if (time_up()) break;
        }
        if (N > bestN) {
            save_best();
            since = 0;
        } else {
            since++;
        }
        if (since > 400) {
            load_best();
            since = 0;
        }
        /* kick: spare cross edge (always valid) or edge removal (kept if still valid) */
        if (rnd_int(10) < 4) {
            add_spare_edge();
        } else {
            int a = -1, b = -1;
            if (remove_random_edge(&a, &b)) {
                compute_balls(DIAM);
                if (!covers_all()) link(a, b);
            }
        }
    }

    load_best();
    long long mout = 0;
    for (int v = 0; v < N; v++) mout += deg[v];
    mout /= 2;
    printf("%d %lld\n", N, mout);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# in which every line meets S in at most s points. For each P in S add a new
# A-vertex joined to the q+1 lines through P; for each j in S add a new
# B-vertex joined to the q+1 points on line j.
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


def _has_spare(n, edges, d):
    """True if some vertex has degree below d (so the C engine can insert vertices)."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return any(x < d for x in deg)


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
# C engine driver.
# ----------------------------------------------------------------------------

def _engine(n, edges, d, D, seed, budget):
    """Run the C ball-cover insertion search from (n, edges) for about `budget` seconds."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=budget + 20.0)
    return lib.parse_graph_text(text)


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
        arcs = _arc_extensions(d, start + 0.12 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.30 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts (only for D >= 4).
    if D >= 4:
        search_end = start + 0.40 * time_limit
        ks = [1, 2, 2, 3, 4]
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

    # C ball-cover insertion with spare-edge kicks, started from the best graph so far.
    if D >= 2 and _has_spare(best_n, best[1], d):
        end = start + 0.88 * time_limit
        budget = end - time.monotonic() - 1.0
        if budget > 2.0:
            try:
                n2, e2 = _engine(best_n, best[1], d, D, seed, budget)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
