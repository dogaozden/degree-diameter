"""Improved search for diameter-3 bipartite graphs.

For D = 3, the best arc-extended projective-plane graph is handed to a C
engine that grows it one vertex at a time. Each attempt adds a vertex, fills
spare degree greedily, then runs simulated annealing over degree-preserving
edge swaps and edge moves, minimising the number of vertex pairs at distance
greater than D. A failed attempt restores the last valid graph. Every output
is validated with lib.is_valid, and the arc graph remains the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1000
#define NW 16
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG)

static int N, DEG, DIAM;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char M[MAXN][MAXN];
static uint64_t Rb[2][MAXN][NW];

static int EU[MAXE], EV[MAXE];
static int SNU[MAXE], SNV[MAXE];
static int SNM, SNN;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double runif(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void reset_graph(int n) {
    N = n;
    memset(M, 0, sizeof(M));
    memset(deg, 0, sizeof(deg));
}

static void add_edge(int u, int v) {
    M[u][v] = 1;
    M[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    M[u][v] = 0;
    M[v][u] = 0;
    del_from(u, v);
    del_from(v, u);
}

/* Number of unordered pairs at distance > DIAM (0 means valid). */
static long long cost_of(void) {
    int nw = (N + 63) / 64;
    int cur = 0;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < nw; w++) Rb[0][v][w] = 0;
        Rb[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        int nx = cur ^ 1;
        for (int v = 0; v < N; v++) {
            uint64_t *dst = Rb[nx][v];
            const uint64_t *src = Rb[cur][v];
            for (int w = 0; w < nw; w++) dst[w] = src[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *o = Rb[cur][nb[v][k]];
                for (int w = 0; w < nw; w++) dst[w] |= o[w];
            }
        }
        cur = nx;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(Rb[cur][v][w]);
        miss += N - c;
    }
    return miss / 2;
}

static void take_snapshot(void) {
    SNN = N;
    SNM = 0;
    for (int u = 0; u < N; u++) {
        for (int k = 0; k < deg[u]; k++) {
            int v = nb[u][k];
            if (u < v) {
                SNU[SNM] = u;
                SNV[SNM] = v;
                SNM++;
            }
        }
    }
}

static void restore_snapshot(void) {
    reset_graph(SNN);
    for (int i = 0; i < SNM; i++) add_edge(SNU[i], SNV[i]);
}

static int rand_edge(int *a, int *b) {
    for (int t = 0; t < 200; t++) {
        int u = rint_(N);
        if (!deg[u]) continue;
        int v = nb[u][rint_(deg[u])];
        if (side[u] == 0) {
            *a = u;
            *b = v;
        } else {
            *a = v;
            *b = u;
        }
        return 1;
    }
    return 0;
}

typedef struct {
    int type, a1, b1, a2, b2;
} Move;

/* Apply a random degree-preserving swap (type 0) or an edge endpoint move (type 1). */
static int propose(Move *mv) {
    if (runif() < 0.6) {
        mv->type = 0;
        if (!rand_edge(&mv->a1, &mv->b1) || !rand_edge(&mv->a2, &mv->b2)) return 0;
        if (mv->a1 == mv->a2 || mv->b1 == mv->b2) return 0;
        if (M[mv->a1][mv->b2] || M[mv->a2][mv->b1]) return 0;
        del_edge(mv->a1, mv->b1);
        del_edge(mv->a2, mv->b2);
        add_edge(mv->a1, mv->b2);
        add_edge(mv->a2, mv->b1);
        return 1;
    }
    mv->type = 1;
    if (!rand_edge(&mv->a1, &mv->b1)) return 0;
    for (int t = 0; t < 30; t++) {
        int b2 = rint_(N);
        if (side[b2] == 1 && b2 != mv->b1 && deg[b2] < DEG && !M[mv->a1][b2]) {
            mv->b2 = b2;
            del_edge(mv->a1, mv->b1);
            add_edge(mv->a1, b2);
            return 1;
        }
    }
    return 0;
}

static void undo(const Move *mv) {
    if (mv->type == 0) {
        del_edge(mv->a1, mv->b2);
        del_edge(mv->a2, mv->b1);
        add_edge(mv->a1, mv->b1);
        add_edge(mv->a2, mv->b2);
    } else {
        del_edge(mv->a1, mv->b2);
        add_edge(mv->a1, mv->b1);
    }
}

/* Add one edge between spare vertices on opposite sides; never increases the cost. */
static int move_add(void) {
    for (int t = 0; t < 60; t++) {
        int a = rint_(N), b = rint_(N);
        if (side[a] == 0 && side[b] == 1 && deg[a] < DEG && deg[b] < DEG && !M[a][b]) {
            add_edge(a, b);
            return 1;
        }
    }
    return 0;
}

static void fill_vertex(int x) {
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < N; v++) {
        if (v != x && side[v] != side[x] && deg[v] < DEG) cand[nc++] = v;
    }
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    for (int i = 0; i < nc && deg[x] < DEG; i++) {
        int v = cand[i];
        if (deg[v] < DEG && !M[x][v]) add_edge(x, v);
    }
}

static void fill_all(void) {
    int off = rint_(N);
    for (int i = 0; i < N; i++) {
        int a = (off + i) % N;
        if (side[a] != 0) continue;
        for (int j = 0; j < N && deg[a] < DEG; j++) {
            int b = (off + j) % N;
            if (side[b] == 1 && deg[b] < DEG && !M[a][b]) add_edge(a, b);
        }
    }
}

static void dump(void) {
    int m = 0;
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (u < nb[u][k]) m++;
    printf("%d %d\n", N, m);
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (u < nb[u][k]) printf("%d %d\n", u, nb[u][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    double budget = atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0 || m > MAXE || n > MAXN - 2 ||
        DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &EU[i], &EV[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }

    reset_graph(n);
    for (int i = 0; i < m; i++) {
        int u = EU[i], v = EV[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || M[u][v] || deg[u] >= DEG || deg[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < n; v++) side[v] = -1;
    int ok = 1;
    static int Q[MAXN];
    for (int s = 0; s < n && ok; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        Q[qt++] = s;
        while (qh < qt && ok) {
            int u = Q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    Q[qt++] = w;
                } else if (side[w] == side[u]) {
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
    if (cost_of() != 0) {
        printf("0 0\n");
        return 0;
    }

    while (now() < budget && N < MAXN - 1) {
        double remain = budget - now();
        double alen = remain * 0.35;
        if (alen < 0.3) alen = 0.3;

        take_snapshot();
        int x = N;
        int s0 = rint_(2);
        side[x] = s0;
        deg[x] = 0;
        N++;
        fill_vertex(x);
        if (deg[x] == 0) {
            side[x] = 1 - s0;
            fill_vertex(x);
        }
        if (deg[x] == 0) {
            N--;
            break; /* no spare capacity to attach a new vertex */
        }
        fill_all();

        long long cur = cost_of();
        double ts = now();
        while (cur > 0 && now() - ts < alen) {
            double frac = (now() - ts) / alen;
            double T = pow(0.03, frac);
            if (runif() < 0.12) {
                if (move_add()) cur = cost_of();
                continue;
            }
            Move mv;
            if (!propose(&mv)) continue;
            long long c2 = cost_of();
            long long delta = c2 - cur;
            if (delta <= 0 || runif() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                undo(&mv);
            }
        }
        if (cur != 0) restore_snapshot();
    }

    dump();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Choose a point set S such that
# every line holds at most s = d-q-1 points of S, and every point lies on at
# most s lines indexed by S. Add a new A-vertex per point of S and a new
# B-vertex per line indexed by S.
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
# C growth stage (D = 3): grow a valid graph by one vertex at a time.
# ----------------------------------------------------------------------------

def _grow(d, D, graph, seed, budget):
    """Run the C engine from a valid graph; returns (n, edges). Raises on failure."""
    n, edges = graph
    out = lib.run_c(C_SOURCE, [d, D, seed % 1000003 + 1, f"{budget:.2f}"],
                    stdin_graph=(n, edges), timeout=budget + 6.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
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

    # Arc-extended projective plane graphs. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D == 3:
        # Main search for D = 3: C growth from the best arc graph.
        remaining = time_limit * 0.8 - (time.monotonic() - start) - 2.0
        if remaining >= 1.0:
            try:
                g = _grow(d, D, best, seed, remaining)
                consider(g[0], g[1])
            except Exception:
                pass
    else:
        # Annealed group voltage lifts for D >= 4. For D >= 5 use larger bases.
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
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
