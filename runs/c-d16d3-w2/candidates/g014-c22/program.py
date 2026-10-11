import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing on bipartite graphs with a fixed side
# assignment and max degree d. The cost is the number of vertex pairs at
# distance > D (bitset BFS). Moves: endpoint rewiring to a deficit vertex,
# edge addition, edge removal, and degree-preserving double swaps. Whenever a
# zero-cost graph is reached, a new vertex is added and the search continues.
# On failure it restores the best valid graph and tries again.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1000
#define MAXW 16
#define MAXDEG 64
#define MAXE 40000
#define PHASE 50000L

static int DEG, DIAM, N, ne;
static int side[MAXN], deg[MAXN], nd[MAXN];
static int nb[MAXN][MAXDEG];
static int eu[MAXE], ev[MAXE];
static int eid[MAXN][MAXN];
static uint64_t R[2][MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static double time_end;
static int cur_cost;
static int have_best, bestN, bestM;
static int bu[MAXE], bv[MAXE];
static int mk, p1, q1, p2, q2;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void clear_state(void) {
    for (int k = 0; k < ne; k++) {
        eid[eu[k]][ev[k]] = -1;
        eid[ev[k]][eu[k]] = -1;
    }
    for (int v = 0; v < N; v++) deg[v] = 0;
    ne = 0;
}

static void add_pair(int p, int q) {
    int a = (side[p] == 0) ? p : q;
    int b = (side[p] == 0) ? q : p;
    eu[ne] = a; ev[ne] = b;
    eid[p][q] = ne; eid[q][p] = ne;
    deg[p]++; deg[q]++;
    ne++;
}

static void remove_pair(int p, int q) {
    int k = eid[p][q];
    int last = ne - 1;
    if (k != last) {
        eu[k] = eu[last]; ev[k] = ev[last];
        eid[eu[k]][ev[k]] = k;
        eid[ev[k]][eu[k]] = k;
    }
    eid[p][q] = -1; eid[q][p] = -1;
    deg[p]--; deg[q]--;
    ne--;
}

static int cost_eval(void) {
    int n = N, W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) nd[v] = 0;
    for (int k = 0; k < ne; k++) {
        int a = eu[k], b = ev[k];
        nb[a][nd[a]++] = b;
        nb[b][nd[b]++] = a;
    }
    int cur = 0;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) R[0][v][w] = 0;
        R[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        int nx = 1 - cur;
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) R[nx][v][w] = R[cur][v][w];
            for (int j = 0; j < nd[v]; j++) {
                int u = nb[v][j];
                for (int w = 0; w < W; w++) R[nx][v][w] |= R[cur][u][w];
            }
        }
        cur = nx;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R[cur][v][w]);
        total += n - c;
    }
    return (int)(total / 2);
}

static int pick_deficit(void) {
    for (int t = 0; t < 24; t++) {
        int v = rnd_int(N);
        if (deg[v] < DEG) return v;
    }
    int cnt = 0, pick = -1;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEG) {
            cnt++;
            if (rnd_int(cnt) == 0) pick = v;
        }
    }
    return pick;
}

/* Propose a move; fills mk and p1,q1,p2,q2. Returns 0 if no move is available. */
static int propose(void) {
    double r = rnd_unit();
    if (r < 0.40) {
        int y = (rnd_unit() < 0.5 && deg[N - 1] < DEG) ? N - 1 : pick_deficit();
        if (y < 0 || ne == 0) return 0;
        int k = rnd_int(ne);
        int a = eu[k], b = ev[k];
        int o;
        if (side[y] == 0) {
            if (y == a) return 0;
            o = b;
        } else {
            if (y == b) return 0;
            o = a;
        }
        if (eid[y][o] >= 0) return 0;
        mk = 0; p1 = a; q1 = b; p2 = y; q2 = o;
        return 1;
    } else if (r < 0.65) {
        int u = (rnd_unit() < 0.5 && deg[N - 1] < DEG) ? N - 1 : pick_deficit();
        if (u < 0) return 0;
        int v = -1;
        for (int t = 0; t < 30; t++) {
            int w = rnd_int(N);
            if (side[w] != side[u] && deg[w] < DEG && eid[u][w] < 0) { v = w; break; }
        }
        if (v < 0) return 0;
        mk = 1; p1 = u; q1 = v;
        return 1;
    } else if (r < 0.75) {
        if (ne == 0) return 0;
        int k = rnd_int(ne);
        mk = 2; p1 = eu[k]; q1 = ev[k];
        return 1;
    } else {
        if (ne < 2) return 0;
        int k1 = rnd_int(ne), k2 = rnd_int(ne);
        if (k1 == k2) return 0;
        int a = eu[k1], b = ev[k1], c = eu[k2], e = ev[k2];
        if (a == c || b == e) return 0;
        if (eid[a][e] >= 0 || eid[c][b] >= 0) return 0;
        mk = 3; p1 = a; q1 = b; p2 = c; q2 = e;
        return 1;
    }
}

static void apply(int fwd) {
    switch (mk) {
    case 0:
        if (fwd) { remove_pair(p1, q1); add_pair(p2, q2); }
        else     { remove_pair(p2, q2); add_pair(p1, q1); }
        break;
    case 1:
        if (fwd) add_pair(p1, q1);
        else     remove_pair(p1, q1);
        break;
    case 2:
        if (fwd) remove_pair(p1, q1);
        else     add_pair(p1, q1);
        break;
    case 3:
        if (fwd) {
            remove_pair(p1, q1); remove_pair(p2, q2);
            add_pair(p1, q2); add_pair(p2, q1);
        } else {
            remove_pair(p1, q2); remove_pair(p2, q1);
            add_pair(p1, q1); add_pair(p2, q2);
        }
        break;
    }
}

static int anneal(long iters, double T0, double T1) {
    for (long it = 0; it < iters && cur_cost > 0; it++) {
        if ((it & 127) == 0 && now_sec() > time_end) return 0;
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        if (!propose()) continue;
        apply(1);
        int c2 = cost_eval();
        int delta = c2 - cur_cost;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            cur_cost = c2;
        } else {
            apply(0);
        }
    }
    return 1;
}

static void save_best(void) {
    have_best = 1;
    bestN = N;
    bestM = ne;
    for (int k = 0; k < ne; k++) { bu[k] = eu[k]; bv[k] = ev[k]; }
}

static void load_best(void) {
    clear_state();
    N = bestN;
    for (int k = 0; k < bestM; k++) add_pair(bu[k], bv[k]);
    cur_cost = cost_eval();
}

static void grow(void) {
    if (N >= MAXN - 1) return;
    side[N] = rnd_int(2);
    deg[N] = 0;
    N++;
    cur_cost = cost_eval();
}

int main(int argc, char **argv) {
    static int su[MAXE], sv[MAXE];
    static int stk[MAXN];
    int n = 0, m = 0, ok = 1;
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    time_end = now_sec() + atof(argv[4]);
    for (int i = 0; i < MAXN; i++)
        for (int j = 0; j < MAXN; j++) eid[i][j] = -1;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n < 2 || n > MAXN - 2 || m < 0 || m > MAXE - 1 || DEG < 1 || DEG >= MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < n; i++) { deg[i] = 0; nd[i] = 0; side[i] = -1; }
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) { ok = 0; break; }
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) { ok = 0; break; }
        if (nd[a] >= DEG || nd[b] >= DEG) { ok = 0; break; }
        su[i] = a; sv[i] = b;
        nb[a][nd[a]++] = b;
        nb[b][nd[b]++] = a;
    }
    if (ok) {
        for (int s = 0; s < n && ok; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0 && ok) {
                int u = stk[--sp];
                for (int j = 0; j < nd[u]; j++) {
                    int w = nb[u][j];
                    if (side[w] < 0) { side[w] = 1 - side[u]; stk[sp++] = w; }
                    else if (side[w] == side[u]) { ok = 0; break; }
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    ne = 0;
    for (int i = 0; i < m; i++)
        if (eid[su[i]][sv[i]] < 0) add_pair(su[i], sv[i]);

    cur_cost = cost_eval();
    have_best = 0;
    if (cur_cost == 0) save_best();

    while (now_sec() < time_end) {
        if (cur_cost == 0) {
            save_best();
            if (N >= MAXN - 1) break;
            grow();
            continue;
        }
        int finished = anneal(PHASE, 2.0, 0.15);
        if (!finished) break;
        if (cur_cost > 0 && have_best) {
            load_best();
            grow();
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int k = 0; k < bestM; k++) printf("%d %d\n", bu[k], bv[k]);
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
# Build: best algebraic start, then the C annealing engine grows it.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold step: anneal from the best start, growing one vertex at a time.
    if D >= 2 and d <= 60 and best_n <= 900:
        elapsed = time.monotonic() - t0
        budget = 0.85 * time_limit - elapsed - 4.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=budget + 8.0)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
