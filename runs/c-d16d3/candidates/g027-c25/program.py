"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C annealing engine.

Starts are valid graphs: the arc-extended PG(2,q) incidence graph, the generalized quadrangle
for D >= 4, or K_{d,d}. Two helpers are new in this version:

1. Bitset energy. The energy of a graph is the number of vertex pairs at distance more than D.
   It is computed with D rounds of bitset OR-propagation over adjacency lists, which is much
   faster than one BFS per vertex.
2. Degree-preserving annealing. Moves are edge switches (a-b, c-e -> a-e, c-b), endpoint shifts
   onto spare vertices, and greedy coverage insertion of new vertices. Annealing lowers the
   energy to zero, which gives a valid graph one vertex larger. Failed growth attempts are rolled
   back to the last valid snapshot.

Python re-checks everything with lib.is_valid. Calibration cases that already sit at the Moore
bound return immediately.
"""
import itertools
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

#define MAXN 1024
#define WORDS 16
#define MAXDEG 64
#define MAXSTART 60000

typedef uint64_t row_t[WORDS];

static int N, W, Dd, Dist;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char adjM[MAXN][MAXN];
static int side[MAXN];
static int bq[MAXN];
static row_t BUFA[MAXN], BUFB[MAXN], RG[MAXN];

static int sN;
static int sdeg[MAXN], sadj[MAXN][MAXDEG];
static int bN, bdeg[MAXN], badj[MAXN][MAXDEG];
static int have_best = 0;
static int startN = 0, startM = 0;
static int su[MAXSTART], sv[MAXSTART];

static uint64_t rs = 88172645463325252ULL;
static double t_end = 0.0;

static int lg_t[16], lg_a[16], lg_b[16], nlg = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ---------------- raw edge operations ---------------- */

static void raw_add(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
    adjM[a][b] = 1;
    adjM[b][a] = 1;
}

static void raw_del(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++) if (adj[a][k] == b) break;
    if (k < deg[a]) { adj[a][k] = adj[a][deg[a] - 1]; deg[a]--; }
    for (k = 0; k < deg[b]; k++) if (adj[b][k] == a) break;
    if (k < deg[b]) { adj[b][k] = adj[b][deg[b] - 1]; deg[b]--; }
    adjM[a][b] = 0;
    adjM[b][a] = 0;
}

/* Logged operations, so a rejected annealing move can be undone. */
static void op_add(int a, int b) {
    raw_add(a, b);
    lg_t[nlg] = 1; lg_a[nlg] = a; lg_b[nlg] = b; nlg++;
}

static void op_del(int a, int b) {
    raw_del(a, b);
    lg_t[nlg] = 0; lg_a[nlg] = a; lg_b[nlg] = b; nlg++;
}

static void undo_all(void) {
    while (nlg > 0) {
        nlg--;
        if (lg_t[nlg]) raw_del(lg_a[nlg], lg_b[nlg]);
        else raw_add(lg_a[nlg], lg_b[nlg]);
    }
}

/* ---------------- bitset reachability and energy ---------------- */

/* Returns R where bit u of R[v] is set iff dist(v,u) <= steps. Uses words < W only. */
static row_t *reach_levels(int steps) {
    row_t *cur = BUFA, *nx = BUFB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < steps; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nx[v][w] |= cur[u][w];
            }
        }
        row_t *t = cur; cur = nx; nx = t;
    }
    return cur;
}

/* Energy = number of unordered vertex pairs at distance > Dist. Zero means valid. */
static long energy(void) {
    row_t *R = reach_levels(Dist);
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

/* ---------------- moves ---------------- */

/* Random cross-side edge, returned with a on side 0 and b on side 1. */
static int rand_edge(int *a, int *b) {
    for (int tries = 0; tries < 64; tries++) {
        int p = rndi(N);
        if (deg[p] == 0) continue;
        int q = adj[p][rndi(deg[p])];
        if (side[p] == 0 && side[q] == 1) { *a = p; *b = q; return 1; }
        if (side[p] == 1 && side[q] == 0) { *a = q; *b = p; return 1; }
    }
    return 0;
}

/* Degree-preserving switch: (a,b),(c,e) -> (a,e),(c,b). */
static int move_switch(void) {
    int a, b, c, e;
    if (!rand_edge(&a, &b)) return 0;
    if (!rand_edge(&c, &e)) return 0;
    if (a == c || b == e || adjM[a][e] || adjM[c][b]) return 0;
    op_del(a, b);
    op_del(c, e);
    op_add(a, e);
    op_add(c, b);
    return 1;
}

/* Move one endpoint of an edge onto a spare vertex on the same side. */
static int move_shift(void) {
    int a, b;
    if (!rand_edge(&a, &b)) return 0;
    int r, o;
    if (rndi(2)) { r = b; o = a; } else { r = a; o = b; }
    int s = -1;
    for (int tries = 0; tries < 64; tries++) {
        int c = rndi(N);
        if (c != r && side[c] == side[r] && deg[c] < Dd && !adjM[c][o]) { s = c; break; }
    }
    if (s < 0) return 0;
    op_del(r, o);
    op_add(s, o);
    return 1;
}

/* Metropolis annealing on the energy. Returns final energy. */
static long anneal(long iters, double T0, double T1) {
    long E = energy();
    for (long it = 0; it < iters && E > 0; it++) {
        if ((it & 31) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        nlg = 0;
        int ok = (rnd01() < 0.7) ? move_switch() : move_shift();
        if (!ok) continue;
        long E2 = energy();
        long dE = E2 - E;
        if (dE <= 0 || rnd01() < exp(-(double)dE / T)) E = E2;
        else undo_all();
    }
    nlg = 0;
    return E;
}

/* Fill cross-side pairs where both endpoints have spare degree. Never increases energy. */
static void fill_spares(void) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int a = 0; a < N; a++) {
            if (side[a] != 0 || deg[a] >= Dd) continue;
            for (int b = 0; b < N && deg[a] < Dd; b++) {
                if (side[b] != 1 || deg[b] >= Dd || adjM[a][b]) continue;
                raw_add(a, b);
                changed = 1;
            }
        }
    }
}

/* Add a new vertex on side X, joined greedily to other-side vertices so that
   every old vertex lies within distance Dist-1 of some chosen neighbour. */
static void grow(int X) {
    int Nold = N;
    int Wold = W;
    row_t *R = reach_levels(Dist - 1);
    for (int v = 0; v < Nold; v++)
        for (int w = 0; w < Wold; w++) RG[v][w] = R[v][w];
    row_t U;
    for (int w = 0; w < WORDS; w++) U[w] = 0;
    for (int v = 0; v < Nold; v++) U[v >> 6] |= 1ULL << (v & 63);

    int x = Nold;
    N = Nold + 1;
    side[x] = X;
    deg[x] = 0;
    for (int i = 0; i < N; i++) { adjM[x][i] = 0; adjM[i][x] = 0; }

    while (deg[x] < Dd) {
        int best = -1;
        long bk = -1;
        for (int t = 0; t < Nold; t++) {
            if (side[t] == X || deg[t] >= Dd) continue;
            int g = 0;
            for (int w = 0; w < Wold; w++) g += popc(RG[t][w] & U[w]);
            if (g <= 0) continue;
            long key = (long)g * 8 + rndi(8);
            if (key > bk) { bk = key; best = t; }
        }
        if (best < 0) break;
        raw_add(x, best);
        for (int w = 0; w < Wold; w++) U[w] &= ~RG[best][w];
    }
    W = (N + 63) / 64;
}

/* ---------------- snapshots and output ---------------- */

static void save_state(int *dn, int *dd, int da[][MAXDEG]) {
    *dn = N;
    for (int v = 0; v < N; v++) {
        dd[v] = deg[v];
        for (int k = 0; k < deg[v]; k++) da[v][k] = adj[v][k];
    }
}

static void load_state(int sn, int *dd, int da[][MAXDEG]) {
    for (int v = 0; v < N; v++)
        for (int u = 0; u < N; u++) adjM[v][u] = 0;
    N = sn;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        deg[v] = dd[v];
        for (int k = 0; k < deg[v]; k++) {
            adj[v][k] = da[v][k];
            adjM[v][adj[v][k]] = 1;
        }
    }
}

static void print_graph(int nn, int *dd, int da[][MAXDEG]) {
    long M = 0;
    for (int v = 0; v < nn; v++)
        for (int k = 0; k < dd[v]; k++)
            if (da[v][k] > v) M++;
    printf("%d %ld\n", nn, M);
    for (int v = 0; v < nn; v++)
        for (int k = 0; k < dd[v]; k++)
            if (da[v][k] > v) printf("%d %d\n", v, da[v][k]);
}

/* ---------------- main ---------------- */

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    if (Dd < 1) Dd = 1;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 80) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    W = (N + 63) / 64;
    startN = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (adjM[u][v] || deg[u] >= Dd || deg[v] >= Dd) continue;
        raw_add(u, v);
        if (startM < MAXSTART) { su[startM] = u; sv[startM] = v; startM++; }
    }

    if (Dist < 2) {
        printf("%d %d\n", startN, startM);
        for (int i = 0; i < startM; i++) printf("%d %d\n", su[i], sv[i]);
        return 0;
    }

    /* 2-colour the graph; the switch moves assume edges cross between sides. */
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    t_end = now() + budget;
    fill_spares();
    long E = anneal(200000L, 2.0, 0.05);
    if (E == 0) {
        save_state(&bN, bdeg, badj);
        have_best = 1;
    }
    if (!have_best) {
        printf("%d %d\n", startN, startM);
        for (int i = 0; i < startM; i++) printf("%d %d\n", su[i], sv[i]);
        return 0;
    }
    if (E != 0) load_state(bN, bdeg, badj);

    /* Growth loop: each attempt adds one vertex and anneals back to energy zero. */
    int fails = 0;
    while (now() < t_end && fails < 300 && N < MAXN - 2) {
        save_state(&sN, sdeg, sadj);
        grow(rndi(2));
        fill_spares();
        long iters = 3000L + 8L * N;
        long E2 = anneal(iters, 1.5, 0.05);
        if (E2 == 0) {
            save_state(&bN, bdeg, badj);
            fails = 0;
        } else {
            load_state(sN, sdeg, sadj);
            fails++;
        }
    }

    print_graph(bN, bdeg, badj);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has spare capacity s = d - q - 1. Choose a point set S that is an arc, so each
# line holds at most s points of S. Add an A-vertex for each P in S (joined to
# lines through P) and a B-vertex for each j in S (joined to points on line j).
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# C engine driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C annealing engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    starts.sort(key=lambda g: -g[0])
    best = starts[0]

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Anneal from the top start with most of the time, then keep growing the result.
    src = best
    for idx, frac in enumerate((0.6, 1.0)):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        share = remaining * frac if idx == 0 else remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.5, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)
            src = best

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
