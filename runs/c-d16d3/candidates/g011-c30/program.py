import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. An A-vertex joined to the q+1 lines
# through a chosen point P (set SA), and a B-vertex joined to the q+1 points on
# a chosen line j (set SB). Loads: each line sees <= s of SA, each point <= s of SB.
# For odd q with s = 2 this gives 2(q^2+q+1) + 2(q+1) vertices.
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
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so every target is hit by <= s chosen elements."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# C engine: degree-preserving annealing with vertex growth.
#
# Idea: keep a valid bipartite graph with max degree d and diameter <= D. Add a new
# vertex on one side, wired to opposite-side vertices with spare degree. Then anneal
# the cost (number of unordered vertex pairs farther than D) using degree-preserving
# 2-switches and endpoint rewires, plus add/remove edge moves. Each time the cost hits
# zero, snapshot the graph and grow again. Bitset BFS gives the exact cost each step.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int N, E, DEG, DIAM, NCAP, ECAP, WMAX;
static int *side, *deg, *eu, *ev, *off, *adjv, *fillp, *cand;
static unsigned char *M;
static u64 *bufA, *bufB;
static int sN = 0, sE = 0, have_snap = 0;
static int *sside, *seu, *sev;
static u64 rs = 88172645463325252ULL;

#define MI(a, b) ((size_t)(a) * (size_t)NCAP + (size_t)(b))

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void print_graph(int n, int m, const int *u, const int *v) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", u[i], v[i]);
}

/* Number of unordered pairs at distance > DIAM (unreachable counts as bad). */
static long long bad_pairs(void) {
    int Wn = (N + 63) >> 6;
    off[0] = 0;
    for (int v = 0; v < N; v++) off[v + 1] = off[v] + deg[v];
    for (int v = 0; v < N; v++) fillp[v] = off[v];
    for (int i = 0; i < E; i++) {
        adjv[fillp[eu[i]]++] = ev[i];
        adjv[fillp[ev[i]]++] = eu[i];
    }
    u64 *A = bufA, *B = bufB;
    memset(A, 0, sizeof(u64) * (size_t)N * (size_t)Wn);
    for (int v = 0; v < N; v++) A[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int st = 0; st < DIAM; st++) {
        for (int v = 0; v < N; v++) {
            u64 *o = B + (size_t)v * Wn;
            const u64 *c = A + (size_t)v * Wn;
            for (int w = 0; w < Wn; w++) o[w] = c[w];
            for (int k = off[v]; k < off[v + 1]; k++) {
                const u64 *cu = A + (size_t)adjv[k] * Wn;
                for (int w = 0; w < Wn; w++) o[w] |= cu[w];
            }
        }
        u64 *t = A; A = B; B = t;
    }
    long long tot = 0;
    size_t len = (size_t)N * (size_t)Wn;
    for (size_t i = 0; i < len; i++) tot += popc(A[i]);
    return ((long long)N * N - tot) / 2;
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    if (T <= 1e-9) return 0;
    return rnd01() < exp(-(double)delta / T);
}

static void add_raw(int a, int b) {
    int x = a, y = b;
    if (side[a]) { x = b; y = a; }
    M[MI(x, y)] = 1;
    deg[x]++;
    deg[y]++;
    eu[E] = x;
    ev[E] = y;
    E++;
}

static int find_spare(int s) {
    for (int t = 0; t < 40; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] < DEG) return v;
    }
    return -1;
}

static void try_switch(double T, long long *cost) {
    if (E < 2) return;
    int i = rndint(E), j = rndint(E);
    if (i == j) return;
    int a = eu[i], b = ev[i], c = eu[j], dd = ev[j];
    if (M[MI(a, dd)] || M[MI(c, b)]) return;
    M[MI(a, b)] = 0; M[MI(c, dd)] = 0;
    M[MI(a, dd)] = 1; M[MI(c, b)] = 1;
    ev[i] = dd; ev[j] = b;
    long long nc = bad_pairs();
    if (accept(nc - *cost, T)) { *cost = nc; return; }
    M[MI(a, dd)] = 0; M[MI(c, b)] = 0;
    M[MI(a, b)] = 1; M[MI(c, dd)] = 1;
    ev[i] = b; ev[j] = dd;
}

static void try_rewire(double T, long long *cost) {
    if (E < 1) return;
    int i = rndint(E), a = eu[i], b = ev[i];
    if (rndint(2) == 0) {
        int y = find_spare(1);
        if (y < 0 || y == b || M[MI(a, y)]) return;
        M[MI(a, b)] = 0; M[MI(a, y)] = 1;
        deg[b]--; deg[y]++; ev[i] = y;
        long long nc = bad_pairs();
        if (accept(nc - *cost, T)) { *cost = nc; return; }
        M[MI(a, y)] = 0; M[MI(a, b)] = 1;
        deg[y]--; deg[b]++; ev[i] = b;
    } else {
        int x = find_spare(0);
        if (x < 0 || x == a || M[MI(x, b)]) return;
        M[MI(a, b)] = 0; M[MI(x, b)] = 1;
        deg[a]--; deg[x]++; eu[i] = x;
        long long nc = bad_pairs();
        if (accept(nc - *cost, T)) { *cost = nc; return; }
        M[MI(x, b)] = 0; M[MI(a, b)] = 1;
        deg[x]--; deg[a]++; eu[i] = a;
    }
}

static void try_add(double T, long long *cost) {
    if (E >= ECAP) return;
    int x = find_spare(0), y = find_spare(1);
    if (x < 0 || y < 0 || M[MI(x, y)]) return;
    add_raw(x, y);
    long long nc = bad_pairs();
    if (accept(nc - *cost, T)) { *cost = nc; return; }
    E--;
    M[MI(x, y)] = 0; deg[x]--; deg[y]--;
}

static void try_remove(double T, long long *cost) {
    if (E < 1) return;
    int i = rndint(E), a = eu[i], b = ev[i];
    M[MI(a, b)] = 0; deg[a]--; deg[b]--;
    eu[i] = eu[E - 1]; ev[i] = ev[E - 1];
    E--;
    long long nc = bad_pairs();
    if (accept(nc - *cost, T)) { *cost = nc; return; }
    eu[E] = a; ev[E] = b; E++;
    M[MI(a, b)] = 1; deg[a]++; deg[b]++;
}

/* Add one vertex on a random side, wired to up to DEG opposite vertices with spare degree. */
static int add_vertex(void) {
    if (N >= NCAP) return 0;
    int s0 = rndint(2);
    for (int t = 0; t < 2; t++) {
        int sd = (s0 + t) & 1;
        int cnt = 0;
        for (int u = 0; u < N; u++)
            if (side[u] != sd && deg[u] < DEG) cand[cnt++] = u;
        if (cnt == 0) continue;
        for (int k = cnt - 1; k > 0; k--) {
            int r = rndint(k + 1);
            int tmp = cand[k]; cand[k] = cand[r]; cand[r] = tmp;
        }
        int v = N;
        N++;
        side[v] = sd;
        deg[v] = 0;
        int k = cnt < DEG ? cnt : DEG;
        for (int q = 0; q < k; q++) add_raw(v, cand[q]);
        return 1;
    }
    return 0;
}

static void snap_save(void) {
    sN = N; sE = E; have_snap = 1;
    memcpy(sside, side, sizeof(int) * (size_t)N);
    memcpy(seu, eu, sizeof(int) * (size_t)E);
    memcpy(sev, ev, sizeof(int) * (size_t)E);
}

static void restore(void) {
    memset(M, 0, (size_t)NCAP * (size_t)NCAP);
    memset(deg, 0, sizeof(int) * (size_t)NCAP);
    N = sN; E = sE;
    memcpy(side, sside, sizeof(int) * (size_t)N);
    memcpy(eu, seu, sizeof(int) * (size_t)E);
    memcpy(ev, sev, sizeof(int) * (size_t)E);
    for (int i = 0; i < E; i++) {
        M[MI(eu[i], ev[i])] = 1;
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double budget = atof(argv[4]);
    double t_end = cpu() + budget;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *ru = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *rv = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) { m0 = i; break; }
    }
    if (n0 > 3000 || DEG < 1 || DIAM < 2) {
        print_graph(n0, m0, ru, rv);
        return 0;
    }

    /* 2-colour the input (bipartite check). */
    int *rd = calloc((size_t)n0, sizeof(int));
    for (int i = 0; i < m0; i++) { rd[ru[i]]++; rd[rv[i]]++; }
    int *ro = malloc(sizeof(int) * (size_t)(n0 + 1));
    ro[0] = 0;
    for (int v = 0; v < n0; v++) ro[v + 1] = ro[v] + rd[v];
    int *ra = malloc(sizeof(int) * (size_t)(2 * m0 + 1));
    int *fp = malloc(sizeof(int) * (size_t)n0);
    for (int v = 0; v < n0; v++) fp[v] = ro[v];
    for (int i = 0; i < m0; i++) {
        ra[fp[ru[i]]++] = rv[i];
        ra[fp[rv[i]]++] = ru[i];
    }
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *qu = malloc(sizeof(int) * (size_t)n0);
    for (int v = 0; v < n0; v++) col[v] = -1;
    int ok = 1;
    for (int s = 0; s < n0 && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail && ok) {
            int u = qu[head++];
            for (int k = ro[u]; k < ro[u + 1]; k++) {
                int w = ra[k];
                if (col[w] < 0) { col[w] = 1 - col[u]; qu[tail++] = w; }
                else if (col[w] == col[u]) { ok = 0; break; }
            }
        }
    }
    if (!ok) {
        print_graph(n0, m0, ru, rv);
        return 0;
    }

    NCAP = n0 + 1500 + n0 / 4;
    ECAP = NCAP * DEG + 16;
    WMAX = (NCAP + 63) >> 6;
    side = calloc((size_t)NCAP, sizeof(int));
    deg = calloc((size_t)NCAP, sizeof(int));
    eu = malloc(sizeof(int) * (size_t)ECAP);
    ev = malloc(sizeof(int) * (size_t)ECAP);
    off = malloc(sizeof(int) * (size_t)(NCAP + 1));
    adjv = malloc(sizeof(int) * (size_t)(2 * ECAP));
    fillp = malloc(sizeof(int) * (size_t)NCAP);
    cand = malloc(sizeof(int) * (size_t)NCAP);
    M = calloc((size_t)NCAP * (size_t)NCAP, 1);
    bufA = malloc(sizeof(u64) * (size_t)NCAP * (size_t)WMAX);
    bufB = malloc(sizeof(u64) * (size_t)NCAP * (size_t)WMAX);
    sside = malloc(sizeof(int) * (size_t)NCAP);
    seu = malloc(sizeof(int) * (size_t)ECAP);
    sev = malloc(sizeof(int) * (size_t)ECAP);

    N = n0; E = 0;
    for (int v = 0; v < n0; v++) side[v] = col[v];
    for (int i = 0; i < m0; i++) {
        int a = ru[i], b = rv[i];
        if (side[a] == side[b] || M[MI(a, b)] || M[MI(b, a)] || a == b) continue;
        if (side[a] == 0) add_raw(a, b); else add_raw(b, a);
    }

    long long cost = bad_pairs();
    if (cost == 0) snap_save();
    if (cost == 0) {
        if (add_vertex()) cost = bad_pairs();
    }

    int stuck = 0;
    const int PH = 6000;
    const double T0 = 1.5;
    while (cpu() < t_end) {
        for (int it = 0; it < PH; it++) {
            if (cost == 0 && !stuck) break;
            if ((it & 31) == 0 && cpu() >= t_end) break;
            double T = T0 * (1.0 - (double)it / PH) + 0.03;
            double r = rnd01();
            if (r < 0.40) try_switch(T, &cost);
            else if (r < 0.70) try_rewire(T, &cost);
            else if (r < 0.85) try_add(T, &cost);
            else try_remove(T, &cost);
        }
        if (cpu() >= t_end) break;
        if (cost == 0) {
            snap_save();
            stuck = 0;
            if (add_vertex()) cost = bad_pairs();
            else stuck = 1;
        } else if (have_snap) {
            restore();
            stuck = 0;
            if (add_vertex()) cost = bad_pairs();
            else { stuck = 1; cost = bad_pairs(); }
        }
    }

    if (have_snap) {
        printf("%d %d\n", sN, sE);
        for (int i = 0; i < sE; i++) printf("%d %d\n", seu[i], sev[i]);
    } else {
        print_graph(n0, m0, ru, rv);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _has_spare(n, edges, d):
    """True if some vertex has degree below d (room to grow)."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return any(x < d for x in deg)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs: valid for D >= 3.
    if D >= 3:
        for n_c, e_c in _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Generalized quadrangle baseline for D >= 4 (cheap for small d).
    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Grow the best start graph with the C annealing engine.
    remaining = 0.9 * time_limit - (time.monotonic() - t0)
    if D >= 3 and best_n <= 3000 and remaining > 4 and _has_spare(best_n, best[1], d):
        budget = 0.8 * remaining - 1.0
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=0.95 * remaining)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
