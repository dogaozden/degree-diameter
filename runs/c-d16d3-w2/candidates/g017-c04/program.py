import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over bipartite graphs with max degree d,
# minimizing the number of vertex pairs at distance > D. Only zero-cost states
# are recorded, so the output is valid whenever it is non-empty. Moves: insert a
# vertex with d opposite-side neighbours (stealing slots when needed), delete a
# vertex (relabelling the last one), and rewire one edge endpoint.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2048
#define WMAX 32
#define DMAX 64

typedef struct {
    int n;
    int deg[NMAX];
    int side[NMAX];
    int adj[NMAX][DMAX];
} State;

static State cur, saved, best;
static int Dd = 3, DIAM = 3;
static int bestN = -1;
static uint64_t rs = 1;
static uint64_t RA[NMAX][WMAX], RB[NMAX][WMAX];
static int cand[NMAX];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
static double urand(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void copy_state(State *dst, const State *src) {
    int n = src->n;
    dst->n = n;
    memcpy(dst->deg, src->deg, sizeof(int) * n);
    memcpy(dst->side, src->side, sizeof(int) * n);
    memcpy(dst->adj, src->adj, sizeof(int) * DMAX * n);
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static long long cost_of(void) {
    int n = cur.n;
    if (n <= 1) return 0;
    int nw = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) RA[v][w] = 0;
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*c)[WMAX] = RA;
    uint64_t (*x)[WMAX] = RB;
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) x[v][w] = c[v][w];
            for (int k = 0; k < cur.deg[v]; k++) {
                int u = cur.adj[v][k];
                for (int w = 0; w < nw; w++) x[v][w] |= c[u][w];
            }
        }
        uint64_t (*t)[WMAX] = c;
        c = x;
        x = t;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < nw; w++) cnt += pop64(c[v][w]);
        tot += n - cnt;
    }
    return tot / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < cur.deg[a]; k++) if (cur.adj[a][k] == b) return 1;
    return 0;
}
static void rm_half(int a, int b) {
    for (int k = 0; k < cur.deg[a]; k++) {
        if (cur.adj[a][k] == b) {
            cur.adj[a][k] = cur.adj[a][cur.deg[a] - 1];
            cur.deg[a]--;
            return;
        }
    }
}
static void del_edge(int a, int b) { rm_half(a, b); rm_half(b, a); }
static void add_edge(int a, int b) {
    cur.adj[a][cur.deg[a]++] = b;
    cur.adj[b][cur.deg[b]++] = a;
}

/* Insert a new vertex on a random side joined to up to Dd opposite-side vertices. */
static int move_add(void) {
    int n = cur.n;
    if (n >= NMAX - 1) return 0;
    int s = rnd_int(2);
    int nc = 0;
    for (int u = 0; u < n; u++) if (cur.side[u] != s) cand[nc++] = u;
    if (nc == 0) return 0;
    int k = Dd < nc ? Dd : nc;
    int v = n;
    cur.n = n + 1;
    cur.side[v] = s;
    cur.deg[v] = 0;
    for (int i = 0; i < k; i++) {
        int j = i + rnd_int(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
        int u = cand[i];
        if (cur.deg[u] >= Dd) {
            int w = cur.adj[u][rnd_int(cur.deg[u])];
            del_edge(u, w);
        }
        add_edge(v, u);
    }
    return 1;
}

/* Delete a random vertex and move the last vertex into its slot. */
static int move_remove(void) {
    int n = cur.n;
    if (n <= 2) return 0;
    int v = rnd_int(n);
    while (cur.deg[v] > 0) {
        int u = cur.adj[v][0];
        del_edge(v, u);
    }
    int L = n - 1;
    if (v != L) {
        for (int k = 0; k < cur.deg[L]; k++) {
            int u = cur.adj[L][k];
            for (int j = 0; j < cur.deg[u]; j++) {
                if (cur.adj[u][j] == L) { cur.adj[u][j] = v; break; }
            }
        }
        memcpy(cur.adj[v], cur.adj[L], sizeof(int) * DMAX);
        cur.deg[v] = cur.deg[L];
        cur.side[v] = cur.side[L];
    }
    cur.n = n - 1;
    return 1;
}

/* Move one edge endpoint: edge x-y becomes x-z, with z on y's side. */
static int move_rewire(void) {
    int n = cur.n;
    int x = rnd_int(n);
    if (cur.deg[x] == 0) return 0;
    int y = cur.adj[x][rnd_int(cur.deg[x])];
    int z = -1;
    for (int t = 0; t < 30; t++) {
        int c = rnd_int(n);
        if (c == y || cur.side[c] != cur.side[y]) continue;
        if (has_edge(c, x)) continue;
        z = c;
        break;
    }
    if (z < 0) return 0;
    del_edge(x, y);
    if (cur.deg[z] >= Dd) {
        int w = cur.adj[z][rnd_int(cur.deg[z])];
        del_edge(z, w);
    }
    add_edge(x, z);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long seed = (unsigned long)atol(argv[3]);
    double budget = atof(argv[4]);
    Dd = d;
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n >= NMAX - 1 || d < 1 || d > DMAX || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    memset(&cur, 0, sizeof cur);
    cur.n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || cur.deg[u] >= Dd || cur.deg[v] >= Dd) {
            printf("0 0\n");
            return 0;
        }
        cur.adj[u][cur.deg[u]++] = v;
        cur.adj[v][cur.deg[v]++] = u;
    }
    /* 2-colour the start graph; reject if it is not bipartite. */
    static int col[NMAX], queue[NMAX];
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int qh = 0, qt = 0;
        col[s] = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int k = 0; k < cur.deg[x]; k++) {
                int y = cur.adj[x][k];
                if (col[y] < 0) { col[y] = 1 - col[x]; queue[qt++] = y; }
                else if (col[y] == col[x]) { printf("0 0\n"); return 0; }
            }
        }
    }
    for (int i = 0; i < n; i++) cur.side[i] = col[i];

    long long cost = cost_of();
    if (cost == 0) { copy_state(&best, &cur); bestN = cur.n; }

    double t0 = clock() / (double)CLOCKS_PER_SEC;
    const long long CYC = 20000;
    const double T0 = 2.0;
    long long cpos = 0, it = 0;

    while (1) {
        if ((it & 31) == 0) {
            double now = clock() / (double)CLOCKS_PER_SEC;
            if (now - t0 > budget) break;
        }
        it++;
        if (cpos >= CYC) {
            cpos = 0;
            if (bestN >= 0) { copy_state(&cur, &best); cost = 0; }
        }
        double frac = (double)cpos / (double)CYC;
        double T = T0 * pow(0.05, frac);
        cpos++;

        copy_state(&saved, &cur);
        int mv = rnd_int(100);
        int ok;
        if (mv < 35) ok = move_add();
        else if (mv < 50) ok = move_remove();
        else ok = move_rewire();
        if (!ok) continue;

        long long nc = cost_of();
        double delta = (double)(nc - cost);
        if (delta <= 0 || urand() < exp(-delta / T)) {
            cost = nc;
            if (cost == 0 && cur.n > bestN) {
                copy_state(&best, &cur);
                bestN = cur.n;
            }
        } else {
            copy_state(&cur, &saved);
        }
    }

    State *o = (bestN >= 0) ? &best : &cur;
    long long m2 = 0;
    for (int v = 0; v < o->n; v++) m2 += o->deg[v];
    m2 /= 2;
    printf("%d %lld\n", o->n, m2);
    for (int v = 0; v < o->n; v++) {
        for (int k = 0; k < o->deg[v]; k++) {
            int u = o->adj[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add one vertex per point of a
# set SA (joined to its q+1 lines) and one per line of a set SB, with load
# constraints. Order is 2(q^2+q+1) + |SA| + |SB|.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the same load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
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
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

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

    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3 and best_n < moore:
        try:
            cands = _arc_extensions(d, start + 0.25 * time_limit,
                                    random.Random(seed * 7919 + d))
            for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
                consider(n_c, e_c)
        except Exception:
            pass

    if D >= 4 and best_n < moore and time.monotonic() < start + 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Main search: C simulated annealing that tries to grow the best valid graph.
    if 2 <= d <= 60 and best_n < moore:
        remaining = start + 0.85 * time_limit - time.monotonic() - 3.0
        if remaining > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                stdin_graph=best, timeout=remaining + 3.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
