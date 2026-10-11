import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: repair / growth search on bipartite graphs.
#
# Starts from a valid bipartite graph (vertices 0..n-1, side 0 / side 1).
# Repeatedly adds one A-vertex and one B-vertex, fills spare degree greedily,
# then runs simulated annealing over edge moves (endpoint rewire, edge swap,
# edge add). Cost = number of unordered vertex pairs at distance > D, computed
# with bitset BFS. Degree <= d and bipartiteness are maintained by every move.
# On cost 0 the graph is saved and growth continues; otherwise the best saved
# graph is restored and growth is retried with fresh randomness.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXADD 48

static int dd, DD;
static int CAP, WCAP, ECAP;
static int N, E;
static int *deg, *adjL, *side, *sl[2], ns[2], *eu, *ev, *bu, *bv;
static int bestN, bestM;
static unsigned char *M;
static uint64_t *R1, *R2;
static uint64_t rs;
static clock_t T_START;

static void die(const char *msg) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
}

static double elapsed(void) {
    return (double)(clock() - T_START) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static inline int isadj(int a, int b) {
    return M[(size_t)a * CAP + b];
}

static void setM(int a, int b, int v) {
    M[(size_t)a * CAP + b] = (unsigned char)v;
    M[(size_t)b * CAP + a] = (unsigned char)v;
}

static void adj_push(int v, int u) {
    adjL[(size_t)v * dd + deg[v]] = u;
    deg[v]++;
}

static void adj_remove(int v, int u) {
    int *p = adjL + (size_t)v * dd;
    for (int i = 0; i < deg[v]; i++) {
        if (p[i] == u) {
            p[i] = p[deg[v] - 1];
            deg[v]--;
            return;
        }
    }
    die("adj_remove: missing neighbour");
}

static void adj_replace(int v, int o, int nw) {
    int *p = adjL + (size_t)v * dd;
    for (int i = 0; i < deg[v]; i++) {
        if (p[i] == o) {
            p[i] = nw;
            return;
        }
    }
    die("adj_replace: missing neighbour");
}

static void add_edge(int a, int b) {
    eu[E] = a;
    ev[E] = b;
    E++;
    adj_push(a, b);
    adj_push(b, a);
    setM(a, b, 1);
}

/* Move endpoint on side s of edge e to vertex nv (same side as the old endpoint). */
static void move_end(int e, int s, int nv) {
    int a = eu[e], b = ev[e];
    int ov = (s == 0) ? a : b;
    int oth = (s == 0) ? b : a;
    adj_remove(ov, oth);
    adj_replace(oth, ov, nv);
    adj_push(nv, oth);
    setM(ov, oth, 0);
    setM(nv, oth, 1);
    if (s == 0) eu[e] = nv;
    else ev[e] = nv;
}

/* Edges e1=(a,b), e2=(c,e) become (a,e), (c,b). Self-inverse on the current edge list. */
static void do_swap(int e1, int e2) {
    int a = eu[e1], b = ev[e1], c = eu[e2], e = ev[e2];
    adj_replace(a, b, e);
    adj_replace(b, a, c);
    adj_replace(c, e, b);
    adj_replace(e, c, a);
    setM(a, b, 0);
    setM(c, e, 0);
    setM(a, e, 1);
    setM(c, b, 1);
    eu[e1] = a;
    ev[e1] = e;
    eu[e2] = c;
    ev[e2] = b;
}

/* Number of unordered pairs at distance > DD (bitset BFS). */
static long cost_eval(void) {
    int w = (N + 63) >> 6;
    uint64_t *A = R1, *B = R2;
    for (int v = 0; v < N; v++) {
        uint64_t *r = A + (size_t)v * WCAP;
        memset(r, 0, sizeof(uint64_t) * (size_t)w);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int round = 0; round < DD; round++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = B + (size_t)v * WCAP;
            const uint64_t *src = A + (size_t)v * WCAP;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)w);
            const int *p = adjL + (size_t)v * dd;
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s2 = A + (size_t)p[i] * WCAP;
                for (int k = 0; k < w; k++) dst[k] |= s2[k];
            }
        }
        uint64_t *t = A;
        A = B;
        B = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = A + (size_t)v * WCAP;
        int pc = 0;
        for (int k = 0; k < w; k++) pc += popc64(r[k]);
        bad += N - pc;
    }
    return bad / 2;
}

static void load_graph(int n, int m, const int *u, const int *v) {
    N = n;
    E = 0;
    ns[0] = ns[1] = 0;
    memset(M, 0, (size_t)CAP * CAP);
    for (int i = 0; i < CAP; i++) deg[i] = 0;
    for (int i = 0; i < n; i++) sl[side[i]][ns[side[i]]++] = i;
    for (int e = 0; e < m; e++) {
        int a = u[e], b = v[e];
        if (side[a] == 1) {
            int t = a;
            a = b;
            b = t;
        }
        add_edge(a, b);
    }
}

static void save_best(void) {
    bestN = N;
    bestM = E;
    for (int e = 0; e < E; e++) {
        bu[e] = eu[e];
        bv[e] = ev[e];
    }
}

static void add_pair(void) {
    int a = N, b = N + 1;
    N += 2;
    side[a] = 0;
    side[b] = 1;
    sl[0][ns[0]++] = a;
    sl[1][ns[1]++] = b;
    deg[a] = 0;
    deg[b] = 0;
}

static void shuffle(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static void fill_spare(void) {
    shuffle(sl[0], ns[0]);
    shuffle(sl[1], ns[1]);
    for (int i = 0; i < ns[0]; i++) {
        int a = sl[0][i];
        for (int j = 0; j < ns[1] && deg[a] < dd && E < ECAP; j++) {
            int b = sl[1][j];
            if (deg[b] < dd && !isadj(a, b)) add_edge(a, b);
        }
    }
}

static int try_add(int tries) {
    if (ns[0] == 0 || ns[1] == 0) return 0;
    for (int t = 0; t < tries; t++) {
        int a = sl[0][rndint(ns[0])];
        int b = sl[1][rndint(ns[1])];
        if (deg[a] < dd && deg[b] < dd && !isadj(a, b) && E < ECAP) {
            add_edge(a, b);
            return 1;
        }
    }
    return 0;
}

/* Simulated annealing on the current graph until cost 0, iteration cap, or time cap. */
static long anneal(long iters, double tlimit) {
    long cost = cost_eval();
    if (cost == 0) return 0;
    const double T0 = 2.0, T1 = 0.15;
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 1023) == 0 && elapsed() > tlimit) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int r = rndint(10);
        if (r < 2) {
            if (try_add(16)) cost = cost_eval();
            continue;
        }
        if (r < 6) {
            if (E == 0) continue;
            int e = rndint(E);
            int s = rndint(2);
            int ov = (s == 0) ? eu[e] : ev[e];
            int oth = (s == 0) ? ev[e] : eu[e];
            int nv = sl[s][rndint(ns[s])];
            if (nv == ov || deg[nv] >= dd || isadj(nv, oth)) continue;
            move_end(e, s, nv);
            long c2 = cost_eval();
            long delta = c2 - cost;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
                cost = c2;
            } else {
                move_end(e, s, ov);
            }
        } else {
            if (E < 2) continue;
            int e1 = rndint(E), e2 = rndint(E);
            if (e1 == e2) continue;
            int a = eu[e1], b = ev[e1], c = eu[e2], e = ev[e2];
            if (a == c || b == e || isadj(a, e) || isadj(c, b)) continue;
            do_swap(e1, e2);
            long c2 = cost_eval();
            long delta = c2 - cost;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
                cost = c2;
            } else {
                do_swap(e1, e2);
            }
        }
    }
    return cost;
}

static void echo_graph(int n, int m, const int *u, const int *v) {
    printf("%d %d\n", n, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", u[e], v[e]);
}

int main(int argc, char **argv) {
    T_START = clock();
    if (argc < 5) die("usage: prog d D seed time_limit");
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) die("out of memory");
    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &iu[e], &iv[e]) != 2) die("bad edge line");
        if (iu[e] < 0 || iu[e] >= n0 || iv[e] < 0 || iv[e] >= n0) die("vertex out of range");
    }

    /* Degree check and bipartition by BFS. */
    int *cdeg = calloc((size_t)n0, sizeof(int));
    for (int e = 0; e < m0; e++) {
        cdeg[iu[e]]++;
        cdeg[iv[e]]++;
    }
    int degok = 1;
    for (int v = 0; v < n0; v++)
        if (cdeg[v] > dd) degok = 0;
    if (!degok) {
        echo_graph(n0, m0, iu, iv);
        return 0;
    }
    int *off = malloc(sizeof(int) * (size_t)(n0 + 1));
    int *pos = malloc(sizeof(int) * (size_t)n0);
    int *nb = malloc(sizeof(int) * (size_t)(2 * m0 + 1));
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *q = malloc(sizeof(int) * (size_t)n0);
    off[0] = 0;
    for (int v = 0; v < n0; v++) off[v + 1] = off[v] + cdeg[v];
    for (int v = 0; v < n0; v++) pos[v] = off[v];
    for (int e = 0; e < m0; e++) {
        nb[pos[iu[e]]++] = iv[e];
        nb[pos[iv[e]]++] = iu[e];
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    int ok = 1;
    for (int s = 0; s < n0 && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail && ok) {
            int u = q[head++];
            for (int k = off[u]; k < off[u + 1]; k++) {
                int w = nb[k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[tail++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        echo_graph(n0, m0, iu, iv);
        return 0;
    }

    CAP = n0 + 2 * MAXADD;
    WCAP = (CAP + 63) >> 6;
    ECAP = CAP * dd + 8;
    deg = calloc((size_t)CAP, sizeof(int));
    adjL = calloc((size_t)CAP * (size_t)dd + 1, sizeof(int));
    side = calloc((size_t)CAP, sizeof(int));
    sl[0] = malloc(sizeof(int) * (size_t)CAP);
    sl[1] = malloc(sizeof(int) * (size_t)CAP);
    eu = malloc(sizeof(int) * (size_t)ECAP);
    ev = malloc(sizeof(int) * (size_t)ECAP);
    bu = malloc(sizeof(int) * (size_t)ECAP);
    bv = malloc(sizeof(int) * (size_t)ECAP);
    M = calloc((size_t)CAP * (size_t)CAP, 1);
    R1 = malloc(sizeof(uint64_t) * (size_t)CAP * (size_t)WCAP);
    R2 = malloc(sizeof(uint64_t) * (size_t)CAP * (size_t)WCAP);
    if (!deg || !adjL || !side || !sl[0] || !sl[1] || !eu || !ev || !bu || !bv || !M || !R1 || !R2)
        die("out of memory");

    for (int v = 0; v < n0; v++) side[v] = (col[v] < 0) ? 0 : col[v];
    load_graph(n0, m0, iu, iv);
    if (cost_eval() != 0) {
        echo_graph(n0, m0, iu, iv);
        return 0;
    }
    save_best();

    long iters = 60000;
    int fails = 0;
    while (elapsed() < budget && N + 2 <= CAP) {
        add_pair();
        fill_spare();
        long c = anneal(iters, budget);
        if (c == 0) {
            save_best();
            fails = 0;
        } else {
            fails++;
            load_graph(bestN, bestM, bu, bv);
            if (fails % 4 == 0 && iters < 2000000) iters *= 2;
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bu[e], bv[e]);
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
# the q+1 lines through P; for each j in S add a new B-vertex joined to the q+1
# points on line j.
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


_LP = None  # line_points for the current q, set in _arc_extensions


def _arc_graph(m, edges, point_lines, S):
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
        for Q in _LP[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    global _LP
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        _LP = line_points
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S)
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
# C repair / growth stage.
# ----------------------------------------------------------------------------

def _c_repair(d, D, seed, n, edges, budget):
    """Run the C growth+annealing engine from (n, edges) for about `budget` CPU seconds."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=budget + 3.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end_target = start + 0.9 * time_limit
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

    # Arc-extended projective plane graphs: diameter 3, valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, end_target, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < end_target:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to search for.
    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Voltage annealing for D >= 4 (Python, small budget).
    if D >= 4:
        volt_deadline = start + 0.35 * time_limit
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < volt_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, volt_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Main search: C growth and repair starting from the best valid graph.
    if D >= 3 and best_n < moore:
        cbudget = end_target - time.monotonic() - 2.5
        if cbudget >= 2.0:
            try:
                n_c, e_c = _c_repair(d, D, seed, best_n, best[1], cbudget)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
