import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: starting from a valid-or-near-valid bipartite graph, it runs
# simulated annealing over degree-preserving edge swaps, edge additions and edge
# removals, minimising the number of vertex pairs at distance > D. It stops as
# soon as the cost is zero and prints that graph. Otherwise it prints "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static int N, DMAX, DIAM, W, M, CAP;
static int *EU, *EV, *DEG, *COL;
static unsigned char *ADJ;
static uint64_t *RA, *RB;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,w), v != w, with dist(v,w) > DIAM. */
static long long cost_fn(void) {
    uint64_t *R = RA, *S = RB;
    size_t words = (size_t)N * (size_t)W;
    memset(R, 0, words * sizeof(uint64_t));
    for (int v = 0; v < N; v++) R[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        memcpy(S, R, words * sizeof(uint64_t));
        for (int e = 0; e < M; e++) {
            size_t u = (size_t)EU[e] * W, v = (size_t)EV[e] * W;
            for (int w = 0; w < W; w++) {
                S[u + w] |= R[v + w];
                S[v + w] |= R[u + w];
            }
        }
        uint64_t *t = R; R = S; S = t;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(R[(size_t)v * W + w]);
        total += N - c;
    }
    return total;
}

static void setadj(int a, int b, int v) {
    ADJ[(size_t)a * N + b] = (unsigned char)v;
    ADJ[(size_t)b * N + a] = (unsigned char)v;
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    clock_t c0 = clock();
    if (argc < 5) return 1;
    DMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double tl = atof(argv[4]);
    double limit = tl * 0.9;

    if (scanf("%d %d", &N, &M) != 2 || N <= 0 || M < 0) { printf("0 0\n"); return 0; }
    int *tu = malloc(sizeof(int) * (size_t)(M + 1));
    int *tv = malloc(sizeof(int) * (size_t)(M + 1));
    ADJ = calloc((size_t)N * (size_t)N, 1);
    DEG = calloc((size_t)N, sizeof(int));
    for (int i = 0; i < M; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || ADJ[(size_t)u * N + v]) {
            printf("0 0\n"); return 0;
        }
        setadj(u, v, 1);
        DEG[u]++; DEG[v]++;
        tu[i] = u; tv[i] = v;
    }
    for (int v = 0; v < N; v++) if (DEG[v] > DMAX) { printf("0 0\n"); return 0; }

    /* Bipartition by propagation. */
    COL = malloc(sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) COL[v] = -1;
    for (int s = 0; s < N; s++) {
        if (COL[s] != -1) continue;
        COL[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int e = 0; e < M; e++) {
                int u = tu[e], v = tv[e];
                if (COL[u] >= 0 && COL[v] < 0) { COL[v] = 1 - COL[u]; changed = 1; }
                else if (COL[v] >= 0 && COL[u] < 0) { COL[u] = 1 - COL[v]; changed = 1; }
            }
        }
    }
    for (int e = 0; e < M; e++) if (COL[tu[e]] == COL[tv[e]]) { printf("0 0\n"); return 0; }

    CAP = (M > N * DMAX / 2 ? M : N * DMAX / 2) + 16;
    EU = malloc(sizeof(int) * (size_t)CAP);
    EV = malloc(sizeof(int) * (size_t)CAP);
    for (int e = 0; e < M; e++) {
        if (COL[tu[e]] == 0) { EU[e] = tu[e]; EV[e] = tv[e]; }
        else { EU[e] = tv[e]; EV[e] = tu[e]; }
    }

    W = (N + 63) / 64;
    RA = malloc(sizeof(uint64_t) * (size_t)N * (size_t)W);
    RB = malloc(sizeof(uint64_t) * (size_t)N * (size_t)W);
    int *spA = malloc(sizeof(int) * (size_t)N);
    int *spB = malloc(sizeof(int) * (size_t)N);

    long long cur = cost_fn();
    double T0 = 3.0, T1 = 0.3, T = T0;
    unsigned long long it = 0;

    while (cur > 0) {
        if ((it & 127ULL) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el > limit) break;
            double f = el / limit;
            T = T0 * pow(T1 / T0, f);
        }
        it++;
        double r = rnd01();
        if (r < 0.75) {
            /* Degree-preserving swap of two edges. */
            if (M >= 2) {
                int i = rndint(M), j = rndint(M);
                if (i != j) {
                    int a1 = EU[i], b1 = EV[i], a2 = EU[j], b2 = EV[j];
                    if (!ADJ[(size_t)a1 * N + b2] && !ADJ[(size_t)a2 * N + b1]) {
                        setadj(a1, b1, 0); setadj(a2, b2, 0);
                        setadj(a1, b2, 1); setadj(a2, b1, 1);
                        EV[i] = b2; EV[j] = b1;
                        long long nc = cost_fn();
                        if (accept(nc - cur, T)) cur = nc;
                        else {
                            setadj(a1, b2, 0); setadj(a2, b1, 0);
                            setadj(a1, b1, 1); setadj(a2, b2, 1);
                            EV[i] = b1; EV[j] = b2;
                        }
                    }
                }
            }
        } else if (r < 0.97) {
            /* Add an edge between two vertices with spare degree. */
            int na = 0, nb = 0;
            for (int v = 0; v < N; v++) {
                if (DEG[v] < DMAX) {
                    if (COL[v] == 0) spA[na++] = v;
                    else spB[nb++] = v;
                }
            }
            if (na > 0 && nb > 0 && M < CAP) {
                int a = spA[rndint(na)], b = spB[rndint(nb)];
                if (!ADJ[(size_t)a * N + b]) {
                    EU[M] = a; EV[M] = b; M++;
                    setadj(a, b, 1); DEG[a]++; DEG[b]++;
                    long long nc = cost_fn();
                    if (accept(nc - cur, T)) cur = nc;
                    else {
                        M--;
                        setadj(a, b, 0); DEG[a]--; DEG[b]--;
                    }
                }
            }
        } else {
            /* Remove a random edge. */
            if (M > 0) {
                int i = rndint(M);
                int a = EU[i], b = EV[i];
                EU[i] = EU[M - 1]; EV[i] = EV[M - 1];
                M--;
                setadj(a, b, 0); DEG[a]--; DEG[b]--;
                long long nc = cost_fn();
                if (accept(nc - cur, T)) cur = nc;
                else {
                    EU[M] = EU[i]; EV[M] = EV[i];
                    EU[i] = a; EV[i] = b; M++;
                    setadj(a, b, 1); DEG[a]++; DEG[b]++;
                }
            }
        }
    }

    if (cur == 0) {
        printf("%d %d\n", N, M);
        for (int e = 0; e < M; e++) printf("%d %d\n", EU[e], EV[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. Each old vertex has degree q+1, so spare
# s = d - q - 1. A set SA of points gets a new A-vertex joined to its q+1 lines
# (each line hit by <= s of SA). A set SB of lines gets a new B-vertex joined
# to its q+1 points (each point hit by <= s of SB).
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy load-constrained selection."""
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
    """Plateau/improvement local search for the load-constrained set problem."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
    """W(q) for the largest prime power q with q + 1 <= d (small q only, for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Growth by the C engine: add one A-vertex and one B-vertex (plus an edge
# between them), then ask C to repair the graph to diameter D.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of the graph, or None if it has an odd cycle."""
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
                elif col[v] == col[u]:
                    return None
    return col


def _add_pair(cur, d, rng):
    """Return a graph with two new vertices (opposite sides) attached to vertices with spare degree."""
    n, edges = cur
    adj = lib.adjacency(n, edges)
    deg = [len(a) for a in adj]
    col = _bipartition(n, adj)
    if col is None:
        return None
    spare0 = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    spare1 = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    if not spare0 or not spare1:
        return None
    x, z = n, n + 1          # x is on side 0, z on side 1
    y = rng.choice(spare1)   # x -> y (side 1)
    w = rng.choice(spare0)   # z -> w (side 0)
    new_edges = list(edges) + [(x, y), (z, w), (x, z)]
    return n + 2, new_edges


def _grow(d, D, base, seed, deadline):
    """Repeatedly add a vertex pair and let the C engine repair the graph. Returns the best valid graph."""
    cur = base
    rng = random.Random(seed + 101)
    k = 0
    while True:
        ok = False
        for attempt in range(3):
            remaining = deadline - time.monotonic()
            if remaining < 3.0:
                break
            budget = remaining * 0.6 if attempt < 2 else remaining - 1.0
            nxt = _add_pair(cur, d, rng)
            if nxt is None:
                break
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed * 31 + k * 7 + attempt, round(budget, 2)],
                                 stdin_graph=nxt, timeout=budget + 5.0)
                n2, e2 = lib.parse_graph_text(text)
            except (RuntimeError, ValueError):
                continue
            if n2 > cur[0] and lib.is_valid(n2, e2, d, D):
                cur = (n2, e2)
                ok = True
                break
        if not ok:
            break
        k += 1
    return cur


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

_BIG_DEADLINE_FRAC = 0.85


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + _BIG_DEADLINE_FRAC * time_limit - 1.0

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
        cands = _arc_extensions(d, start + 0.3 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    # Generalized quadrangle baseline (diameter 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C engine grows the best graph by vertex pairs, repairing diameter by annealing.
    if D >= 3 and time.monotonic() < end - 3.0:
        grown = _grow(d, D, best, seed, end)
        consider(grown[0], grown[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
