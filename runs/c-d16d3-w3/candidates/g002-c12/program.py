import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points, each giving a new vertex joined to its q+1 lines.
#         Every line may hold <= s points of SA.
# B-side: a set SB of lines, each giving a new vertex joined to its q+1 points.
#         Every point may lie on <= s lines of SB.
#
# Order is 2(q^2+q+1) + |SA| + |SB|. Diameter stays 3 for any SA, SB.
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


def _local_side(m, s, nbr, S0, rng, deadline, iters=6000):
    """Plateau local search on a feasible set S0 (insert, or swap out one blocker)."""
    if s < 1:
        return list(S0)
    inS = [False] * m
    load = [0] * m
    S = list(S0)
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            load[t] += 1
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        over = {t for t in nbr[x] if load[t] >= s}
        if not over:
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
            if len(S) > len(best):
                best = list(S)
            continue
        cand = [y for y in S if any(t in over for t in nbr[y])]
        if not cand:
            continue
        y = rng.choice(cand)
        for t in nbr[y]:
            load[t] -= 1
        if all(load[t] < s for t in nbr[x]):
            S.remove(y)
            inS[y] = False
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
        else:
            for t in nbr[y]:
                load[t] += 1
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

        SA = _local_side(m, s, point_lines, SA, rng, deadline)
        SB = _local_side(m, s, line_points, SB, rng, deadline)

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
# Annealed group voltage lifts (used for D >= 4 only).
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
# NEW: generic bipartite augmentation annealer in C.
#
# Idea: the arc construction only lets new vertices attach to OLD lines/points
# with full pencils, which forces the side sets to be arcs. Here the whole
# bipartite graph is open to local edits: new vertices may also join each other
# (A-B edges between new vertices), and old edges can be rewired. The C engine
# grows the graph one vertex at a time. Moves are add-edge, delete-edge,
# endpoint-move and 2-switch; each keeps bipartiteness and the degree bound.
# The cost is the number of vertex pairs at distance > D (unreachable counts).
# Whenever the cost reaches 0, the graph is saved and a new isolated vertex is
# added on a random side.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2048
#define WMAX 32
#define DMAXL 18
#define EMAX 20000

static int dd, DD;
static int N, NCAP;
static int side[NMAX];
static int deg[NMAX];
static int nb[NMAX][DMAXL + 2];
static unsigned char adj[NMAX][NMAX];
static uint64_t BA[NMAX][WMAX], BB[NMAX][WMAX];
static uint64_t (*R)[WMAX];
static uint64_t (*T)[WMAX];
static uint64_t rs;
static int bestu[EMAX], bestv[EMAX];
static int bestM, bestN;

typedef struct { int t, u, v; } Op;
static Op logv[16];
static int nlog;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void remove_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adj[u][v] = 1;
    adj[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    adj[u][v] = 0;
    adj[v][u] = 0;
    remove_from(u, v);
    remove_from(v, u);
}

static void do_add(int u, int v) {
    add_edge(u, v);
    logv[nlog].t = 1; logv[nlog].u = u; logv[nlog].v = v; nlog++;
}

static void do_del(int u, int v) {
    del_edge(u, v);
    logv[nlog].t = 0; logv[nlog].u = u; logv[nlog].v = v; nlog++;
}

static void undo_all(void) {
    while (nlog > 0) {
        Op o = logv[--nlog];
        if (o.t) del_edge(o.u, o.v);
        else add_edge(o.u, o.v);
    }
}

/* Bad pairs: unordered pairs at distance > DD (unreachable counts as bad). */
static long cost_eval(void) {
    int W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) R[v][w] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DD; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *t = T[v];
            const uint64_t *s = R[v];
            for (int w = 0; w < W; w++) t[w] = s[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *r = R[nb[v][k]];
                for (int w = 0; w < W; w++) t[w] |= r[w];
            }
        }
        uint64_t (*tmp)[WMAX] = R;
        R = T;
        T = tmp;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(R[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int rand_edge(int *a, int *b) {
    for (int t = 0; t < 400; t++) {
        int u = rndint(N);
        if (deg[u] == 0) continue;
        *a = u;
        *b = nb[u][rndint(deg[u])];
        return 1;
    }
    return 0;
}

static int move_add(void) {
    for (int t = 0; t < 300; t++) {
        int u, v;
        if (rnd01() < 0.3) u = N - 1 - rndint(N < 4 ? N : 4);
        else u = rndint(N);
        v = rndint(N);
        if (u == v || side[u] == side[v]) continue;
        if (deg[u] >= dd || deg[v] >= dd || adj[u][v]) continue;
        do_add(u, v);
        return 1;
    }
    return 0;
}

static int move_del(void) {
    int a, b;
    if (!rand_edge(&a, &b)) return 0;
    do_del(a, b);
    return 1;
}

/* Keep edge (a,b), move its b-end to another vertex c on b's side. */
static int move_end(void) {
    int a, b;
    if (!rand_edge(&a, &b)) return 0;
    if (rnd64() & 1) { int t = a; a = b; b = t; }
    for (int t = 0; t < 300; t++) {
        int c = rndint(N);
        if (c == b || c == a || side[c] != side[b]) continue;
        if (deg[c] >= dd || adj[a][c]) continue;
        do_del(a, b);
        do_add(a, c);
        return 1;
    }
    return 0;
}

/* 2-switch: (a,b),(c,e) with a,c on side 0 becomes (a,e),(c,b). Degrees kept. */
static int move_switch(void) {
    int a, b, c, e;
    if (!rand_edge(&a, &b)) return 0;
    if (!rand_edge(&c, &e)) return 0;
    if (side[a] == 1) { int t = a; a = b; b = t; }
    if (side[c] == 1) { int t = c; c = e; e = t; }
    if (side[a] != 0 || side[c] != 0) return 0;
    if (a == c || b == e) return 0;
    if (adj[a][e] || adj[c][b]) return 0;
    do_del(a, b);
    do_del(c, e);
    do_add(a, e);
    do_add(c, b);
    return 1;
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++)
            if (adj[u][v] && bestM < EMAX) {
                bestu[bestM] = u;
                bestv[bestM] = v;
                bestM++;
            }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 88172645463325252ULL;
    R = BA;
    T = BB;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > NMAX / 2 ||
        dd < 1 || dd > DMAXL || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (adj[u][v] || deg[u] >= dd || deg[v] >= dd) continue;
        add_edge(u, v);
    }

    /* Bipartition: BFS colouring; isolated vertices get a random side. */
    static int col[NMAX];
    static int qu[NMAX];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0 || deg[s] == 0) continue;
        int h = 0, t = 0;
        col[s] = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qu[t++] = v;
                }
            }
        }
    }
    for (int v = 0; v < N; v++) if (col[v] < 0) col[v] = rndint(2);
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (col[nb[u][k]] == col[u]) {
                printf("0 0\n");
                return 0;
            }
    for (int v = 0; v < N; v++) side[v] = col[v];

    NCAP = N + 120;
    if (NCAP > NMAX - 1) NCAP = NMAX - 1;

    save_best();
    long cur = cost_eval();

    double budget = tl;
    double roundLen = budget / 6.0;
    if (roundLen < 1.0) roundLen = 1.0;
    double roundStart = elapsed();
    const double T0 = 2.0, Tend = 0.05;

    while (1) {
        double now = elapsed();
        if (now >= budget) break;
        if (now - roundStart >= roundLen) roundStart = now;
        double phase = (now - roundStart) / roundLen;
        double Tc = T0 * pow(Tend / T0, phase);

        nlog = 0;
        double r = rnd01();
        int ok;
        if (r < 0.30) ok = move_add();
        else if (r < 0.40) ok = move_del();
        else if (r < 0.70) ok = move_end();
        else ok = move_switch();
        if (!ok) continue;

        long c2 = cost_eval();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / Tc)) cur = c2;
        else undo_all();

        if (cur == 0) {
            if (N > bestN) save_best();
            if (N >= NCAP) break;
            side[N] = rndint(2);
            deg[N] = 0;
            N++;
            cur = cost_eval();
            roundStart = elapsed();
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestu[i], bestv[i]);
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    tl = float(time_limit)

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
        cands = _arc_extensions(d, t0 + 0.2 * tl, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t0 + 0.2 * tl:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for D >= 4 (short phase).
    if D >= 4:
        rng = random.Random(seed)
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        lift_deadline = t0 + 0.25 * tl
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # NEW: bipartite augmentation annealing in C, starting from the best graph.
    if D >= 3 and d <= 18 and best_n < lib.moore_bound(d, D):
        remaining = tl - (time.monotonic() - t0)
        cbudget = remaining * 0.75 - 3.0
        if cbudget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{cbudget:.2f}"],
                                stdin_graph=best, timeout=remaining * 0.85)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
