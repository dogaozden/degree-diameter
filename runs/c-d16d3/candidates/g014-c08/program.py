"""Arc-extended projective plane graphs plus a C growth engine.

Construction (unchanged in spirit from the parent): start from the incidence graph of PG(2, q).
Each point gets a twin-like A-vertex and each line a B-vertex, subject to spare-degree arc
conditions (conic / greedy). This gives 2(q^2+q+1) + |SA| + |SB| vertices.

New in this version: a C growth engine (`C_SOURCE`). It takes any valid bipartite graph with
max degree d and diameter D, keeps degree <= d as a hard constraint, and anneals on the number
of vertex pairs at distance > D. Every time the graph becomes valid it is recorded and one
isolated vertex is added on the side with more spare capacity, so the order keeps growing
while the search runs. Moves are: switch (degree-preserving double edge swap), endpoint rewire
(moves spare capacity), add edge, remove edge. Distances are computed with bit-parallel
reachability sets (D rounds of OR over neighbours).

Analysis note: for d = 16 and q = 13, any "twin" extension of PG(2,13) (a new vertex with the
neighbourhood of a point or line, or any cover of all points by lines) is capped at 394 vertices,
because the centres of the new vertices must form an arc. So gains must come from the C search
or from a structurally different base. Validity is always checked in Python, with fallbacks.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bipartite diameter-D growth engine: simulated annealing on the number of
   vertex pairs at distance > D, with max degree DEG kept as a hard constraint.
   When the graph is valid it is recorded and one isolated vertex is added on
   the side with more spare capacity. Output: best valid graph found. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXDEG 64

static int N, DEG, DIST, W;
static int side[MAXN], deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char adj[MAXN][MAXN];
static uint64_t RS[2][MAXN][MAXW];
static uint64_t rs = 1;
static int bestN = 0, bestM = 0;
static int bu[MAXN * MAXDEG], bv[MAXN * MAXDEG];
static int qbuf[MAXN];

typedef struct { int add, u, v; } Op;
static Op ops[8];
static int nops = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adj[u][v] = 1;
    adj[v][u] = 1;
}

static void del_nb(int u, int v) {
    int k;
    for (k = 0; k < deg[u]; k++) {
        if (nb[u][k] == v) {
            nb[u][k] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    del_nb(u, v);
    del_nb(v, u);
    adj[u][v] = 0;
    adj[v][u] = 0;
}

static void push(int add, int u, int v) {
    ops[nops].add = add;
    ops[nops].u = u;
    ops[nops].v = v;
    nops++;
}

static void apply_ops(void) {
    int i;
    for (i = 0; i < nops; i++) {
        if (ops[i].add) add_edge(ops[i].u, ops[i].v);
        else remove_edge(ops[i].u, ops[i].v);
    }
}

static void undo_ops(void) {
    int i;
    for (i = nops - 1; i >= 0; i--) {
        if (ops[i].add) remove_edge(ops[i].u, ops[i].v);
        else add_edge(ops[i].u, ops[i].v);
    }
}

/* Number of unordered pairs at distance > DIST (unreached pairs included). */
static long long cost_eval(void) {
    int cur = 0, v, t, k, w;
    long long miss = 0;
    for (v = 0; v < N; v++) {
        memset(RS[0][v], 0, sizeof(uint64_t) * W);
        RS[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (t = 0; t < DIST; t++) {
        int nxt = 1 - cur;
        for (v = 0; v < N; v++) {
            uint64_t *o = RS[nxt][v];
            memcpy(o, RS[cur][v], sizeof(uint64_t) * W);
            for (k = 0; k < deg[v]; k++) {
                const uint64_t *r = RS[cur][nb[v][k]];
                for (w = 0; w < W; w++) o[w] |= r[w];
            }
        }
        cur = nxt;
    }
    for (v = 0; v < N; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc64(RS[cur][v][w]);
        miss += N - c;
    }
    return miss / 2;
}

/* Random vertex on side s; need_spare: deg < DEG, else deg > 0. */
static int pick_v(int s, int need_spare) {
    int t;
    for (t = 0; t < 64; t++) {
        int v = rnd(N);
        if (side[v] != s) continue;
        if (need_spare) {
            if (deg[v] < DEG) return v;
        } else {
            if (deg[v] > 0) return v;
        }
    }
    return -1;
}

/* Degree-preserving switch: (a,b),(c,e) -> (a,e),(c,b), with a,c on the same side. */
static int move_switch(void) {
    int s = rnd(2);
    int a = pick_v(s, 0), c, b, e;
    if (a < 0) return 0;
    c = pick_v(s, 0);
    if (c < 0 || c == a) return 0;
    b = nb[a][rnd(deg[a])];
    e = nb[c][rnd(deg[c])];
    if (b == e || adj[a][e] || adj[c][b]) return 0;
    nops = 0;
    push(0, a, b);
    push(0, c, e);
    push(1, a, e);
    push(1, c, b);
    return 1;
}

/* Move one endpoint of an edge: (a,b) -> (a,e), giving spare capacity a new place. */
static int move_rewire(void) {
    int a = pick_v(rnd(2), 0), b, e;
    if (a < 0) return 0;
    b = nb[a][rnd(deg[a])];
    e = pick_v(side[b], 1);
    if (e < 0 || e == b || adj[a][e]) return 0;
    nops = 0;
    push(0, a, b);
    push(1, a, e);
    return 1;
}

static int move_add(void) {
    int u, v, s = rnd(2);
    if (rndu() < 0.3 && deg[N - 1] < DEG) u = N - 1;
    else u = pick_v(s, 1);
    if (u < 0) return 0;
    v = pick_v(1 - side[u], 1);
    if (v < 0 || adj[u][v]) return 0;
    nops = 0;
    push(1, u, v);
    return 1;
}

static int move_remove(void) {
    int a = pick_v(rnd(2), 0), b;
    if (a < 0) return 0;
    b = nb[a][rnd(deg[a])];
    nops = 0;
    push(0, a, b);
    return 1;
}

static int bestRecorded(void) { return bestN; }

static void snapshot(void) {
    int v, k, m = 0;
    if (N <= bestN) return;
    for (v = 0; v < N; v++) {
        for (k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (u > v) {
                bu[m] = v;
                bv[m] = u;
                m++;
            }
        }
    }
    bestN = N;
    bestM = m;
}

/* Add one isolated vertex on the side whose opposite side has more spare capacity. */
static void grow(void) {
    int spare[2] = {0, 0}, v, s;
    for (v = 0; v < N; v++) spare[side[v]] += DEG - deg[v];
    s = (spare[1] >= spare[0]) ? 0 : 1;
    side[N] = s;
    deg[N] = 0;
    N++;
    W = (N + 63) / 64;
}

int main(int argc, char **argv) {
    int n, m, i, bad = 0;
    double budget;
    unsigned long long seed;
    clock_t c0 = clock();
    long long cur, it = 0;
    double T, frac;
    const long long STAGE = 30000;

    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIST = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    if (DEG < 1 || DEG >= MAXDEG || DIST < 1) {
        printf("0 0\n");
        return 0;
    }
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 8) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (adj[u][v] || deg[u] >= DEG || deg[v] >= DEG) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS 2-colouring; reject non-bipartite input. */
    for (i = 0; i < N; i++) side[i] = -1;
    for (i = 0; i < N; i++) {
        int h = 0, t = 0;
        if (side[i] >= 0) continue;
        side[i] = 0;
        qbuf[t++] = i;
        while (h < t) {
            int x = qbuf[h++], k;
            for (k = 0; k < deg[x]; k++) {
                int y = nb[x][k];
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    qbuf[t++] = y;
                } else if (side[y] == side[x]) {
                    bad = 1;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    W = (N + 63) / 64;
    cur = cost_eval();
    if (cur == 0) {
        snapshot();
        if (N < MAXN - 2) {
            grow();
            cur = cost_eval();
        }
    }

    for (;;) {
        double r;
        int ok;
        if ((it & 127) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
        }
        it++;
        frac = (double)(it % STAGE) / (double)STAGE;
        T = 2.0 * pow(0.05, frac);

        r = rndu();
        if (r < 0.40) ok = move_switch();
        else if (r < 0.75) ok = move_rewire();
        else if (r < 0.95) ok = move_add();
        else ok = move_remove();
        if (!ok) continue;

        apply_ops();
        {
            long long nc = cost_eval();
            long long dl = nc - cur;
            if (dl <= 0 || rndu() < exp(-(double)dl / T)) {
                cur = nc;
                if (cur == 0) {
                    snapshot();
                    if (N >= MAXN - 2) break;
                    grow();
                    cur = cost_eval();
                }
            } else {
                undo_ops();
            }
        }
    }

    (void)bestRecorded;
    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
'''


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
# Simulated annealing over bi-Cayley voltage lifts (Python fallback search).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.92 * time_limit - 1.0   # hard end of all Python-side work
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
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New: C growth engine started from the best valid graph found so far.
    # It anneals on distance violations and adds vertices whenever it reaches validity.
    c_end = t0 + 0.75 * time_limit
    if 1 <= best_n <= 1900:
        remaining = c_end - time.monotonic()
        if remaining > 4.0:
            budget = remaining - 2.0
            timeout = max(2.0, min(budget + 10.0, deadline - time.monotonic()))
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                 stdin_graph=best, timeout=timeout)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    # Python voltage-lift annealing for the remaining time (mainly useful for D >= 5).
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
