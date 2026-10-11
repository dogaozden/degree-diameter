"""Arc-extended projective-plane graphs (D = 3) improved by a C repair search.

New in this version: a C annealer that never touches the parent's voltage code. It starts from the
best valid graph, appends one vertex at a time with random capacity-respecting edges, and anneals
degree-preserving swaps and additions to remove all pairs at distance > D (bad pairs). Moves are
focused on a sampled bad pair (x, y): for opposite sides it swaps edges so that x-y becomes an
edge, and for the same side it creates a common neighbour. Bipartiteness is kept by side labels.
Degrees are kept by 2-swaps, and undo is a short operation log, so each step costs one bitset ball
computation.

Python builds the arc-extended PG(2,q) graphs and the GQ baseline, then hands the best one to C.
Voltage annealing (parent) continues for the remaining time.
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

#define EXTRA 300
#define FIX_ITERS 100000
#define ATTEMPT_ITERS 12000

static int dmax, Dist;
static int N, CAP, WMAX, Wc;
static int *adj, *deg, *side;
static int *base_adj, *base_deg;
static uint64_t *bufs[3];
static int curb;
static int nops;
typedef struct { int t, u, v; } Op;
static Op oplog[8];
static uint64_t rng_s;
static double deadline;
static long long cur_cost;
static int *best_e;
static int best_m, best_n;

static uint64_t rnd64(void) {
    rng_s ^= rng_s >> 12;
    rng_s ^= rng_s << 25;
    rng_s ^= rng_s >> 27;
    return rng_s * 2685821657736338717ULL;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    const int *a = adj + (size_t)u * dmax;
    for (int i = 0; i < deg[u]; i++) if (a[i] == v) return 1;
    return 0;
}
static void raw_add(int u, int v) {
    adj[u * dmax + deg[u]++] = v;
    adj[v * dmax + deg[v]++] = u;
}
static void raw_del_arc(int u, int v) {
    int *a = adj + (size_t)u * dmax;
    for (int i = 0; i < deg[u]; i++) {
        if (a[i] == v) { a[i] = a[--deg[u]]; return; }
    }
}
static void raw_del(int u, int v) { raw_del_arc(u, v); raw_del_arc(v, u); }

static void op_add(int u, int v) {
    raw_add(u, v);
    oplog[nops].t = 0; oplog[nops].u = u; oplog[nops].v = v; nops++;
}
static void op_del(int u, int v) {
    raw_del(u, v);
    oplog[nops].t = 1; oplog[nops].u = u; oplog[nops].v = v; nops++;
}
static void undo(void) {
    while (nops > 0) {
        Op o = oplog[--nops];
        if (o.t == 0) raw_del(o.u, o.v);
        else raw_add(o.u, o.v);
    }
}

static int bit(const uint64_t *R, int x, int y) {
    return (int)((R[(size_t)x * Wc + (y >> 6)] >> (y & 63)) & 1ULL);
}

/* Ball of radius Dist for every vertex, written into a buffer different from curb.
   Returns the index of that buffer. Sets Wc from N. */
static int ball(void) {
    Wc = (N + 63) >> 6;
    int ix = (curb + 1) % 3, iy = (curb + 2) % 3;
    uint64_t *cur = bufs[ix];
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * Wc);
    for (int v = 0; v < N; v++) cur[(size_t)v * Wc + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < Dist; it++) {
        uint64_t *nx = bufs[iy];
        cur = bufs[ix];
        for (int v = 0; v < N; v++) {
            uint64_t *o = nx + (size_t)v * Wc;
            memcpy(o, cur + (size_t)v * Wc, sizeof(uint64_t) * Wc);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s = cur + (size_t)adj[v * dmax + k] * Wc;
                for (int w = 0; w < Wc; w++) o[w] |= s[w];
            }
        }
        int t = ix; ix = iy; iy = t;
    }
    return ix;
}

static long long count_bad(const uint64_t *R) {
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = R + (size_t)v * Wc;
        int c = 0;
        for (int w = 0; w < Wc; w++) c += popc(r[w]);
        bad += N - c;
    }
    return bad / 2;
}

static int pick_nb(int v) { return adj[v * dmax + rndint(deg[v])]; }

/* Focused move on a sampled bad pair (x, y) of the accepted state. */
static int propose_focus(void) {
    const uint64_t *R = bufs[curb];
    int x = -1, y = -1;
    for (int tr = 0; tr < 6 && y < 0; tr++) {
        int cx = rndint(N);
        if (deg[cx] == 0) continue;
        int off = rndint(N);
        for (int k = 0; k < N; k++) {
            int v = off + k;
            if (v >= N) v -= N;
            if (v != cx && !bit(R, cx, v)) { x = cx; y = v; break; }
        }
    }
    if (y < 0) return 0;
    if (deg[x] == 0 || deg[y] == 0) return 0;
    if (side[x] != side[y]) {
        int b = pick_nb(x), c = pick_nb(y);
        if (has_edge(c, b)) return 0;
        op_del(x, b); op_del(c, y); op_add(x, y); op_add(c, b);
        return 1;
    } else {
        int b = pick_nb(x);
        if (deg[b] < 2) return 0;
        int z = pick_nb(b);
        if (z == x || z == y) return 0;
        int c = pick_nb(y);
        if (c == b || has_edge(y, b) || has_edge(z, c)) return 0;
        op_del(z, b); op_del(y, c); op_add(y, b); op_add(z, c);
        return 1;
    }
}

/* Degree-preserving random 2-swap between two vertices on the same side. */
static int propose_swap(void) {
    int s = rndint(2);
    int a = -1, c = -1;
    for (int t = 0; t < 40 && a < 0; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] > 0) a = v;
    }
    for (int t = 0; t < 40 && c < 0; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] > 0 && v != a) c = v;
    }
    if (a < 0 || c < 0) return 0;
    int b = pick_nb(a), e = pick_nb(c);
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    op_del(a, b); op_del(c, e); op_add(a, e); op_add(c, b);
    return 1;
}

/* Add a random edge between vertices with spare capacity (never increases bad pairs). */
static int propose_add(void) {
    for (int t = 0; t < 30; t++) {
        int a = rndint(N), b = rndint(N);
        if (side[a] == side[b] || deg[a] >= dmax || deg[b] >= dmax || has_edge(a, b)) continue;
        op_add(a, b);
        return 1;
    }
    return 0;
}

static int propose(void) {
    nops = 0;
    double r = rnd01();
    if (r < 0.08) return propose_add();
    if (r < 0.25) return propose_swap();
    return propose_focus();
}

static long long anneal(int iters, double T0) {
    long long cost = cur_cost;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && cpu_now() > deadline) break;
        double T = T0 * (1.0 - (double)it / iters) + 0.05;
        if (!propose()) continue;
        int ix = ball();
        long long c2 = count_bad(bufs[ix]);
        long long dl = c2 - cost;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cost = c2;
            curb = ix;
        } else {
            undo();
        }
    }
    cur_cost = cost;
    return cost;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v * dmax + k];
            if (u > v) {
                best_e[2 * m] = v;
                best_e[2 * m + 1] = u;
                m++;
            }
        }
    }
    best_m = m;
    best_n = N;
}

static void echo_input(int n0, int m0, const int *eu, const int *ev) {
    printf("%d %d\n", n0, m0);
    for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 2;
    }
    dmax = atoi(argv[1]);
    Dist = atoi(argv[2]);
    double tl = atof(argv[4]);
    rng_s = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rng_s == 0) rng_s = 1;
    deadline = cpu_now() + tl - 0.5;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m0 = i; break; }
    }

    CAP = n0 + EXTRA;
    WMAX = (CAP + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)CAP * dmax);
    base_adj = malloc(sizeof(int) * (size_t)CAP * dmax);
    deg = calloc((size_t)CAP, sizeof(int));
    base_deg = calloc((size_t)CAP, sizeof(int));
    side = malloc(sizeof(int) * (size_t)CAP);
    for (int v = 0; v < CAP; v++) side[v] = -1;
    for (int b = 0; b < 3; b++) bufs[b] = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    best_e = malloc(sizeof(int) * 2 * (size_t)CAP * dmax);
    int *qu = malloc(sizeof(int) * (size_t)CAP);

    /* Validate and load the start graph; echo it back if it is unusable. */
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) ok = 0;
        else if (has_edge(u, v)) ok = 0;
        else if (deg[u] >= dmax || deg[v] >= dmax) ok = 0;
        else raw_add(u, v);
    }
    for (int s = 0; s < n0 && ok; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t && ok) {
            int x = qu[h++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x * dmax + k];
                if (side[y] < 0) { side[y] = 1 - side[x]; qu[t++] = y; }
                else if (side[y] == side[x]) { ok = 0; break; }
            }
        }
    }
    if (!ok) {
        echo_input(n0, m0, eu, ev);
        return 0;
    }

    N = n0;
    curb = 0;
    int ix = ball();
    curb = ix;
    cur_cost = count_bad(bufs[ix]);
    best_n = 0;
    best_m = 0;
    if (cur_cost == 0) save_best();
    else {
        anneal(FIX_ITERS, 0.8);
        if (cur_cost == 0) save_best();
    }
    if (best_n == 0) {
        echo_input(n0, m0, eu, ev);
        return 0;
    }

    int base_N = N;
    memcpy(base_adj, adj, sizeof(int) * (size_t)CAP * dmax);
    memcpy(base_deg, deg, sizeof(int) * (size_t)CAP);

    while (cpu_now() < deadline) {
        int v = N;
        N++;
        deg[v] = 0;
        side[v] = rndint(2);

        /* Fill the new vertex from the opposite side, then add spare edges elsewhere. */
        for (int t = 0; t < 4 * N && deg[v] < dmax; t++) {
            int w = rndint(N);
            if (w == v || side[w] == side[v] || deg[w] >= dmax || has_edge(v, w)) continue;
            raw_add(v, w);
        }
        for (int t = 0; t < 2 * N; t++) {
            propose_add();
            nops = 0;
        }
        nops = 0;

        ix = ball();
        curb = ix;
        cur_cost = count_bad(bufs[ix]);
        if (cur_cost > 0) anneal(ATTEMPT_ITERS, 1.0);

        if (cur_cost == 0) {
            save_best();
            base_N = N;
            memcpy(base_adj, adj, sizeof(int) * (size_t)CAP * dmax);
            memcpy(base_deg, deg, sizeof(int) * (size_t)CAP);
        } else {
            N = base_N;
            memcpy(adj, base_adj, sizeof(int) * (size_t)CAP * dmax);
            memcpy(deg, base_deg, sizeof(int) * (size_t)CAP);
            ix = ball();
            curb = ix;
            cur_cost = count_bad(bufs[ix]);
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per point of S (joined to lines through it) and a
    new B-vertex per line index in S (joined to points on it)."""
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
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Simulated annealing over bi-Cayley voltage lifts (parent, unchanged).
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
# C repair search (new in this version).
# ----------------------------------------------------------------------------

def _c_repair(n, edges, d, D, seed, budget):
    """Run the C annealer from (n, edges) for `budget` seconds; return a valid (n, edges) or None."""
    if budget < 1.0:
        return None
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                         stdin_graph=(n, edges), timeout=budget + 10.0)
        n2, e2 = lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return None
    if lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for n_c, e_c in _arc_extensions(d, deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New: C repair search from the best graph. Skipped when the Moore bound is reached.
    if D >= 3 and best_n < lib.moore_bound(d, D):
        remaining = deadline - time.monotonic() - 2.0
        if remaining > 2.0:
            frac = 0.85 if D == 3 else 0.5
            res = _c_repair(best_n, best[1], d, D, seed, frac * remaining)
            if res is not None:
                consider(res[0], res[1])

    # Remaining time: annealed group voltage lifts.
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
