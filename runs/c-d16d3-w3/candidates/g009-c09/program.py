import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite graphs with degree <= d and
# diameter <= D. It starts from a valid graph, repeatedly adds one vertex
# (to the smaller side), and anneals the number of vertex pairs at distance
# > D back to zero. Only zero-cost states are ever saved, so the output is
# always valid. Moves keep the graph bipartite and the degrees bounded.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXLOG 8

static int DEG = 1, DIAM = 1;
static int NCAP = 0, W = 1;
static int n = 0;
static int *side = NULL, *deg = NULL, *adj = NULL;
static int *sl[2];
static int sc[2];
static u64 *bufA = NULL, *bufB = NULL;
static int *snap_side = NULL, *snap_u = NULL, *snap_v = NULL;
static int best_n = 0, best_m = 0;
static int lg_n = 0, lg_op[MAXLOG], lg_a[MAXLOG], lg_b[MAXLOG];
static u64 rs = 88172645463325252ULL;

static inline u64 rnd64(void) {
    u64 x = rs;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rs = x;
    return x;
}

static inline int rndi(int k) {
    return (int)(rnd64() % (u64)k);
}

static inline double rndd(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int k = 0; k < deg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void list_add(int a, int b) {
    adj[(size_t)a * DEG + deg[a]] = b;
    deg[a]++;
}

static void list_del(int a, int b) {
    int *p = adj + (size_t)a * DEG;
    int da = deg[a];
    for (int k = 0; k < da; k++) {
        if (p[k] == b) {
            p[k] = p[da - 1];
            deg[a] = da - 1;
            return;
        }
    }
}

static void edge_add(int a, int b) {
    list_add(a, b);
    list_add(b, a);
}

static void edge_del(int a, int b) {
    list_del(a, b);
    list_del(b, a);
}

static void mv_add(int a, int b) {
    edge_add(a, b);
    lg_op[lg_n] = 0; lg_a[lg_n] = a; lg_b[lg_n] = b;
    lg_n++;
}

static void mv_del(int a, int b) {
    edge_del(a, b);
    lg_op[lg_n] = 1; lg_a[lg_n] = a; lg_b[lg_n] = b;
    lg_n++;
}

static void mv_undo(void) {
    while (lg_n > 0) {
        lg_n--;
        if (lg_op[lg_n] == 0) edge_del(lg_a[lg_n], lg_b[lg_n]);
        else edge_add(lg_a[lg_n], lg_b[lg_n]);
    }
}

/* Number of unordered vertex pairs at distance > DIAM (disconnected counts). */
static long long cost_eval(void) {
    u64 *cur = bufA, *nxt = bufB;
    size_t tot = (size_t)n * W;
    memset(cur, 0, tot * sizeof(u64));
    for (int v = 0; v < n; v++) {
        u64 *c = cur + (size_t)v * W;
        c[v >> 6] |= 1ULL << (v & 63);
        const int *p = adj + (size_t)v * DEG;
        for (int k = 0; k < deg[v]; k++) {
            int u = p[k];
            c[u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int r = 1; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            u64 *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, (size_t)W * sizeof(u64));
            const int *p = adj + (size_t)v * DEG;
            for (int k = 0; k < deg[v]; k++) {
                const u64 *s = cur + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const u64 *c = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(c[w]);
        bad += (long long)(n - cnt);
    }
    return bad / 2;
}

static void snapshot(void) {
    best_n = n;
    best_m = 0;
    for (int v = 0; v < n; v++) snap_side[v] = side[v];
    for (int v = 0; v < n; v++) {
        if (side[v] != 0) continue;
        const int *p = adj + (size_t)v * DEG;
        for (int k = 0; k < deg[v]; k++) {
            snap_u[best_m] = v;
            snap_v[best_m] = p[k];
            best_m++;
        }
    }
}

static void restore_best(void) {
    n = best_n;
    sc[0] = 0; sc[1] = 0;
    for (int v = 0; v < n; v++) {
        side[v] = snap_side[v];
        deg[v] = 0;
        sl[side[v]][sc[side[v]]++] = v;
    }
    for (int i = 0; i < best_m; i++) edge_add(snap_u[i], snap_v[i]);
}

static void grow(void) {
    if (n >= NCAP) return;
    int s = (sc[0] <= sc[1]) ? 0 : 1;
    side[n] = s;
    deg[n] = 0;
    sl[s][sc[s]++] = n;
    n++;
}

static int pick_free(int s) {
    for (int t = 0; t < 24; t++) {
        int v = sl[s][rndi(sc[s])];
        if (deg[v] < DEG) return v;
    }
    int st = rndi(sc[s]);
    for (int t = 0; t < sc[s]; t++) {
        int v = sl[s][(st + t) % sc[s]];
        if (deg[v] < DEG) return v;
    }
    return -1;
}

/* Propose one move; returns 0 if nothing was changed. */
static int propose(void) {
    lg_n = 0;
    int r = rndi(100);
    if (r < 30) {
        int x = pick_free(0);
        int y = pick_free(1);
        if (x < 0 || y < 0 || has_edge(x, y)) return 0;
        mv_add(x, y);
        return 1;
    }
    if (r < 60) {
        /* rewire one endpoint of an edge, keeping the side of the moved end */
        int s = rndi(2);
        int x = sl[s][rndi(sc[s])];
        if (deg[x] == 0) return 0;
        int y = adj[(size_t)x * DEG + rndi(deg[x])];
        int z = pick_free(side[y]);
        if (z < 0 || z == y || has_edge(x, z)) return 0;
        mv_del(x, y);
        mv_add(x, z);
        return 1;
    }
    if (r < 95) {
        /* degree-preserving double edge swap */
        int x = sl[0][rndi(sc[0])];
        int x2 = sl[0][rndi(sc[0])];
        if (x == x2 || deg[x] == 0 || deg[x2] == 0) return 0;
        int y = adj[(size_t)x * DEG + rndi(deg[x])];
        int y2 = adj[(size_t)x2 * DEG + rndi(deg[x2])];
        if (y == y2 || has_edge(x, y2) || has_edge(x2, y)) return 0;
        mv_del(x, y);
        mv_del(x2, y2);
        mv_add(x, y2);
        mv_add(x2, y);
        return 1;
    }
    {
        /* remove one edge (frees capacity) */
        int s = rndi(2);
        int x = sl[s][rndi(sc[s])];
        if (deg[x] == 0) return 0;
        int y = adj[(size_t)x * DEG + rndi(deg[x])];
        mv_del(x, y);
        return 1;
    }
}

static void emit_input(int n_in, int m_in, const int *eu, const int *ev) {
    printf("%d %d\n", n_in, m_in);
    for (int i = 0; i < m_in; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1) d = 1;
    if (DIAM < 1) DIAM = 1;
    DEG = d;
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd64();
    clock_t t0 = clock();

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) { printf("1 0\n"); return 0; }
    if (n_in <= 0) { printf("1 0\n"); return 0; }
    if (m_in < 0) m_in = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m_in + 1));
    for (int i = 0; i < m_in; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m_in = i; break; }
    }

    NCAP = n_in + n_in / 2 + 64;
    if (NCAP > 4000) NCAP = 4000;
    if (NCAP < n_in) NCAP = n_in;
    W = (NCAP + 63) / 64;
    side = malloc(sizeof(int) * (size_t)NCAP);
    deg = calloc((size_t)NCAP, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)NCAP * DEG);
    sl[0] = malloc(sizeof(int) * (size_t)NCAP);
    sl[1] = malloc(sizeof(int) * (size_t)NCAP);
    bufA = malloc(sizeof(u64) * (size_t)NCAP * W);
    bufB = malloc(sizeof(u64) * (size_t)NCAP * W);
    snap_side = malloc(sizeof(int) * (size_t)NCAP);
    snap_u = malloc(sizeof(int) * (size_t)NCAP * DEG);
    snap_v = malloc(sizeof(int) * (size_t)NCAP * DEG);

    /* Load the input graph, checking that it is simple and degree-bounded. */
    n = n_in;
    int ok = 1;
    for (int i = 0; i < m_in && ok; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) ok = 0;
        else if (deg[a] >= DEG || deg[b] >= DEG) ok = 0;
        else if (has_edge(a, b)) ok = 0;
        else edge_add(a, b);
    }
    if (!ok) { emit_input(n_in, m_in, eu, ev); return 0; }

    /* Bipartition by BFS. */
    int *col = malloc(sizeof(int) * (size_t)n);
    int *queue = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    int bip = 1;
    for (int s0 = 0; s0 < n && bip; s0++) {
        if (col[s0] >= 0) continue;
        col[s0] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s0;
        while (qh < qt && bip) {
            int u = queue[qh++];
            const int *p = adj + (size_t)u * DEG;
            for (int k = 0; k < deg[u]; k++) {
                int w = p[k];
                if (col[w] < 0) { col[w] = 1 - col[u]; queue[qt++] = w; }
                else if (col[w] == col[u]) { bip = 0; break; }
            }
        }
    }
    if (!bip) { emit_input(n_in, m_in, eu, ev); return 0; }

    sc[0] = 0; sc[1] = 0;
    for (int v = 0; v < n; v++) {
        side[v] = col[v];
        sl[side[v]][sc[side[v]]++] = v;
    }
    if (sc[0] == 0 || sc[1] == 0) { emit_input(n_in, m_in, eu, ev); return 0; }

    long long cur = cost_eval();
    if (cur != 0) { emit_input(n_in, m_in, eu, ev); return 0; }
    snapshot();

    grow();
    cur = cost_eval();
    long long att = 0;
    long long att_max = 60000LL + 150LL * n;
    long long it = 0;

    while (1) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
        }
        it++;
        if (att >= att_max) {
            restore_best();
            if (n >= NCAP) break;
            grow();
            cur = cost_eval();
            att = 0;
            att_max = 60000LL + 150LL * n;
            continue;
        }
        double frac = (double)att / (double)att_max;
        double T = 1.0 * (1.0 - frac) + 0.05;
        att++;
        if (!propose()) continue;
        long long c2 = cost_eval();
        long long delta = c2 - cur;
        if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            mv_undo();
        }
        if (cur == 0) {
            if (n > best_n) snapshot();
            if (n >= NCAP) break;
            grow();
            cur = cost_eval();
            att = 0;
            att_max = 60000LL + 150LL * n;
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", snap_u[i], snap_v[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add one new A-vertex per entry
# of a multiset SA of points (joined to the q+1 lines through it, with each
# line hit at most s times) and one new B-vertex per entry of SB.
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
    """True if every target t is hit by <= s entries of S (repeats counted)."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets with every target hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
        SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
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
# Annealed bi-Cayley voltage lifts (used only for D >= 5, as a start graph).
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
    T = float(time_limit)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Start-graph phase (Python constructions), kept within ~20-40% of the budget.
    if D >= 3:
        try:
            cands = _arc_extensions(d, t0 + 0.2 * T, random.Random(seed * 7919 + d))
            cands.sort(key=lambda t: -t[0])
            for n_c, e_c in cands[:6]:
                consider(n_c, e_c)
        except Exception:
            pass

    if D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if D >= 5:
        try:
            rng = random.Random(seed)
            dl = t0 + 0.4 * T
            ks = [1, 2, 2, 3, 4]
            while time.monotonic() < dl:
                k = rng.choice(ks)
                base = best[0] // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, dl, iters=400)
                if res is not None:
                    consider(res[0], res[1])
        except Exception:
            pass

    # Main phase: C annealing that grows the best valid graph by vertices.
    budget = t0 + 0.9 * T - 1.5 - time.monotonic()
    if budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 10.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
