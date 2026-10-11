import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). With d >= q+1 each old vertex has
# spare capacity s = d - q - 1. Pick a point set S with every line holding <= s
# points of S and every point on <= s lines indexed by S. For each P in S add a
# new A-vertex on all q+1 lines through P; for each j in S add a new B-vertex on
# all q+1 points of line j. Order is 2(q^2+q+1) + 2|S|.
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# C search: vertex insertion by simulated annealing (diameter-D repair).
#
# Starting from a valid bipartite graph, the program appends one vertex at a time
# and anneals over degree-preserving double edge swaps and attach/detach/relocate
# moves on the new vertex. Cost = ordered pairs at distance > D (bitset BFS).
# Each success is snapshotted; failures roll back to the last snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 32
#define MAXW 16
#define MAXLOG 64

static int n, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int sn = 0;
static int sdeg[MAXN];
static int sadj[MAXN][MAXDEG];
static int logk[MAXLOG][3];
static int log_n = 0;
static uint64_t rs = 88172645463325252ULL;
static double t_budget = 1.0;
static clock_t t_start;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) / 9007199254740992.0; }
static int timed_out(void) { return (double)(clock() - t_start) / CLOCKS_PER_SEC > t_budget; }

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}
static void raw_add(int u, int v) { adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
static void raw_rem(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; break; }
    for (int i = 0; i < deg[v]; i++) if (adj[v][i] == u) { adj[v][i] = adj[v][--deg[v]]; break; }
}
static void L_add(int u, int v) {
    raw_add(u, v); logk[log_n][0] = 0; logk[log_n][1] = u; logk[log_n][2] = v; log_n++;
}
static void L_rem(int u, int v) {
    raw_rem(u, v); logk[log_n][0] = 1; logk[log_n][1] = u; logk[log_n][2] = v; log_n++;
}
static void undo(void) {
    while (log_n > 0) {
        log_n--;
        int u = logk[log_n][1], v = logk[log_n][2];
        if (logk[log_n][0] == 0) raw_rem(u, v); else raw_add(u, v);
    }
}
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static long long cost_fn(void) {
    int nw = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * nw);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = RB[v];
            memcpy(o, RA[v], sizeof(uint64_t) * nw);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = RA[adj[v][i]];
                for (int k = 0; k < nw; k++) o[k] |= s[k];
            }
        }
        for (int v = 0; v < n; v++) memcpy(RA[v], RB[v], sizeof(uint64_t) * nw);
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < nw; k++) c += popc(RA[v][k]);
        bad += n - c;
    }
    return bad;
}

static int move_swap(void) {
    int a = rndint(n), c = rndint(n);
    if (a == c || deg[a] == 0 || deg[c] == 0 || col[a] != col[c]) return 0;
    int b = adj[a][rndint(deg[a])], e = adj[c][rndint(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    L_rem(a, b); L_rem(c, e); L_add(a, e); L_add(c, b);
    return 1;
}

static int move_x(int x) {
    int r = rndint(3);
    if (r == 0) {
        if (deg[x] >= d) return 0;
        int w = rndint(n);
        if (w == x || col[w] == col[x] || deg[w] >= d || has_edge(x, w)) return 0;
        L_add(x, w); return 1;
    } else if (r == 1) {
        if (deg[x] == 0) return 0;
        L_rem(x, adj[x][rndint(deg[x])]); return 1;
    } else {
        if (deg[x] == 0) return 0;
        int w = adj[x][rndint(deg[x])];
        int w2 = rndint(n);
        if (w2 == x || col[w2] == col[x] || deg[w2] >= d || has_edge(x, w2)) return 0;
        L_rem(x, w); L_add(x, w2); return 1;
    }
}

static int propose(int x) {
    log_n = 0;
    if (rndint(10) < 3) return move_x(x);
    return move_swap();
}

static void snapshot(void) {
    sn = n;
    for (int v = 0; v < n; v++) { sdeg[v] = deg[v]; memcpy(sadj[v], adj[v], sizeof(int) * deg[v]); }
}
static void restore(void) {
    n = sn;
    for (int v = 0; v < sn; v++) { deg[v] = sdeg[v]; memcpy(adj[v], sadj[v], sizeof(int) * sdeg[v]); }
    log_n = 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]); D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    t_budget = atof(argv[4]);
    t_start = clock();
    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n < 0 || n > MAXN - 256 || d < 1 || d > MAXDEG || D < 1) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        raw_add(u, v);
    }
    int *q = malloc(sizeof(int) * (n + 1));
    for (int v = 0; v < n; v++) col[v] = -1;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0; int qh = 0, qt = 0; q[qt++] = s;
        while (qh < qt && ok) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; q[qt++] = v; }
                else if (col[v] == col[u]) ok = 0;
            }
        }
    }
    free(q);
    if (!ok || cost_fn() != 0) { printf("0 0\n"); return 0; }
    snapshot();

    while (!timed_out() && n + 1 < MAXN) {
        int x = n;
        n++; deg[x] = 0; col[x] = rndint(2);
        long long c = cost_fn();
        double T = 1.0;
        long long since = 0;
        log_n = 0;
        while (c != 0 && !timed_out() && since < 200000) {
            since++;
            if (T > 0.05) T *= 0.99995;
            if (!propose(x)) continue;
            long long c2 = cost_fn();
            long long delta = c2 - c;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) c = c2;
            else undo();
            log_n = 0;
            if (c < 1000000000LL) since = (c == 0) ? since : since;
        }
        if (c == 0) snapshot();
        else restore();
    }

    int me = 0;
    for (int v = 0; v < sn; v++) me += sdeg[v];
    me /= 2;
    printf("%d %d\n", sn, me);
    for (int v = 0; v < sn; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (sadj[v][i] > v) printf("%d %d\n", v, sadj[v][i]);
    return 0;
}
'''


def _augment_c(d, D, seed, n, edges, budget):
    """Run the C insertion search from (n, edges); return (n2, edges2) or None."""
    if budget < 1.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=(n, edges),
                        timeout=budget + 15.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


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
# Simulated annealing over bi-Cayley voltage lifts.
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


def _has_spare(n, edges, d):
    """True if some vertex has degree below d (so a vertex can be inserted)."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return any(x < d for x in deg)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
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

    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

        # New: grow the best diameter-3 graph by inserting vertices with C annealing.
        # Insertion never breaks existing pairs, so the search only has to cover the new vertex.
        if _has_spare(best_n, best[1], d):
            budget = 0.55 * time_limit - (time.monotonic() - start) - 2.0
            res = _augment_c(d, D, seed, best_n, best[1], budget)
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts. For D >= 5 use larger bases.
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
