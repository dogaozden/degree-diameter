import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static unsigned char pc16[65536];
static int pc64(u64 x) {
    return pc16[x & 0xFFFFu] + pc16[(x >> 16) & 0xFFFFu] +
           pc16[(x >> 32) & 0xFFFFu] + pc16[(x >> 48) & 0xFFFFu];
}

static int d, D, CAP, n, Wcap;
static int *adj, *deg, *side, *perm, *lst[2], lcnt[2];
static unsigned char *M;
static u64 *R0, *R1;
static int *badj, *bdeg, *radj, *rdeg;
static int best_n;
static double budget_s;
static clock_t t0;

#define MT(u, v) M[(size_t)(u) * (size_t)CAP + (size_t)(v)]
#define ADJ(u, k) adj[(size_t)(u) * (size_t)d + (size_t)(k)]
#define RADJ(u, k) radj[(size_t)(u) * (size_t)d + (size_t)(k)]

static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static void add_edge(int u, int v) {
    ADJ(u, deg[u]) = v;
    deg[u]++;
    ADJ(v, deg[v]) = u;
    deg[v]++;
    MT(u, v) = 1;
    MT(v, u) = 1;
}

static void del_from(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (ADJ(u, k) == v) {
            ADJ(u, k) = ADJ(u, deg[u] - 1);
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_from(u, v);
    del_from(v, u);
    MT(u, v) = 0;
    MT(v, u) = 0;
}

/* Sum over vertices of the number of vertices at distance > D (ordered pairs). */
static long eval_cost(void) {
    int Wn = (n + 63) / 64;
    u64 *prev = R0, *cur = R1;
    memset(prev, 0, sizeof(u64) * (size_t)n * (size_t)Wn);
    for (int v = 0; v < n; v++)
        prev[(size_t)v * Wn + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            u64 *cv = cur + (size_t)v * Wn;
            memcpy(cv, prev + (size_t)v * Wn, sizeof(u64) * (size_t)Wn);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *pu = prev + (size_t)ADJ(v, k) * Wn;
                for (int w = 0; w < Wn; w++) cv[w] |= pu[w];
            }
        }
        u64 *tmp = prev;
        prev = cur;
        cur = tmp;
    }
    long miss = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const u64 *pv = prev + (size_t)v * Wn;
        for (int w = 0; w < Wn; w++) c += pc64(pv[w]);
        miss += n - c;
    }
    return miss;
}

static void take_snapshot(void) {
    memcpy(badj, adj, sizeof(int) * (size_t)CAP * (size_t)d);
    memcpy(bdeg, deg, sizeof(int) * (size_t)CAP);
}

static void restore_snapshot(void) {
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++) MT(v, ADJ(v, k)) = 0;
    memcpy(adj, badj, sizeof(int) * (size_t)CAP * (size_t)d);
    memcpy(deg, bdeg, sizeof(int) * (size_t)CAP);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++) MT(v, ADJ(v, k)) = 1;
}

static void record_best(void) {
    memcpy(radj, adj, sizeof(int) * (size_t)CAP * (size_t)d);
    memcpy(rdeg, deg, sizeof(int) * (size_t)CAP);
    best_n = n;
}

typedef struct { int type, a, b, c, e; } Move;
static Move mv;

static int propose(void) {
    int r = rndint(100);
    if (r < 60) {
        /* degree-preserving 2-switch on one side */
        int s = rndint(2);
        if (lcnt[s] < 2) return 0;
        int x = lst[s][rndint(lcnt[s])];
        int x2 = lst[s][rndint(lcnt[s])];
        if (x == x2 || deg[x] == 0 || deg[x2] == 0) return 0;
        int y = ADJ(x, rndint(deg[x]));
        int y2 = ADJ(x2, rndint(deg[x2]));
        if (y == y2 || MT(x, y2) || MT(x2, y)) return 0;
        del_edge(x, y);
        del_edge(x2, y2);
        add_edge(x, y2);
        add_edge(x2, y);
        mv.type = 0; mv.a = x; mv.b = y; mv.c = x2; mv.e = y2;
        return 1;
    } else if (r < 85) {
        /* move one endpoint of an edge to another vertex with spare capacity */
        int x = rndint(n);
        if (deg[x] == 0) return 0;
        int y = ADJ(x, rndint(deg[x]));
        int s = side[y];
        if (lcnt[s] < 2) return 0;
        int y2 = lst[s][rndint(lcnt[s])];
        if (y2 == y || deg[y2] >= d || MT(x, y2)) return 0;
        del_edge(x, y);
        add_edge(x, y2);
        mv.type = 1; mv.a = x; mv.b = y; mv.c = y2;
        return 1;
    } else {
        /* add an edge between spare vertices on opposite sides */
        if (lcnt[0] == 0 || lcnt[1] == 0) return 0;
        int a = lst[0][rndint(lcnt[0])];
        int b = lst[1][rndint(lcnt[1])];
        if (deg[a] >= d || deg[b] >= d || MT(a, b)) return 0;
        add_edge(a, b);
        mv.type = 2; mv.a = a; mv.b = b;
        return 1;
    }
}

static void undo(void) {
    if (mv.type == 0) {
        del_edge(mv.a, mv.e);
        del_edge(mv.c, mv.b);
        add_edge(mv.a, mv.b);
        add_edge(mv.c, mv.e);
    } else if (mv.type == 1) {
        del_edge(mv.a, mv.c);
        add_edge(mv.a, mv.b);
    } else {
        del_edge(mv.a, mv.b);
    }
}

static void attach(int v, int o) {
    int c = lcnt[o];
    if (c == 0) return;
    memcpy(perm, lst[o], sizeof(int) * (size_t)c);
    for (int i = c - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = perm[i];
        perm[i] = perm[j];
        perm[j] = t;
    }
    for (int i = 0; i < c && deg[v] < d; i++) {
        int u = perm[i];
        if (deg[u] < d && u != v && !MT(u, v)) add_edge(u, v);
    }
}

/* Add one new A vertex and one new B vertex, each greedily attached to spare capacity. */
static int add_pair(void) {
    if (n + 2 > CAP) return 0;
    int a = n, b = n + 1;
    side[a] = 0;
    side[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    attach(a, 1);
    lst[0][lcnt[0]++] = a;
    attach(b, 0);
    lst[1][lcnt[1]++] = b;
    n += 2;
    return 1;
}

/* Simulated annealing at the current size. Returns 1 if a valid graph (cost 0) is reached. */
static int run_size(double T0, double T1, long cycle) {
    long cur = eval_cost();
    long bestc = cur;
    take_snapshot();
    if (cur == 0) return 1;
    for (long it = 1;; it++) {
        if ((it & 127) == 0 && elapsed() > budget_s) return 0;
        if (it % cycle == 0) {
            restore_snapshot();
            cur = eval_cost();
        }
        double frac = (double)(it % cycle) / (double)cycle;
        double T = T0 * pow(T1 / T0, frac);
        if (!propose()) continue;
        long c2 = eval_cost();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                take_snapshot();
            }
            if (cur == 0) return 1;
        } else {
            undo();
        }
    }
}

static void emit(void) {
    long m = 0;
    for (int v = 0; v < best_n; v++)
        for (int k = 0; k < rdeg[v]; k++)
            if (RADJ(v, k) > v) m++;
    printf("%d %ld\n", best_n, m);
    for (int v = 0; v < best_n; v++)
        for (int k = 0; k < rdeg[v]; k++) {
            int u = RADJ(v, k);
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    t0 = clock();
    for (int i = 0; i < 65536; i++) {
        int x = i, c = 0;
        while (x) {
            x &= x - 1;
            c++;
        }
        pc16[i] = (unsigned char)c;
    }
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    CAP = 2 * n0 + 64;
    Wcap = (CAP + 63) / 64;
    adj = calloc((size_t)CAP * (size_t)d, sizeof(int));
    deg = calloc((size_t)CAP, sizeof(int));
    side = calloc((size_t)CAP, sizeof(int));
    perm = calloc((size_t)CAP, sizeof(int));
    lst[0] = calloc((size_t)CAP, sizeof(int));
    lst[1] = calloc((size_t)CAP, sizeof(int));
    M = calloc((size_t)CAP * (size_t)CAP, 1);
    R0 = calloc((size_t)CAP * (size_t)Wcap, sizeof(u64));
    R1 = calloc((size_t)CAP * (size_t)Wcap, sizeof(u64));
    badj = calloc((size_t)CAP * (size_t)d, sizeof(int));
    bdeg = calloc((size_t)CAP, sizeof(int));
    radj = calloc((size_t)CAP * (size_t)d, sizeof(int));
    rdeg = calloc((size_t)CAP, sizeof(int));
    if (!adj || !deg || !side || !perm || !lst[0] || !lst[1] || !M || !R0 || !R1 ||
        !badj || !bdeg || !radj || !rdeg) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            ok = 0;
            break;
        }
        if (u < 0 || v < 0 || u >= n || v >= n) {
            ok = 0;
            continue;
        }
        if (u == v || MT(u, v)) continue;
        if (deg[u] >= d || deg[v] >= d) {
            ok = 0;
            continue;
        }
        add_edge(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    /* 2-colour the start graph; the search only keeps it bipartite. */
    int *col = calloc((size_t)CAP, sizeof(int));
    int *qu = calloc((size_t)CAP, sizeof(int));
    for (int v = 0; v < n; v++) col[v] = -1;
    int bip = 1;
    for (int s0 = 0; s0 < n; s0++) {
        if (col[s0] >= 0) continue;
        int qh = 0, qt = 0;
        col[s0] = 0;
        qu[qt++] = s0;
        while (qh < qt) {
            int u = qu[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = ADJ(u, k);
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    qu[qt++] = w;
                } else if (col[w] == col[u]) {
                    bip = 0;
                }
            }
        }
    }
    long spare = 0;
    for (int v = 0; v < n; v++) {
        side[v] = col[v] < 0 ? 0 : col[v];
        spare += d - deg[v];
    }
    record_best();
    if (!bip || spare == 0) {
        emit();
        return 0;
    }
    for (int v = 0; v < n; v++) lst[side[v]][lcnt[side[v]]++] = v;

    double T0 = 3.0, T1 = 0.2;
    long cycle = 20000;
    while (elapsed() < budget_s) {
        if (!run_size(T0, T1, cycle)) break;
        record_best();
        if (!add_pair()) break;
    }
    emit();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q); each old vertex has spare degree s = d - q - 1. Choose
# point set S with every line holding <= s points of S, and line set T with
# every point on <= s lines of T. Add an A-vertex per point of S (joined to the
# q+1 lines through it) and a B-vertex per line of T (joined to its q+1 points).
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
# Python voltage-lift annealing: fallback only if the C engine is unavailable.
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
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
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


def _voltage_search(d, D, best, rng, deadline):
    best_n = best[0]
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
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            return res
    return None


# ----------------------------------------------------------------------------
# New search stage: C simulated annealing that grows a valid graph by adding
# vertex pairs and repairing diameter (bipartition kept fixed).
# ----------------------------------------------------------------------------

def _has_spare(d, graph):
    n, edges = graph
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return any(x < d for x in deg)


def _c_augment(d, D, graph, seed, budget):
    n0, e0 = graph
    text = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 20.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    deadline = t_start + 0.72 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        for cand in _arc_extensions(d, deadline, random.Random(seed * 7919 + d)):
            consider(cand)

    # Generalized quadrangle baseline (diameter 4).
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Main new stage: C annealing that adds vertex pairs to the current best.
    c_ok = False
    if D >= 2 and _has_spare(d, best):
        remaining = deadline - time.monotonic()
        if remaining > 4.0:
            try:
                cand = _c_augment(d, D, best, seed, remaining - 2.0)
                consider(cand)
                c_ok = True
            except Exception:
                c_ok = False

    # Python fallback if the C engine could not run.
    if not c_ok and time.monotonic() < deadline - 1.0:
        res = _voltage_search(d, D, best, rng, deadline)
        if res is not None:
            consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
