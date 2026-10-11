"""Arc-extended projective planes, plus a C repair search for D = 3.

Pipeline:
  1. Arc-extended PG(2, q) incidence graphs (valid for D >= 3).
  2. For D = 3, a C simulated-annealing engine inserts vertices into the best
     valid graph and keeps any state with zero bad pairs. It only returns a graph
     that lib.is_valid accepts; otherwise the Python fallback is used.
  3. For D >= 4, the parent's Python voltage annealing and GQ baseline are kept.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C repair engine (D = 3 target). Input: valid graph on stdin, args d D seed time.
# Repeatedly inserts one vertex and anneals the edge set (degree-preserving
# 2-switches and spare-slot additions) to reach zero pairs at distance > D.
# Sides of the bipartition are kept, so the graph stays bipartite.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define MAXW 16
#define EPOCH 20000
#define TSTART 1.5
#define TEND 0.1

static int dmax, diam;
static int N;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char adj[MAXN][MAXN];
static uint64_t R0[MAXN][MAXW], R1[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int bn, bm;
static int bu[MAXN * MAXD], bv[MAXN * MAXD];

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    adj[u][v] = adj[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; return; }
}

static void del_edge(int u, int v) {
    adj[u][v] = adj[v][u] = 0;
    del_nb(u, v);
    del_nb(v, u);
}

/* Number of unordered vertex pairs at distance > diam. Zero means valid. */
static long cost_of(void) {
    int nw = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(R0[v], 0, sizeof(uint64_t) * nw);
        R0[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < diam; it++) {
        for (int v = 0; v < N; v++) {
            memcpy(R1[v], R0[v], sizeof(uint64_t) * nw);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *s = R0[nb[v][i]];
                for (int w = 0; w < nw; w++) R1[v][w] |= s[w];
            }
        }
        for (int v = 0; v < N; v++) memcpy(R0[v], R1[v], sizeof(uint64_t) * nw);
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(R0[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void save_best(void) {
    bn = N;
    bm = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u) {
                bu[bm] = u;
                bv[bm] = nb[u][i];
                bm++;
            }
}

static void pick_edge(int *x, int *y) {
    int u;
    do { u = rndi(N); } while (deg[u] == 0);
    int v = nb[u][rndi(deg[u])];
    if (side[u] == 0) { *x = u; *y = v; }
    else { *x = v; *y = u; }
}

static int try_switch(int *x1, int *y1, int *x2, int *y2) {
    pick_edge(x1, y1);
    pick_edge(x2, y2);
    if (*x1 == *x2 || *y1 == *y2) return 0;
    if (adj[*x1][*y2] || adj[*x2][*y1]) return 0;
    del_edge(*x1, *y1);
    del_edge(*x2, *y2);
    add_edge(*x1, *y2);
    add_edge(*x2, *y1);
    return 1;
}

static void undo_switch(int x1, int y1, int x2, int y2) {
    del_edge(x1, y2);
    del_edge(x2, y1);
    add_edge(x1, y1);
    add_edge(x2, y2);
}

static int find_spare(int want, int *out) {
    for (int t = 0; t < 400; t++) {
        int u = rndi(N);
        if (side[u] == want && deg[u] < dmax) { *out = u; return 1; }
    }
    return 0;
}

static int try_add(int *x, int *y) {
    int a, b;
    if (!find_spare(0, &a) || !find_spare(1, &b)) return 0;
    if (adj[a][b]) return 0;
    add_edge(a, b);
    *x = a;
    *y = b;
    return 1;
}

/* Add vertex N on a random side, filling its dmax slots from the other side. */
static void insert_vertex(void) {
    int v = N++;
    int s = rndi(2), t = 1 - s;
    deg[v] = 0;
    side[v] = s;
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < v; u++)
        if (side[u] == t && deg[u] < dmax) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
    for (int i = 0; i < nc && deg[v] < dmax; i++) add_edge(v, cand[i]);
    while (deg[v] < dmax) {
        int w, tries = 0;
        do {
            w = rndi(v);
            tries++;
        } while ((side[w] != t || adj[v][w]) && tries < 100000);
        if (side[w] != t || adj[v][w]) break;
        if (deg[w] == 0) break;
        int x = nb[w][rndi(deg[w])];
        del_edge(w, x);
        add_edge(v, w);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    diam = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 2 || dmax < 1 || dmax >= MAXD || diam < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adj[u][v]) continue;
        if (deg[u] >= dmax || deg[v] >= dmax) { printf("0 0\n"); return 0; }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int i = 0; i < N; i++) side[i] = -1;
    static int q[MAXN];
    for (int s0 = 0; s0 < N; s0++) {
        if (side[s0] != -1) continue;
        side[s0] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s0;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (side[v] == -1) { side[v] = 1 - side[u]; q[qt++] = v; }
                else if (side[v] == side[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    int c0 = 0, c1 = 0, total = 0;
    for (int i = 0; i < N; i++) { if (side[i] == 0) c0++; else c1++; total += deg[i]; }
    if (c0 == 0 || c1 == 0 || total == 0) { printf("0 0\n"); return 0; }

    save_best();
    long cur = cost_of();
    long it = 0;
    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        if (cur == 0) {
            save_best();
            if (N >= MAXN - 2) break;
            insert_vertex();
            cur = cost_of();
            continue;
        }
        it++;
        double frac = (double)(it % EPOCH) / EPOCH;
        double T = TSTART * pow(TEND / TSTART, frac);
        int x1, y1, x2, y2;
        if (rndu() < 0.1) {
            if (!try_add(&x1, &y1)) continue;
            long c2 = cost_of();
            long delta = c2 - cur;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) cur = c2;
            else del_edge(x1, y1);
        } else {
            if (!try_switch(&x1, &y1, &x2, &y2)) continue;
            long c2 = cost_of();
            long delta = c2 - cur;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) cur = c2;
            else undo_switch(x1, y1, x2, y2);
        }
    }
    if (cur == 0) save_best();

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add one A-vertex per point of SA
# (joined to the q+1 lines through it, each line in <= s such sets) and one
# B-vertex per line of SB (joined to its q+1 points, each point in <= s sets).
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# Simulated annealing over bi-Cayley voltage lifts (D >= 4 path, unchanged).
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
# C repair (D = 3). Any failure returns None, so the Python fallback is kept.
# ----------------------------------------------------------------------------

def _c_repair(d, D, start_graph, budget, seed):
    """Run the C insertion-annealing engine; return a validated (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=start_graph, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if lib.is_valid(n, e, d, D):
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Arc-extended projective plane graphs (diameter 3, so valid for D >= 3).
    if D >= 3:
        frac = 0.3 if D == 3 else 0.4
        cands = _arc_extensions(d, start + frac * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() - start < 0.7 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D == 3:
        # Bold path: C insertion annealing from the best valid graph.
        # Skip when the Moore bound already matches the current order.
        if lib.moore_bound(d, D) > best_n:
            left = 0.85 * time_limit - (time.monotonic() - start) - 3.0
            if left > 2.0:
                res = _c_repair(d, D, best, left, seed)
                if res is not None:
                    consider(res[0], res[1])
    else:
        # Voltage-lift annealing for D >= 4 (parent behaviour).
        deadline = start + 0.7 * time_limit
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
