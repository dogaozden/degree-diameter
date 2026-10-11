import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction 1: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so spare s = d - q - 1. Add an A-vertex per point of SA (joined to its q+1
# lines) and a B-vertex per line of SB (joined to its q+1 points), where every
# line carries <= s SA points and every point lies on <= s SB lines.
# ----------------------------------------------------------------------------

_LS_ITERS = 12000


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
    """Randomized greedy load-constrained set."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus new A-vertices (per SA point) and B-vertices (per SB line)."""
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


_LS_ITERS_UNUSED = None


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) arc-extended candidates for each usable prime power q."""
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
        SA = _greedy_side(m, s, point_lines, rng, 30, deadline)
        SB = _greedy_side(m, s, line_points, rng, 30, deadline)
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
# Construction 2 (bold): C simulated annealing that grows the arc graph.
#
# The C engine keeps the bipartition fixed. Moves rewire one edge endpoint or add
# an edge between spare-degree vertices on opposite sides. The cost is the number
# of ordered vertex pairs at distance > D. Whenever cost reaches zero the engine
# saves the graph and adds one new vertex on a random side, joined to spare
# vertices of the other side. Only saved, valid graphs are printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64

static int N, DEG, DIAM;
static int nb[MAXN][MAXD];
static int dg[MAXN];
static int side[MAXN];
static unsigned long long rs = 88172645463325252ULL;
static int bestN;
static int bnb[MAXN][MAXD];
static int bdg[MAXN];
static int mk, ma, mb, mc;

static unsigned rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return (unsigned)(rs >> 11);
}
static int rint_(int k) { return (int)(rnd() % (unsigned)k); }
static double rdbl(void) { return (double)(rnd() & 0xFFFFFF) / 16777216.0; }

static int has_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++) if (nb[a][i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    nb[a][dg[a]++] = b;
    nb[b][dg[b]++] = a;
}
static void del_arc(int a, int b) {
    for (int i = 0; i < dg[a]; i++) {
        if (nb[a][i] == b) { nb[a][i] = nb[a][dg[a] - 1]; dg[a]--; return; }
    }
}
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

static long cost(void) {
    static int dist[MAXN], q[MAXN];
    long bad = 0;
    for (int s = 0; s < N; s++) {
        for (int v = 0; v < N; v++) dist[v] = -1;
        int h = 0, t = 0;
        q[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int u = q[h++];
            if (dist[u] >= DIAM) continue;
            for (int i = 0; i < dg[u]; i++) {
                int v = nb[u][i];
                if (dist[v] < 0) { dist[v] = dist[u] + 1; q[t++] = v; }
            }
        }
        bad += N - t;
    }
    return bad;
}

static int pick_nonisolated(void) {
    for (int t = 0; t < 200; t++) {
        int a = rint_(N);
        if (dg[a] > 0) return a;
    }
    return -1;
}

static int pick_spare_side(int s) {
    for (int t = 0; t < 400; t++) {
        int x = rint_(N);
        if (side[x] == s && dg[x] < DEG) return x;
    }
    return -1;
}

static int move_rewire(void) {
    int a = pick_nonisolated();
    if (a < 0) return 0;
    int b = nb[a][rint_(dg[a])];
    int c = -1;
    for (int t = 0; t < 60; t++) {
        int x = rint_(N);
        if (side[x] == side[b] && dg[x] < DEG && x != b && !has_edge(a, x)) { c = x; break; }
    }
    if (c < 0) return 0;
    del_edge(a, b);
    add_edge(a, c);
    mk = 1; ma = a; mb = b; mc = c;
    return 1;
}

static int move_add(void) {
    int a = pick_spare_side(0);
    int c = pick_spare_side(1);
    if (a < 0 || c < 0 || has_edge(a, c)) return 0;
    add_edge(a, c);
    mk = 2; ma = a; mb = -1; mc = c;
    return 1;
}

static void undo(void) {
    if (mk == 1) { del_edge(ma, mc); add_edge(ma, mb); }
    else if (mk == 2) { del_edge(ma, mc); }
}

static void save(void) {
    bestN = N;
    memcpy(bnb, nb, sizeof nb);
    memcpy(bdg, dg, sizeof dg);
}

static void grow(void) {
    if (N >= MAXN - 1) return;
    int v = N++;
    dg[v] = 0;
    side[v] = (int)(rnd() & 1u);
    static int cand[MAXN];
    int nc = 0;
    for (int x = 0; x < N - 1; x++)
        if (side[x] != side[v] && dg[x] < DEG) cand[nc++] = x;
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int tmp = cand[i]; cand[i] = cand[j]; cand[j] = tmp;
    }
    for (int i = 0; i < nc && dg[v] < DEG; i++) {
        int x = cand[i];
        if (dg[x] < DEG) add_edge(v, x);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    double limit = atof(argv[4]);
    DEG = d;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n <= 0 || n > MAXN / 2 || DEG < 1 || DEG >= MAXD) { printf("0 0\n"); return 0; }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (dg[u] >= DEG || dg[v] >= DEG || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int qq[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    int bip = 1;
    for (int s = 0; s < N && bip; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qq[t++] = s;
        while (h < t && bip) {
            int u = qq[h++];
            for (int i = 0; i < dg[u]; i++) {
                int v = nb[u][i];
                if (side[v] < 0) { side[v] = 1 - side[u]; qq[t++] = v; }
                else if (side[v] == side[u]) bip = 0;
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }

    save();
    long cur = cost();
    if (cur != 0) { printf("%d %d\n", bestN, 0); return 0; }
    grow();
    cur = cost();

    double t0 = 2.0, t1 = 0.08;
    double T = t0;
    clock_t c0 = clock();
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        T = t0 * pow(t1 / t0, frac);
        if (cur == 0) {
            if (N > bestN) save();
            grow();
            cur = cost();
            continue;
        }
        int ok;
        if (rnd() % 10 == 0) ok = move_add();
        else ok = move_rewire();
        if (!ok) continue;
        long c2 = cost();
        long delta = c2 - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) cur = c2;
        else undo();
    }

    long me = 0;
    for (int u = 0; u < bestN; u++) me += bdg[u];
    me /= 2;
    printf("%d %ld\n", bestN, me);
    for (int u = 0; u < bestN; u++)
        for (int i = 0; i < bdg[u]; i++) {
            int v = bnb[u][i];
            if (u < v) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


def _c_grow(start, d, D, seed, budget, timeout):
    """Run the C annealer from `start`; return the (n, edges) it reports."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=start, timeout=timeout)
    return lib.parse_graph_text(text)


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

    if D < 3 or d > 60:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    rng = random.Random(seed * 7919 + d)

    # Stage 1: arc-extended projective plane graphs (quick, always valid).
    try:
        arc_deadline = start + 0.25 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, rng):
            consider(n_c, e_c)
    except Exception:
        pass

    # Stage 2: C annealing that grows the best graph found so far.
    try:
        elapsed = time.monotonic() - start
        budget = 0.6 * time_limit - elapsed - 2.0
        if budget >= 2.0:
            timeout = 0.9 * time_limit - elapsed
            n2, e2 = _c_grow(best, d, D, seed, budget, timeout)
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
