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
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# C repair engine: simulated annealing on a degree-bounded bipartite graph.
#
# Starting from a valid graph, it repeatedly adds one vertex (attached to spare
# vertices on the other side) and then anneals edge rewirings that keep the
# bipartition and max degree, minimizing the number of vertex pairs at distance
# more than D. Each time the cost reaches zero the graph is recorded and another
# vertex is added. The best valid graph found is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WD 16
#define MAXM 40000
#define MAXD 64

static int d, D, n, M;
static int eu[MAXM], ev[MAXM];
static int deg[MAXN], side[MAXN];
static unsigned char adjc[MAXN][MAXN];
static int adjl[MAXN][MAXD], adjn[MAXN];
static uint64_t RA[MAXN][WD], RB[MAXN][WD];
static uint64_t rs = 88172645463325252ULL;
static int bestN = -1, bestM = 0;
static int bu[MAXM], bv[MAXM];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void build_adj(void) {
    for (int v = 0; v < n; v++) adjn[v] = 0;
    for (int i = 0; i < M; i++) {
        int a = eu[i], b = ev[i];
        adjl[a][adjn[a]++] = b;
        adjl[b][adjn[b]++] = a;
    }
}

/* Sum over vertices of the number of vertices not within distance D. */
static long eval_cost(void) {
    build_adj();
    int nw = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) RA[v][w] = 0;
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[WD] = RA;
    uint64_t (*nxt)[WD] = RB;
    for (int r = 0; r < D; r++) {
        uint64_t diff = 0;
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < adjn[v]; k++) {
                int u = adjl[v][k];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
            for (int w = 0; w < nw; w++) diff |= nxt[v][w] ^ cur[v][w];
        }
        uint64_t (*t)[WD] = cur;
        cur = nxt;
        nxt = t;
        if (!diff) break;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(cur[v][w]);
        total += n - c;
    }
    return total;
}

static void add_vertex(void) {
    if (n >= MAXN - 2) return;
    int v = n++;
    side[v] = rndint(2);
    deg[v] = 0;
    int tries = 0;
    while (deg[v] < d && tries < 50 * n && M < MAXM) {
        tries++;
        int c = rndint(v);
        if (side[c] == side[v] || deg[c] >= d || adjc[v][c]) continue;
        eu[M] = v;
        ev[M] = c;
        M++;
        adjc[v][c] = adjc[c][v] = 1;
        deg[v]++;
        deg[c]++;
    }
}

static void record(void) {
    bestN = n;
    bestM = M;
    memcpy(bu, eu, sizeof(int) * (size_t)M);
    memcpy(bv, ev, sizeof(int) * (size_t)M);
}

static void print_graph(int nn, int mm, const int *u, const int *v) {
    printf("%d %d\n", nn, mm);
    for (int i = 0; i < mm; i++) printf("%d %d\n", u[i], v[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)(atoll(argv[3]) + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    static int ou[MAXM], ov[MAXM];
    int om = 0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (om < MAXM) {
            ou[om] = a;
            ov[om] = b;
            om++;
        }
    }
    if (n0 == 0) {
        n0 = 2;
        ou[0] = 0;
        ov[0] = 1;
        om = 1;
    }

    int ok = (d >= 1 && d <= MAXD && D >= 1 && n0 >= 1 && n0 <= MAXN - 64);
    if (ok) {
        n = n0;
        M = 0;
        for (int v = 0; v < n; v++) deg[v] = 0;
        for (int i = 0; i < om && ok; i++) {
            int a = ou[i], b = ov[i];
            if (a < 0 || b < 0 || a >= n || b >= n || a == b || adjc[a][b]) {
                ok = 0;
                break;
            }
            adjc[a][b] = adjc[b][a] = 1;
            eu[M] = a;
            ev[M] = b;
            M++;
            deg[a]++;
            deg[b]++;
            if (deg[a] > d || deg[b] > d) ok = 0;
        }
    }
    if (ok) {
        build_adj();
        for (int v = 0; v < n; v++) side[v] = -1;
        static int q[MAXN];
        for (int s = 0; s < n && ok; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int h = 0, t = 0;
            q[t++] = s;
            while (h < t && ok) {
                int u = q[h++];
                for (int k = 0; k < adjn[u]; k++) {
                    int w = adjl[u][k];
                    if (side[w] < 0) {
                        side[w] = 1 - side[u];
                        q[t++] = w;
                    } else if (side[w] == side[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) {
        print_graph(n0, om, ou, ov);
        return 0;
    }

    clock_t t0 = clock();
    long cost = eval_cost();
    if (cost == 0) {
        record();
        add_vertex();
        cost = eval_cost();
    }

    double T0 = 2.0, T = T0;
    long stage = 0;
    while (1) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        stage++;
        if (stage % 40000 == 0) T = T0;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;

        if (rnd01() < 0.1) {
            /* Add a new edge between spare vertices on opposite sides; never raises cost. */
            int a = rndint(n), c = rndint(n);
            if (a != c && side[a] != side[c] && deg[a] < d && deg[c] < d &&
                !adjc[a][c] && M < MAXM) {
                eu[M] = a;
                ev[M] = c;
                M++;
                adjc[a][c] = adjc[c][a] = 1;
                deg[a]++;
                deg[c]++;
                cost = eval_cost();
            }
        } else {
            /* Rewire: edge (keep, y) becomes (keep, c) with c on y's side. */
            if (M == 0) continue;
            int i = rndint(M);
            int keep, y;
            if (rnd() & 1) {
                keep = eu[i];
                y = ev[i];
            } else {
                keep = ev[i];
                y = eu[i];
            }
            int c = -1;
            for (int t = 0; t < 20; t++) {
                int cand = rndint(n);
                if (side[cand] == side[y] && cand != y && deg[cand] < d && !adjc[keep][cand]) {
                    c = cand;
                    break;
                }
            }
            if (c < 0) continue;

            adjc[keep][y] = adjc[y][keep] = 0;
            adjc[keep][c] = adjc[c][keep] = 1;
            deg[y]--;
            deg[c]++;
            if (eu[i] == keep) ev[i] = c;
            else eu[i] = c;

            long nc = eval_cost();
            long delta = nc - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                adjc[keep][c] = adjc[c][keep] = 0;
                adjc[keep][y] = adjc[y][keep] = 1;
                deg[c]--;
                deg[y]++;
                if (eu[i] == keep) ev[i] = y;
                else eu[i] = y;
            }
        }

        if (cost == 0) {
            if (n > bestN) record();
            if (n >= MAXN - 2) break;
            add_vertex();
            cost = eval_cost();
            T = T0;
            stage = 0;
        }
    }

    if (bestN < 0) print_graph(n0, om, ou, ov);
    else print_graph(bestN, bestM, bu, bv);
    return 0;
}
"""


def _c_repair(d, D, seed, graph, budget):
    """Run the C annealer for about `budget` seconds starting from `graph`; return (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=graph, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


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

    # Arc-extended projective plane graphs: diameter 3, valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.35 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing is kept for D >= 4 only; it is time-boxed.
    if D >= 4:
        vdead = start + 0.35 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < vdead:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, vdead, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C repair search: add vertices to the best graph and anneal edge rewirings.
    elapsed = time.monotonic() - start
    budget = 0.9 * time_limit - elapsed - 2.0
    if budget >= 1.0:
        try:
            n_c, e_c = _c_repair(d, D, seed, best, budget)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
