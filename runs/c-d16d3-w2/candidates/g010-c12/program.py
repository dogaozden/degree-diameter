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
#
# For d = 16 and q = 13 (s = 2) the constraint says SA and SB are arcs, so the
# best choice is a conic plus, for even q, a nucleus. That gives 2*183 + 2*14 = 394.
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 5).
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
# C engine: grow-and-repair annealing.
#
# State: a bipartite graph with max degree d, diameter-D validity measured as the
# number of unordered vertex pairs farther than D apart (bitset BFS).
# Loop: append one vertex on a random side, then anneal with moves
#   add edge (biased toward the new vertex), double-edge switch (keeps degrees),
#   remove edge. On cost 0 the grown graph becomes the new best; otherwise
#   the state reverts to the best.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define ATT_ITERS 6000

static int N, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];

static int bN;
static int bdeg[MAXN];
static int badj[MAXN][MAXD];
static int bside[MAXN];

static double deadline_s;
static uint64_t rng_s = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rng_s ^= rng_s >> 12;
    rng_s ^= rng_s << 25;
    rng_s ^= rng_s >> 27;
    return rng_s * 2685821657736338717ULL;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost(void) {
    int nw = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * nw);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * nw);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[adj[v][i]];
                for (int w = 0; w < nw; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int is_adj(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}
static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}
static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}
static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

typedef struct {
    int nrem, nadd;
    int rem[2][2];
    int add[2][2];
} Move;

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nrem; i++) del_edge(m->rem[i][0], m->rem[i][1]);
    for (int i = 0; i < m->nadd; i++) add_edge(m->add[i][0], m->add[i][1]);
}
static void undo_move(const Move *m) {
    for (int i = 0; i < m->nadd; i++) del_edge(m->add[i][0], m->add[i][1]);
    for (int i = 0; i < m->nrem; i++) add_edge(m->rem[i][0], m->rem[i][1]);
}

static int try_add(int focus, Move *mv) {
    int u = -1;
    if (focus >= 0 && deg[focus] < d && rnd01() < 0.5) {
        u = focus;
    } else {
        for (int t = 0; t < 20 && u < 0; t++) {
            int x = rndint(N);
            if (deg[x] < d) u = x;
        }
    }
    if (u < 0) return 0;
    for (int t = 0; t < 60; t++) {
        int v = rndint(N);
        if (v == u || side[v] == side[u] || deg[v] >= d || is_adj(u, v)) continue;
        mv->nrem = 0;
        mv->nadd = 1;
        mv->add[0][0] = u;
        mv->add[0][1] = v;
        return 1;
    }
    return 0;
}

static int try_switch(Move *mv) {
    int a = rndint(N);
    if (deg[a] == 0) return 0;
    int b = adj[a][rndint(deg[a])];
    int c = rndint(N);
    if (c == a || side[c] != side[a] || deg[c] == 0) return 0;
    int e = adj[c][rndint(deg[c])];
    if (e == b || is_adj(a, e) || is_adj(c, b)) return 0;
    mv->nrem = 2;
    mv->rem[0][0] = a; mv->rem[0][1] = b;
    mv->rem[1][0] = c; mv->rem[1][1] = e;
    mv->nadd = 2;
    mv->add[0][0] = a; mv->add[0][1] = e;
    mv->add[1][0] = c; mv->add[1][1] = b;
    return 1;
}

static int try_remove(Move *mv) {
    int a = rndint(N);
    if (deg[a] == 0) return 0;
    int b = adj[a][rndint(deg[a])];
    mv->nrem = 1;
    mv->rem[0][0] = a; mv->rem[0][1] = b;
    mv->nadd = 0;
    return 1;
}

static int anneal(int focus, int iters) {
    long long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && now_s() > deadline_s) break;
        double frac = (double)it / (double)iters;
        double T = 0.6 * (1.0 - frac) + 0.05;
        Move mv;
        int ok;
        double r = rnd01();
        if (r < 0.5) ok = try_add(focus, &mv);
        else if (r < 0.93) ok = try_switch(&mv);
        else ok = try_remove(&mv);
        if (!ok) continue;
        apply_move(&mv);
        long long c2 = cost();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            undo_move(&mv);
        }
    }
    return cur == 0;
}

static void save_best(void) {
    bN = N;
    memcpy(bdeg, deg, sizeof deg);
    memcpy(badj, adj, sizeof adj);
    memcpy(bside, side, sizeof side);
}
static void restore_best(void) {
    N = bN;
    memcpy(deg, bdeg, sizeof deg);
    memcpy(adj, badj, sizeof adj);
    memcpy(side, bside, sizeof side);
}

static void emit(void) {
    long long M = 0;
    for (int v = 0; v < bN; v++)
        for (int i = 0; i < bdeg[v]; i++)
            if (badj[v][i] > v) M++;
    printf("%d %lld\n", bN, M);
    for (int v = 0; v < bN; v++)
        for (int i = 0; i < bdeg[v]; i++) {
            int u = badj[v][i];
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rng_s ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rng_s == 0) rng_s = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int n, m;
    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 64) { printf("0 0\n"); return 0; }
    N = n;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || is_adj(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adj[x][i];
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    queue[qt++] = y;
                }
            }
        }
    }
    int bip = 1;
    for (int v = 0; v < N && bip; v++)
        for (int i = 0; i < deg[v]; i++)
            if (side[adj[v][i]] == side[v]) { bip = 0; break; }

    save_best();
    if (!bip || cost() != 0) {
        emit();
        return 0;
    }

    deadline_s = budget;
    while (now_s() < deadline_s && bN < MAXN - 2) {
        restore_best();
        int X = rndint(2);
        int nv = N;
        N++;
        side[nv] = X;
        deg[nv] = 0;
        if (anneal(nv, ATT_ITERS)) save_best();
    }
    emit();
    return 0;
}
'''


def _search_c(d, D, seed, budget, start_graph):
    """Run the C grow-and-repair search from a valid start graph; return (n, edges) or None."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=start_graph, timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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
    if D >= 3 and time.monotonic() < start + 0.3 * T:
        cands = _arc_extensions(d, start + 0.3 * T, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.3 * T:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing, mainly useful for D >= 5.
    if D >= 5:
        ks = [1, 2, 2, 3, 4]
        anneal_deadline = start + 0.4 * T
        while time.monotonic() < anneal_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Grow-and-repair C search from the best valid graph.
    # Skip it when the Moore bound is already reached (e.g. calibration cases).
    if best_n < lib.moore_bound(d, D):
        c_deadline = start + 0.85 * T
        c_budget = c_deadline - time.monotonic() - 1.0
        if c_budget >= 1.0:
            try:
                consider(*_search_c(d, D, seed, c_budget, best))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
