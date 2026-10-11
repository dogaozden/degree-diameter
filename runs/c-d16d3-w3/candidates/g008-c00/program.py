import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. An A-side set SA of points gets
# one new vertex each (joined to the q+1 lines through it); every line may hold
# at most s points of SA. A B-side set SB of lines is symmetric.
# Order is 2(q^2+q+1) + |SA| + |SB|. Diameter stays 3.
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
# Simulated annealing over bi-Cayley voltage lifts (kept for D >= 4).
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
# New construction: unstructured graph search in C, started from the best known
# graph. The engine keeps a bipartite graph with max degree d and simulated
# annealing over degree-preserving edge swaps, endpoint moves and edge additions.
# The cost is the number of vertex pairs at distance > D. When the cost reaches
# zero, the engine saves the graph and inserts a new vertex on the side that
# gets the greedily best neighbours. After a long stall it restores the best
# saved graph and retries the insertion. Output is always re-checked in Python.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WMAX 16
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)
#define STALL 15000

static int N, DEG, DIAM, W;
static int col[MAXN], deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char M[MAXN][MAXN];
static uint64_t RA[MAXN][WMAX], RB[MAXN][WMAX];

static int bestN = 0, bestM = 0;
static int bestCol[MAXN];
static int bestEu[MAXE], bestEv[MAXE];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM (0 means valid diameter). */
static long long bad_pairs(void) {
    int v, r, k, w;
    W = (N + 63) / 64;
    for (v = 0; v < N; v++) {
        for (w = 0; w < W; w++) RA[v][w] = 0;
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            for (w = 0; w < W; w++) RB[v][w] = RA[v][w];
            for (k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (w = 0; w < W; w++) RB[v][w] |= RA[u][w];
            }
        }
        for (v = 0; v < N; v++)
            for (w = 0; w < W; w++)
                RA[v][w] = RB[v][w];
    }
    long long reach = 0;
    for (v = 0; v < N; v++)
        for (w = 0; w < W; w++)
            reach += pc64(RA[v][w]);
    return ((long long)N * N - reach) / 2;
}

static void add_edge(int a, int b) {
    M[a][b] = 1; M[b][a] = 1;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_from(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    M[a][b] = 0; M[b][a] = 0;
    del_from(a, b);
    del_from(b, a);
}

static int color_graph(void) {
    int s, i, k, h, t;
    static int q[MAXN];
    for (i = 0; i < N; i++) col[i] = -1;
    for (s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0; h = 0; t = 0; q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] < 0) { col[v] = 1 - col[u]; q[t++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    return 1;
}

static void save_best(void) {
    int a, k;
    bestN = N; bestM = 0;
    for (a = 0; a < N; a++) {
        bestCol[a] = col[a];
        for (k = 0; k < deg[a]; k++) {
            int b = adj[a][k];
            if (a < b && bestM < MAXE) {
                bestEu[bestM] = a; bestEv[bestM] = b; bestM++;
            }
        }
    }
}

static void restore_best(void) {
    int a, i;
    int oldN = N;
    for (a = 0; a < oldN; a++) {
        memset(M[a], 0, (size_t)oldN);
        deg[a] = 0;
    }
    N = bestN;
    for (a = 0; a < N; a++) col[a] = bestCol[a];
    for (i = 0; i < bestM; i++) add_edge(bestEu[i], bestEv[i]);
}

/* Add a vertex of random side, joined greedily (by cost) to up to DEG spare opposite vertices. */
static void insert_vertex(void) {
    int x = N, c, k, i, tr;
    static int cand[MAXN];
    c = rndi(2);
    N++;
    col[x] = c; deg[x] = 0;
    for (i = 0; i < N; i++) { M[x][i] = 0; M[i][x] = 0; }
    for (k = 0; k < DEG; k++) {
        int nc = 0, bestc = -1;
        long long bestv = (1LL << 60);
        int trials;
        for (i = 0; i < x; i++)
            if (col[i] != c && deg[i] < DEG && !M[x][i]) cand[nc++] = i;
        if (nc == 0) break;
        trials = nc < 40 ? nc : 40;
        for (tr = 0; tr < trials; tr++) {
            int pick = (nc <= 40) ? tr : rndi(nc);
            int y = cand[pick];
            long long v;
            add_edge(x, y);
            v = bad_pairs();
            del_edge(x, y);
            if (v < bestv || (v == bestv && rndi(2))) { bestv = v; bestc = y; }
        }
        add_edge(x, bestc);
    }
}

int main(int argc, char **argv) {
    int n, m, i;
    double tl;
    clock_t t0;
    long long cur, minSince, stall = 0, it = 0;
    const double T = 0.5;

    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    tl = atof(argv[4]);

    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 4 || m < 0 ||
        DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || M[u][v] ||
            deg[u] >= DEG || deg[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    if (!color_graph()) { printf("0 0\n"); return 0; }
    cur = bad_pairs();
    if (cur != 0) { printf("0 0\n"); return 0; }
    save_best();

    minSince = cur;
    t0 = clock();
    for (;;) {
        if ((it & 63) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC >= tl) break;
        it++;
        {
            int type = rndi(10);
            if (type < 4) {
                /* degree-preserving swap of two edges on the same side */
                int a = rndi(N), b, c, e;
                long long c2;
                if (!deg[a]) continue;
                b = adj[a][rndi(deg[a])];
                c = rndi(N);
                if (c == a || col[c] != col[a] || !deg[c]) continue;
                e = adj[c][rndi(deg[c])];
                if (e == b || M[a][e] || M[c][b]) continue;
                del_edge(a, b); del_edge(c, e);
                add_edge(a, e); add_edge(c, b);
                c2 = bad_pairs();
                if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) cur = c2;
                else {
                    del_edge(a, e); del_edge(c, b);
                    add_edge(a, b); add_edge(c, e);
                }
            } else if (type < 7) {
                /* move one endpoint of an edge to a spare vertex on the same side */
                int a = rndi(N), b, e;
                long long c2;
                if (!deg[a]) continue;
                b = adj[a][rndi(deg[a])];
                e = rndi(N);
                if (e == b || col[e] != col[b] || deg[e] >= DEG || M[a][e]) continue;
                del_edge(a, b); add_edge(a, e);
                c2 = bad_pairs();
                if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) cur = c2;
                else { del_edge(a, e); add_edge(a, b); }
            } else {
                /* add an edge between spare vertices (never increases cost) */
                int a = rndi(N), e = rndi(N);
                long long c2;
                if (a == e || col[a] == col[e] || M[a][e] || deg[a] >= DEG || deg[e] >= DEG) continue;
                add_edge(a, e);
                c2 = bad_pairs();
                if (c2 > cur) del_edge(a, e);
                else cur = c2;
            }
        }

        if (cur == 0) {
            if (N > bestN) save_best();
            if (N >= MAXN - 2) break;
            insert_vertex();
            cur = bad_pairs();
            minSince = cur;
            stall = 0;
            continue;
        }
        if (cur < minSince) {
            minSince = cur;
            stall = 0;
        } else if (++stall > STALL) {
            restore_best();
            if (N >= MAXN - 2) break;
            insert_vertex();
            cur = bad_pairs();
            minSince = cur;
            stall = 0;
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (i = 0; i < bestM; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
'''


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t0 + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing, only for D >= 4 and only in the first part of the budget.
    if D >= 4:
        volt_deadline = t0 + 0.35 * time_limit
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < volt_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, volt_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # New construction: C graph-growth search started from the best graph so far.
    # Skip it when the graph already meets the Moore bound (it cannot grow).
    if D >= 3 and d <= 40 and best_n < lib.moore_bound(d, D):
        remaining = time_limit - (time.monotonic() - t0)
        budget = remaining * 0.7 - 1.0
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=remaining * 0.9)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
