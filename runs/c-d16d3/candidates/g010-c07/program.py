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
# Python simulated annealing over bi-Cayley voltage lifts (small d only).
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
# NEW: C engine for vertex insertion with bitset-based diameter repair.
#
# Start from a valid bipartite graph. Keep a side label per vertex. Grow by
# inserting a new vertex joined to spare opposite-side vertices (best of 3
# random attachments), then anneal with edge moves (endpoint move, add, remove)
# whose cost is the number of vertex pairs at distance > D. Moves focus on
# vertices that still have bad pairs. When cost reaches zero the graph is saved
# and grown again. After a stall the search restarts from the best saved graph.
# All distances are computed with 64-bit bitsets over D rounds of neighbourhood
# unions.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define DMAX 64
#define MAXW 18
#define STALL 30000

typedef uint64_t u64;

static int N, DEGCAP, DIAM, W;
static int side[MAXN], deg[MAXN], adj[MAXN][DMAX];
static u64 RA[MAXN][MAXW], RB[MAXN][MAXW];
static int badv[MAXN], badlist[MAXN], nbad;

static int bestN = -1;
static int bestSide[MAXN], bestDeg[MAXN], bestAdj[MAXN][DMAX];

static u64 rs = 88172645463325252ULL;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (u64)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int pop64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIAM. Also fills badv / badlist. */
static int bad_count(void) {
    int i, k, w, it, total = 0;
    u64 (*cur)[MAXW] = RA;
    u64 (*nxt)[MAXW] = RB;
    u64 (*tmp)[MAXW];
    W = (N + 63) / 64;
    for (i = 0; i < N; i++) {
        for (w = 0; w < W; w++) cur[i][w] = 0;
        cur[i][i >> 6] |= (1ULL << (i & 63));
    }
    for (it = 0; it < DIAM; it++) {
        for (i = 0; i < N; i++) {
            for (w = 0; w < W; w++) nxt[i][w] = cur[i][w];
            for (k = 0; k < deg[i]; k++) {
                const u64 *src = cur[adj[i][k]];
                for (w = 0; w < W; w++) nxt[i][w] |= src[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    nbad = 0;
    for (i = 0; i < N; i++) {
        int c = 0;
        for (w = 0; w < W; w++) c += pop64(cur[i][w]);
        badv[i] = N - c;
        total += N - c;
        if (badv[i] > 0) badlist[nbad++] = i;
    }
    return total / 2;
}

static int has_edge(int u, int v) {
    int k;
    for (k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void raw_add(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void raw_del1(int u, int v) {
    int k;
    for (k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void raw_del(int u, int v) {
    raw_del1(u, v);
    raw_del1(v, u);
}

typedef struct { int type, a, b, c; } Move;
/* type 1: remove a-b, add a-c. type 2: add a-c. type 3: remove a-b. */

static void apply_move(const Move *m) {
    if (m->type == 1) { raw_del(m->a, m->b); raw_add(m->a, m->c); }
    else if (m->type == 2) { raw_add(m->a, m->c); }
    else if (m->type == 3) { raw_del(m->a, m->b); }
}

static void undo_move(const Move *m) {
    if (m->type == 1) { raw_del(m->a, m->c); raw_add(m->a, m->b); }
    else if (m->type == 2) { raw_del(m->a, m->c); }
    else if (m->type == 3) { raw_add(m->a, m->b); }
}

static int pick_vertex(int focused) {
    if (focused && nbad > 0) return badlist[rndint(nbad)];
    return rndint(N);
}

static int propose(Move *m) {
    int focused = rnd01() < 0.6;
    double r = rnd01();
    int a, b = -1, c = -1, t;
    if (N < 2) return 0;
    a = pick_vertex(focused);
    if (r < 0.12) {
        if (deg[a] == 0) return 0;
        m->type = 3;
        m->a = a;
        m->b = adj[a][rndint(deg[a])];
        return 1;
    }
    if (r < 0.6 && deg[a] > 0) b = adj[a][rndint(deg[a])];
    for (t = 0; t < 60; t++) {
        int cc = rndint(N);
        if (cc == a || cc == b || side[cc] == side[a]) continue;
        if (deg[cc] >= DEGCAP || has_edge(a, cc)) continue;
        c = cc;
        break;
    }
    if (c < 0) return 0;
    if (b >= 0) {
        m->type = 1; m->a = a; m->b = b; m->c = c;
        return 1;
    }
    if (deg[a] >= DEGCAP) return 0;
    m->type = 2; m->a = a; m->c = c;
    return 1;
}

/* Insert a new vertex on a random side, joined to up to DEGCAP spare opposite vertices. */
static int grow(void) {
    int cnt[2] = {0, 0}, i, t, ns, v, k, nc, bestc = 1 << 30, bestk = 0;
    int cand[MAXN], bestset[DMAX];
    if (N >= MAXN - 2) return 0;
    for (i = 0; i < N; i++)
        if (deg[i] < DEGCAP) cnt[side[i]]++;
    if (cnt[0] == 0 && cnt[1] == 0) return 0;
    ns = rndint(2);
    if (cnt[1 - ns] == 0) ns = 1 - ns;
    v = N++;
    side[v] = ns;
    deg[v] = 0;
    for (t = 0; t < 3; t++) {
        int c;
        nc = 0;
        for (i = 0; i < v; i++)
            if (side[i] != ns && deg[i] < DEGCAP) cand[nc++] = i;
        k = nc < DEGCAP ? nc : DEGCAP;
        for (i = 0; i < k; i++) {
            int j = i + rndint(nc - i);
            int tmp = cand[i];
            cand[i] = cand[j];
            cand[j] = tmp;
        }
        for (i = 0; i < k; i++) raw_add(v, cand[i]);
        c = bad_count();
        if (c < bestc) {
            bestc = c;
            bestk = k;
            memcpy(bestset, cand, sizeof(int) * (size_t)k);
        }
        for (i = 0; i < k; i++) raw_del(v, cand[i]);
    }
    for (i = 0; i < bestk; i++) raw_add(v, bestset[i]);
    return 1;
}

static void save_best(void) {
    int i;
    bestN = N;
    for (i = 0; i < N; i++) {
        bestSide[i] = side[i];
        bestDeg[i] = deg[i];
        memcpy(bestAdj[i], adj[i], sizeof(int) * (size_t)deg[i]);
    }
}

static void load_best(void) {
    int i;
    N = bestN;
    for (i = 0; i < N; i++) {
        side[i] = bestSide[i];
        deg[i] = bestDeg[i];
        memcpy(adj[i], bestAdj[i], sizeof(int) * (size_t)deg[i]);
    }
}

static void print_best(void) {
    int i, k, m = 0;
    if (bestN < 0) {
        printf("0 0\n");
        return;
    }
    for (i = 0; i < bestN; i++) m += bestDeg[i];
    m /= 2;
    printf("%d %d\n", bestN, m);
    for (i = 0; i < bestN; i++)
        for (k = 0; k < bestDeg[i]; k++)
            if (i < bestAdj[i][k])
                printf("%d %d\n", i, bestAdj[i][k]);
}

int main(int argc, char **argv) {
    int d, n0, m0, i, ok = 1;
    double limit;
    unsigned long seed;
    clock_t t0 = clock();
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    seed = strtoul(argv[3], NULL, 10);
    limit = atof(argv[4]);
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (i = 0; i < 10; i++) rnd64();

    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d < 1 || d > DMAX || DIAM < 0 || n0 < 0 || n0 > MAXN - 200 || m0 < 0) ok = 0;
    if (ok) {
        N = n0;
        DEGCAP = d;
        for (i = 0; i < n0; i++) { deg[i] = 0; side[i] = -1; }
        for (i = 0; i < m0 && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) { ok = 0; break; }
            raw_add(u, v);
        }
    }
    if (ok) {
        int *q = (int *)malloc(sizeof(int) * (size_t)(n0 + 1));
        int s, head, tail;
        for (s = 0; s < n0 && ok; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            head = 0;
            tail = 0;
            q[tail++] = s;
            while (head < tail && ok) {
                int x = q[head++], k;
                for (k = 0; k < deg[x]; k++) {
                    int y = adj[x][k];
                    if (side[y] < 0) {
                        side[y] = 1 - side[x];
                        q[tail++] = y;
                    } else if (side[y] == side[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        free(q);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    if (N == 0) {
        printf("0 0\n");
        return 0;
    }

    {
        int cost = bad_count();
        double T0 = 1.0, Tmin = 0.25, T = T0;
        long iter = 0, stall = 0;
        if (cost == 0) save_best();
        for (;;) {
            if ((iter & 15) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > limit) break;
            iter++;
            if (cost == 0) {
                if (N > bestN) save_best();
                if (!grow()) break;
                cost = bad_count();
                T = T0;
                stall = 0;
                continue;
            }
            {
                Move mv;
                stall++;
                if (propose(&mv)) {
                    int nc, delta;
                    apply_move(&mv);
                    nc = bad_count();
                    delta = nc - cost;
                    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = nc;
                    else undo_move(&mv);
                }
            }
            T *= 0.9995;
            if (T < Tmin) T = Tmin;
            if (stall > STALL) {
                if (bestN >= 0) load_best();
                cost = bad_count();
                T = T0;
                stall = 0;
            }
        }
    }
    print_best();
    return 0;
}
"""


def _c_refine(d, D, seed, graph, budget):
    """Run the C insertion-annealing engine from graph for about budget seconds; return (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(budget, 2)],
                        stdin_graph=graph, timeout=budget + 6.0)
        return lib.parse_graph_text(out)
    except Exception:
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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    # Generalized quadrangle baseline (diameter 4).
    if D >= 4 and time.monotonic() < start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Small d: annealed group voltage lifts (these give the small-degree records).
    if d <= 8:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        deadline = start + 0.3 * time_limit
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

    # NEW: C insertion-annealing refinement from the best graph found so far.
    elapsed = time.monotonic() - start
    budget = 0.80 * time_limit - elapsed - 1.0
    if D >= 2 and best_n >= 2 and budget > 1.0:
        res = _c_refine(d, D, seed, best, budget)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
