"""Arc-extended projective-plane graphs repaired by a C annealer that grows vertices.

Pipeline:
1. Python builds arc-extended PG(2, q) graphs (D = 3 construction) for each prime power q <= d-1.
   For D >= 4 it also tries W(q) and group voltage lifts.
2. The best valid graph is passed to a C engine. The engine splits an edge to insert a new
   vertex on one side, then anneals with edge-add, double-edge-swap and edge-remove moves,
   minimising the number of vertex pairs at distance > D. Every zero-cost state is snapshotted.
3. Fallbacks: K_{d,d} (valid for D >= 2). Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64

static int d_, D_, cap, W, n;
static int *deg, *side, *adj;
static uint64_t *bufA, *bufB;
static uint64_t rs;
static int *snapU, *snapV, *snapSide;
static int snapN = -1, snapM = 0;

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a * MAXD + i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a * MAXD + deg[a]++] = b;
    adj[b * MAXD + deg[b]++] = a;
}

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * MAXD + i] == b) {
            adj[a * MAXD + i] = adj[a * MAXD + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

/* Number of unordered pairs at distance > D_ (unreached pairs included). */
static long long cost_bad(void) {
    int wn = (n + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < wn; w++) cur[(size_t)v * W + w] = 0;
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D_; step++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            for (int w = 0; w < wn; w++) o[w] = c[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *c2 = cur + (size_t)adj[v * MAXD + i] * W;
                for (int w = 0; w < wn; w++) o[w] |= c2[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < wn; w++) pc += __builtin_popcountll(c[w]);
        bad += n - pc;
    }
    return bad / 2;
}

static void save_snapshot(void) {
    snapN = n;
    snapM = 0;
    for (int v = 0; v < n; v++) snapSide[v] = side[v];
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * MAXD + i];
            if (u > v && snapM < cap * MAXD) {
                snapU[snapM] = v;
                snapV[snapM] = u;
                snapM++;
            }
        }
    }
}

static void restore_snapshot(void) {
    n = snapN;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        side[v] = snapSide[v];
    }
    for (int i = 0; i < snapM; i++) add_edge(snapU[i], snapV[i]);
}

static int pick_side(int s) {
    for (int t = 0; t < 100; t++) {
        int v = rndint(n);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* New vertex z on a random side; each attachment either uses spare degree at x or
   splits an edge (x,y): drop (x,y), add (x,z), which frees a slot at y. */
static void insert_vertex(void) {
    int z = n++;
    deg[z] = 0;
    side[z] = rndint(2);
    int tries = 0;
    while (deg[z] < d_ && tries < 2000) {
        tries++;
        int x = rndint(n - 1);
        if (side[x] == side[z] || has_edge(x, z)) continue;
        if (deg[x] < d_) {
            add_edge(x, z);
            continue;
        }
        int y = adj[x * MAXD + rndint(deg[x])];
        del_edge(x, y);
        add_edge(x, z);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    double t0 = now_s();
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x12345677ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    if (d_ > MAXD) d_ = MAXD;
    if (d_ < 2 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) {
        nin = 0;
        min_ = 0;
    }
    if (nin < 0) nin = 0;
    if (min_ < 0) min_ = 0;
    int *eu = malloc(sizeof(int) * (size_t)(min_ + 1));
    int *ev = malloc(sizeof(int) * (size_t)(min_ + 1));
    int ne = 0;
    for (int i = 0; i < min_; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nin || v >= nin || u == v) continue;
        eu[ne] = u;
        ev[ne] = v;
        ne++;
    }
    if (nin < 2) nin = 2;
    int extra = nin / 2 > 700 ? nin / 2 : 700;
    cap = nin + extra;
    W = (cap + 63) / 64;
    deg = calloc((size_t)cap, sizeof(int));
    side = calloc((size_t)cap, sizeof(int));
    adj = calloc((size_t)cap * MAXD, sizeof(int));
    bufA = calloc((size_t)cap * W, sizeof(uint64_t));
    bufB = calloc((size_t)cap * W, sizeof(uint64_t));
    snapU = calloc((size_t)cap * MAXD, sizeof(int));
    snapV = calloc((size_t)cap * MAXD, sizeof(int));
    snapSide = calloc((size_t)cap, sizeof(int));

    /* 2-colour the input graph by BFS over a CSR copy of its edges. */
    int *start = calloc((size_t)nin + 1, sizeof(int));
    for (int i = 0; i < ne; i++) {
        start[eu[i] + 1]++;
        start[ev[i] + 1]++;
    }
    for (int v = 0; v < nin; v++) start[v + 1] += start[v];
    int *fillp = malloc(sizeof(int) * (size_t)(nin + 1));
    for (int v = 0; v <= nin; v++) fillp[v] = start[v];
    int *csr = malloc(sizeof(int) * (size_t)(2 * ne + 1));
    for (int i = 0; i < ne; i++) {
        csr[fillp[eu[i]]++] = ev[i];
        csr[fillp[ev[i]]++] = eu[i];
    }
    int *col = malloc(sizeof(int) * (size_t)nin);
    int *queue = malloc(sizeof(int) * (size_t)nin);
    for (int v = 0; v < nin; v++) col[v] = -1;
    for (int s = 0; s < nin; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = start[u]; k < start[u + 1]; k++) {
                int w = csr[k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    queue[qt++] = w;
                }
            }
        }
    }

    n = nin;
    for (int v = 0; v < n; v++) {
        side[v] = col[v];
        deg[v] = 0;
    }
    int added = 0;
    for (int i = 0; i < ne; i++) {
        int u = eu[i], v = ev[i];
        if (side[u] == side[v]) continue;
        if (has_edge(u, v)) continue;
        if (deg[u] >= d_ || deg[v] >= d_) continue;
        add_edge(u, v);
        added++;
    }
    if (added == 0) {
        for (int v = 0; v < n; v++) {
            side[v] = v & 1;
            deg[v] = 0;
        }
        add_edge(0, 1);
    }

    long long cost = cost_bad();
    if (cost == 0) save_snapshot();
    double T = 2.0;
    long long bestc = cost, stall = 0, it = 0;
    const long long STALL = 60000;

    while (1) {
        if ((it & 63) == 0 && now_s() - t0 > tl) break;
        it++;

        if (cost == 0) {
            if (n > snapN) save_snapshot();
            if (n >= cap - 2) break;
            insert_vertex();
            cost = cost_bad();
            bestc = cost;
            stall = 0;
            T = 2.0;
            continue;
        }
        if (snapN >= 0 && stall > STALL) {
            restore_snapshot();
            cost = cost_bad();
            bestc = cost;
            stall = 0;
            T = 2.0;
            continue;
        }

        int mv = rndint(100);
        if (mv < 45) {
            int u = rndint(n), v = rndint(n);
            if (u != v && side[u] != side[v] && deg[u] < d_ && deg[v] < d_ && !has_edge(u, v)) {
                add_edge(u, v);
                cost = cost_bad();   /* adding an edge never increases the cost */
            }
        } else if (mv < 90) {
            int a1 = pick_side(0), a2 = pick_side(0);
            if (a1 >= 0 && a2 >= 0 && a1 != a2) {
                int b1 = adj[a1 * MAXD + rndint(deg[a1])];
                int b2 = adj[a2 * MAXD + rndint(deg[a2])];
                if (b1 != b2 && !has_edge(a1, b2) && !has_edge(a2, b1)) {
                    del_edge(a1, b1);
                    del_edge(a2, b2);
                    add_edge(a1, b2);
                    add_edge(a2, b1);
                    long long nc = cost_bad();
                    if (accept(nc - cost, T)) {
                        cost = nc;
                    } else {
                        del_edge(a1, b2);
                        del_edge(a2, b1);
                        add_edge(a1, b1);
                        add_edge(a2, b2);
                    }
                }
            }
        } else {
            int a = pick_side(0);
            if (a >= 0) {
                int b = adj[a * MAXD + rndint(deg[a])];
                del_edge(a, b);
                long long nc = cost_bad();
                if (accept(nc - cost, T)) cost = nc;
                else add_edge(a, b);
            }
        }

        T = T > 0.3 ? T * 0.99997 : 0.3;
        if (cost < bestc) {
            bestc = cost;
            stall = 0;
        } else {
            stall++;
        }
    }

    if (snapN < 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a multiset SA of points (repeats allowed). Each entry P gets a new
#         vertex joined to all q+1 lines through P. Constraint: every line
#         holds <= s entries of SA.
# B-side: a multiset SB of lines. Each entry j gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s entries of SB.
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
    """Iterated greedy over multisets with perturbation; returns the largest multiset seen."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    margin = max(4.0, 0.1 * time_limit)
    c_end = start + time_limit - margin

    # Construction phase: arc-extended PG graphs (D >= 3), W(q) (D >= 4).
    if D >= 3:
        try:
            cands = _arc_extensions(d, start + 0.3 * time_limit, random.Random(seed * 7919 + d))
            for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
                consider(n_c, e_c)
        except Exception:
            pass

    if D >= 4 and time.monotonic() < start + 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Group voltage lifts for D != 3 (parent behaviour).
    if D != 3:
        deadline = start + 0.4 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        try:
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
        except Exception:
            pass

    # Growth phase: C engine inserts vertices and repairs from the best valid graph.
    remaining = c_end - time.monotonic()
    if remaining > 1.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 30.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
