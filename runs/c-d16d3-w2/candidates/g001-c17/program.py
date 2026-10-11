import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: conflict-directed local search on bipartite graphs.
#
# Cost = number of unordered vertex pairs at distance > D (unreachable counts).
# Each step picks a bad pair (u, w) and proposes repairs that aim at it:
#   same side  -> add edge e--x with x a neighbour of the other endpoint
#                 (creates a common neighbour, distance 2);
#   opposite   -> add edge e--x with x a neighbour of a neighbour of the other
#                 endpoint (creates a path of length 3).
# Degree overflow is handled by evicting one random edge at each saturated end.
# Several candidates are scored exactly and the best is accepted by annealing.
# Whenever cost reaches 0 the engine saves the graph and appends one isolated
# vertex on the smaller side. Python re-checks the output with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXN 1600
#define MAXW 25
#define DCAP 64
#define MAXE (MAXN * DCAP)
#define KC 6

typedef struct { int a, b, add; } Op;

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static uint64_t RF[MAXN][MAXW];
static int missing[MAXN];
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0;
static uint64_t rs = 1;
static int vis[MAXN];
static int queue_[MAXN];
static Op ops[4];
static int nops = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

/* Returns number of unordered pairs at distance > D. Also fills RF (reach sets)
   and missing[] (number of vertices not reached from each vertex). */
static int bad_pairs(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        missing[v] = n - c;
        bad += n - c;
        memcpy(RF[v], cur[v], sizeof(uint64_t) * (size_t)W);
    }
    return (int)(bad / 2);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (nb[u][i] > u && m < MAXE) {
                bestU[m] = u; bestV[m] = nb[u][i]; m++;
            }
        }
    }
    best_n = n; best_m = m;
}

static int color_graph(void) {
    int iso = 0;
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        if (deg[s] == 0) { vis[s] = 1; side[s] = (iso++) & 1; continue; }
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; queue_[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

/* Pick a bad pair (*pu, *pw) using the reach data from the last bad_pairs(). */
static int pick_bad(int *pu, int *pw) {
    int v = -1;
    for (int tries = 0; tries < 8 * n; tries++) {
        int c = rint_(n);
        if (missing[c] > 0) { v = c; break; }
    }
    if (v < 0) return 0;
    int s = rint_(n);
    for (int i = 0; i < n; i++) {
        int w = (s + i) % n;
        if (w != v && !((RF[v][w >> 6] >> (w & 63)) & 1ULL)) {
            *pu = v; *pw = w;
            return 1;
        }
    }
    return 0;
}

/* Propose an edge e--x that should help the pair (u, w). */
static int gen_candidate(int u, int w, int *pe, int *px) {
    int e, other;
    if (rint_(2)) { e = u; other = w; } else { e = w; other = u; }
    if (rint_(5) == 0) {
        int c = rint_(n);
        if (c == e || side[c] == side[e]) return 0;
        *pe = e; *px = c;
        return 1;
    }
    if (deg[other] == 0) return 0;
    if (side[other] == side[e]) {
        /* same side: x adjacent to other gives a common neighbour (distance 2) */
        int x = nb[other][rint_(deg[other])];
        *pe = e; *px = x;
        return 1;
    }
    /* opposite sides: e - x - a - other is a path of length 3 */
    int a = nb[other][rint_(deg[other])];
    if (deg[a] == 0) return 0;
    int x = nb[a][rint_(deg[a])];
    *pe = e; *px = x;
    return 1;
}

static void op_add(int a, int b) {
    add_edge(a, b);
    ops[nops].a = a; ops[nops].b = b; ops[nops].add = 1; nops++;
}
static void op_del(int a, int b) {
    del_edge(a, b);
    ops[nops].a = a; ops[nops].b = b; ops[nops].add = 0; nops++;
}

/* Add edge e--x, evicting a random edge at each endpoint that is saturated. */
static int apply_move(int e, int x) {
    nops = 0;
    if (e == x || adjm[e][x] || side[e] == side[x]) return 0;
    if (deg[e] >= d) {
        int y = nb[e][rint_(deg[e])];
        op_del(e, y);
    }
    if (deg[x] >= d) {
        int z = nb[x][rint_(deg[x])];
        op_del(x, z);
    }
    if (deg[e] >= d || deg[x] >= d) {
        /* should not happen; roll back */
        while (nops > 0) {
            nops--;
            Op o = ops[nops];
            if (o.add) del_edge(o.a, o.b); else add_edge(o.a, o.b);
        }
        return 0;
    }
    op_add(e, x);
    return 1;
}

static void undo(void) {
    while (nops > 0) {
        nops--;
        Op o = ops[nops];
        if (o.add) del_edge(o.a, o.b);
        else add_edge(o.a, o.b);
    }
}

static void replay(const Op *o, int k) {
    for (int i = 0; i < k; i++) {
        if (o[i].add) add_edge(o[i].a, o[i].b);
        else del_edge(o[i].a, o[i].b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || n < 0 || m0 < 0) { printf("0 0\n"); return 0; }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) return 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { m0 = i; break; }
    }

    int ok = (n >= 2 && n <= MAXN - 256 && d >= 1 && d <= DCAP && D >= 1);
    if (ok) {
        for (int i = 0; i < m0 && ok; i++) {
            int u = iu[i], v = iv[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
                deg[u] >= d || deg[v] >= d) {
                ok = 0;
            } else {
                add_edge(u, v);
            }
        }
    }
    if (ok) ok = color_graph();
    if (!ok) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }

    int cur_bad = bad_pairs();
    int have_best = 0;
    if (cur_bad == 0) { save_best(); have_best = 1; }

    long it = 0;
    for (;;) {
        if ((it & 15) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur_bad == 0) {
            save_best();
            have_best = 1;
            if (n >= MAXN - 2) break;
            int ca = 0;
            for (int v = 0; v < n; v++) if (side[v] == 0) ca++;
            side[n] = (ca <= n - ca) ? 0 : 1;
            deg[n] = 0;
            n++;
            cur_bad = bad_pairs();
            continue;
        }

        int u = -1, w = -1;
        if (!pick_bad(&u, &w)) { cur_bad = bad_pairs(); continue; }

        double phase = (double)(it % 40000) / 40000.0;
        double T = 0.25 + 1.0 * (1.0 - phase) * (1.0 - phase);

        int bestbad = INT_MAX, bestn = 0, have_c = 0;
        Op bops[4];
        for (int k = 0; k < KC; k++) {
            int e = -1, x = -1;
            if (!gen_candidate(u, w, &e, &x)) continue;
            if (!apply_move(e, x)) continue;
            int tb = bad_pairs();
            Op tops[4];
            int tn = nops;
            memcpy(tops, ops, sizeof(Op) * (size_t)tn);
            undo();
            if (tb < bestbad || (tb == bestbad && rint_(2))) {
                bestbad = tb;
                bestn = tn;
                memcpy(bops, tops, sizeof(Op) * (size_t)tn);
                have_c = 1;
            }
        }
        if (have_c) {
            int delta = bestbad - cur_bad;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                replay(bops, bestn);
            }
        }
        cur_bad = bad_pairs();
    }

    if (!have_best) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. With d >= q+1 each vertex has spare capacity
# s = d - q - 1. Add point-like vertices (pencils) and line-like vertices
# (point sets on a line). Each line may take at most s new neighbours and each
# point at most s, so the chosen set S must be a (k, s)-arc-like set.
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
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # New construction path for D = 3: conflict-directed local search that
    # grows the order from the best arc-extended graph. The start graph gets one
    # extra isolated vertex; the engine repairs it and keeps adding vertices.
    if D == 3:
        bound = lib.moore_bound(d, D)
        cbudget = end - time.monotonic()
        if best[0] < bound and cbudget > 3.0:
            try:
                start_graph = (best[0] + 1, list(best[1]))
                out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget - 1.5, 2)],
                                stdin_graph=start_graph, timeout=cbudget + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    # Voltage-lift annealing for D >= 4 (unchanged from parent).
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
