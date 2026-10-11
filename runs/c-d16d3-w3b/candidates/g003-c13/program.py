import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing that adds one vertex at a time.
#
# State: a valid bipartite graph with max degree d and diameter <= D. A new
# vertex is attached to spare-degree vertices on the opposite side, then
# annealing rewires or adds edges (only across the two sides, so the graph stays
# bipartite and degrees stay <= d) to minimise the number of vertex pairs at
# distance > D. Cost 0 means valid, and the vertex count grows by one.
# Distances are computed with bitsets: ball_k(v) = OR of ball_{k-1}(u) over u in N[v].
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG)

static int n_ = 0, W_ = 0, D_ = 3, dEff = 3;
static int nb[MAXN][MAXDEG];
static int deg[MAXN];
static int side[MAXN];
static uint64_t adjB[MAXN][MAXW];
static uint64_t BUF1[MAXN][MAXW], BUF2[MAXN][MAXW];
static int L0[MAXN], L1[MAXN], nL0 = 0, nL1 = 0;
static uint64_t rs = 88172645463325252ULL;
static int BEU[MAXE], BEV[MAXE], bestN = 0, bestM = 0;
static int IEU[MAXE], IEV[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double clk(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) { return (int)((adjB[u][v >> 6] >> (v & 63)) & 1ULL); }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjB[u][v >> 6] |= 1ULL << (v & 63);
    adjB[v][u >> 6] |= 1ULL << (u & 63);
}

static void del_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][--deg[u]];
            break;
        }
    }
    adjB[u][v >> 6] &= ~(1ULL << (v & 63));
}

static void del_edge(int u, int v) {
    del_from(u, v);
    del_from(v, u);
}

static void clear_state(int n) {
    n_ = n;
    W_ = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        memset(adjB[v], 0, sizeof(adjB[v]));
    }
}

static int load_edges(int n, int m, const int *eu, const int *ev) {
    clear_state(n);
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        if (u == v || u < 0 || v < 0 || u >= n || v >= n) return 0;
        if (has_edge(u, v)) return 0;
        if (deg[u] >= dEff || deg[v] >= dEff) return 0;
        add_edge(u, v);
    }
    return 1;
}

static int export_edges(int *eu, int *ev) {
    int m = 0;
    for (int u = 0; u < n_; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (u < v) {
                eu[m] = u;
                ev[m] = v;
                m++;
            }
        }
    }
    return m;
}

static int color_input(int n) {
    static int Q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        Q[tail++] = s;
        while (head < tail) {
            int u = Q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    Q[tail++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Number of ordered-pair-halved vertex pairs at distance > D_. Zero means valid. */
static long long eval_cost(void) {
    int n = n_, W = W_;
    uint64_t (*cur)[MAXW] = BUF1, (*nxt)[MAXW] = BUF2;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D_; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static int L0_cnt(void) { return nL0; }

static void build_lists(void) {
    nL0 = 0;
    nL1 = 0;
    for (int v = 0; v < n_; v++) {
        if (side[v] == 0) L0[nL0++] = v;
        else L1[nL1++] = v;
    }
}

typedef struct {
    int type, a, b, c;
} Move;

static int try_move(Move *mv) {
    if (nL0 == 0 || nL1 == 0) return 0;
    int r = rndint(100);
    if (r < 45) {
        /* rewire the B end of edge (a,b) to b2 */
        int a = L0[rndint(nL0)];
        if (deg[a] == 0) return 0;
        int b = nb[a][rndint(deg[a])];
        int b2 = -1;
        for (int t = 0; t < 16; t++) {
            int c2 = L1[rndint(nL1)];
            if (c2 != b && deg[c2] < dEff && !has_edge(a, c2)) {
                b2 = c2;
                break;
            }
        }
        if (b2 < 0) return 0;
        del_edge(a, b);
        add_edge(a, b2);
        mv->type = 0;
        mv->a = a;
        mv->b = b;
        mv->c = b2;
        return 1;
    } else if (r < 90) {
        /* rewire the A end of edge (a,b) to a2 */
        int b = L1[rndint(nL1)];
        if (deg[b] == 0) return 0;
        int a = nb[b][rndint(deg[b])];
        int a2 = -1;
        for (int t = 0; t < 16; t++) {
            int c2 = L0[rndint(nL0)];
            if (c2 != a && deg[c2] < dEff && !has_edge(c2, b)) {
                a2 = c2;
                break;
            }
        }
        if (a2 < 0) return 0;
        del_edge(a, b);
        add_edge(a2, b);
        mv->type = 1;
        mv->a = a;
        mv->b = b;
        mv->c = a2;
        return 1;
    } else {
        /* add a new cross edge between two spare vertices */
        int a = -1, b = -1;
        for (int t = 0; t < 16; t++) {
            int x = L0[rndint(nL0)];
            int y = L1[rndint(nL1)];
            if (deg[x] < dEff && deg[y] < dEff && !has_edge(x, y)) {
                a = x;
                b = y;
                break;
            }
        }
        if (a < 0) return 0;
        add_edge(a, b);
        mv->type = 2;
        mv->a = a;
        mv->b = b;
        mv->c = -1;
        return 1;
    }
}

static void undo_move(const Move *mv) {
    if (mv->type == 0) {
        del_edge(mv->a, mv->c);
        add_edge(mv->a, mv->b);
    } else if (mv->type == 1) {
        del_edge(mv->c, mv->b);
        add_edge(mv->a, mv->b);
    } else {
        del_edge(mv->a, mv->b);
    }
}

static long long sa_run(long iters, double T0, double T1, double tend) {
    long long cost = eval_cost();
    if (cost == 0) return 0;
    build_lists();
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && clk() > tend) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        Move mv;
        if (!try_move(&mv)) continue;
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0) return 0;
        } else {
            undo_move(&mv);
        }
    }
    return cost;
}

static long long moore_bound(int d, int D) {
    long long mb = 0, term = 1;
    for (int i = 0; i < D; i++) {
        mb += term;
        term *= (d - 1);
        if (term > 1000000) term = 1000000;
    }
    return 2 * mb;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    dEff = d < MAXDEG ? d : MAXDEG;
    if (dEff < 1) dEff = 1;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    double tend = clk() + tl;
    long long mb = moore_bound(d, D_);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 <= 0 || n0 > MAXN - 2 || m0 < 0 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &IEU[e], &IEV[e]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    if (!load_edges(n0, m0, IEU, IEV) || !color_input(n0) || eval_cost() != 0) {
        printf("%d %d\n", n0, m0);
        for (int e = 0; e < m0; e++) printf("%d %d\n", IEU[e], IEV[e]);
        return 0;
    }
    bestN = n0;
    bestM = export_edges(BEU, BEV);

    int fails = 0;
    while (clk() < tend && bestN < mb) {
        if (bestN + 1 > MAXN - 1) break;
        load_edges(bestN + 1, bestM, BEU, BEV);
        int x = bestN;
        int c = rndint(2);
        side[x] = c;
        int cand[MAXN];
        int nc = 0;
        for (int v = 0; v < bestN; v++) {
            if (side[v] != c && deg[v] < dEff) cand[nc++] = v;
        }
        for (int i = nc - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = cand[i];
            cand[i] = cand[j];
            cand[j] = t;
        }
        int want = dEff < nc ? dEff : nc;
        for (int i = 0; i < want; i++) add_edge(x, cand[i]);

        long iters = 20000L + 3000L * (fails < 20 ? fails : 20);
        long long cost = sa_run(iters, 3.0, 0.15, tend);
        if (cost == 0) {
            bestM = export_edges(BEU, BEV);
            bestN = n_;
            fails = 0;
        } else {
            fails++;
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", BEU[e], BEV[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), with optional
# deletions of a matching. Start from PG(2, q) (points 0..m-1, lines m..2m-1).
# Points in SA get a new A-vertex joined to their q+1 lines; lines in SB get a
# new B-vertex joined to their q+1 points. Loads are capacity-limited so that
# every old vertex keeps degree <= d.
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


def _loads_ok(S, caps, nbr):
    """True if every target t is hit by <= caps[t] elements of S, where element x hits nbr[x]."""
    load = [0] * len(caps)
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(len(caps)))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so every target t is hit by <= caps[t] chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < caps[t] for t in nbr[x]):
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


def _pick_deletions(edges, m, r, rng):
    """Random matching of up to r PG incidences, as (point, line) pairs with line index 0..m-1."""
    inc = [(u, v - m) for u, v in edges]
    rng.shuffle(inc)
    usedP, usedL, R = set(), set(), []
    for P, L in inc:
        if len(R) >= r:
            break
        if P in usedP or L in usedL:
            continue
        usedP.add(P)
        usedL.add(L)
        R.append((P, L))
    return R


def _arc_graph(m, edges, R, point_lines, line_points, SA, SB):
    """PG incidence minus deleted matching R, plus one new A-vertex per SA point and one B-vertex per SB line."""
    Rset = set(R)
    na, nb_ = len(SA), len(SB)
    n = 2 * m + na + nb_
    E = [(u, v) for u, v in edges if (u, v - m) not in Rset]
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """Return (n, edges) candidates from arc extensions of PG(2, q), largest first."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q))
        capS = [s] * m
        if _loads_ok(conic, capS, point_lines) and _loads_ok(conic, capS, line_points):
            out.append(_arc_graph(m, edges, [], point_lines, line_points, conic, conic))
        rs_ = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline and trial < 40:
            r = rs_[trial % len(rs_)]
            trial += 1
            R = _pick_deletions(edges, m, r, rng) if r else []
            delP = [0] * m
            delL = [0] * m
            for P, L in R:
                delP[P] += 1
                delL[L] += 1
            capL = [s + delL[L] for L in range(m)]
            capP = [s + delP[P] for P in range(m)]
            SA = _greedy_side(m, capL, point_lines, rng, 6, q_deadline)
            SB = _greedy_side(m, capP, line_points, rng, 6, q_deadline)
            if not (_loads_ok(SA, capL, point_lines) and _loads_ok(SB, capP, line_points)):
                continue
            out.append(_arc_graph(m, edges, R, point_lines, line_points, SA, SB))
    out.sort(key=lambda t: -t[0])
    return out[:40]


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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4 only).
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
# Build: best algebraic start, then the C annealer adds vertices.
# ----------------------------------------------------------------------------

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

    if best_n >= lib.moore_bound(d, D):
        return best

    # Arc-extended projective plane graphs (diameter 3, valid for all D >= 3).
    if D >= 3:
        cands = _arc_candidates(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in cands[:12]:
            if n_c > best_n:
                consider(n_c, e_c)

    # For D >= 4: generalized quadrangle baseline and annealed group lifts.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < t0 + 0.3 * time_limit:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, t0 + 0.3 * time_limit, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C annealer: repeatedly add one vertex and repair with edge rewiring.
    if D >= 3 and best_n > 2:
        elapsed = time.monotonic() - t0
        remaining = 0.9 * time_limit - elapsed
        if remaining > 3.0:
            c_budget = remaining - 2.5
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                                 stdin_graph=best, timeout=remaining)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
