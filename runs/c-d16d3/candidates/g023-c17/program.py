import itertools
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
# C engine: bipartite vertex-insertion annealing with bitset distance cost.
#
# State: a bipartite graph with max degree d and n vertices. Cost = number of
# unordered pairs at distance > D (computed by bitset BFS to depth D).
# Moves: degree-preserving edge switches, edge additions into spare capacity,
# and edge removals. When cost hits 0 the graph is saved and a new vertex is
# inserted (joined to spare vertices of the opposite colour). If the search
# stalls, it restarts from the best saved graph plus a fresh vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 2048
#define WMAX 32
#define MAXE 200000
#define MAXD 60
#define STALL 6000

typedef uint64_t row_t[WMAX];

static int d_, D_;
static int n_, M_;
static unsigned char adj[MAXN][MAXN];
static int col[MAXN], deg[MAXN], ncnt[MAXN];
static int nbr[MAXN][MAXD];
static int ea[MAXE], eb[MAXE];
static row_t RA[MAXN], RB[MAXN];

static int best_n, best_M;
static int best_col[MAXN];
static int bea[MAXE], beb[MAXE];

static int s0[MAXN], s1[MAXN];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int a, int b) {           /* a has colour 0, b colour 1 */
    adj[a][b] = adj[b][a] = 1;
    ea[M_] = a; eb[M_] = b; M_++;
    deg[a]++; deg[b]++;
}

static void remove_index(int i) {
    int a = ea[i], b = eb[i];
    adj[a][b] = adj[b][a] = 0;
    deg[a]--; deg[b]--;
    M_--;
    ea[i] = ea[M_]; eb[i] = eb[M_];
}

static void clear_state(void) {
    for (int i = 0; i < M_; i++) {
        int a = ea[i], b = eb[i];
        adj[a][b] = adj[b][a] = 0;
    }
    for (int v = 0; v < n_; v++) deg[v] = 0;
    M_ = 0;
}

static void load_state(int n, const int *c, const int *xa, const int *xb, int m) {
    clear_state();
    n_ = n;
    for (int v = 0; v < n; v++) { col[v] = c[v]; deg[v] = 0; }
    for (int i = 0; i < m; i++) add_edge(xa[i], xb[i]);
}

static void build_nbr(void) {
    for (int v = 0; v < n_; v++) ncnt[v] = 0;
    for (int i = 0; i < M_; i++) {
        int a = ea[i], b = eb[i];
        nbr[a][ncnt[a]++] = b;
        nbr[b][ncnt[b]++] = a;
    }
}

/* Number of unordered pairs at distance > D_ (0 means valid). */
static long cost_eval(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    build_nbr();
    row_t *cur = RA, *nx = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < D_; s++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cur[v][w];
            for (int k = 0; k < ncnt[v]; k++) {
                const uint64_t *src = cur[nbr[v][k]];
                for (int w = 0; w < W; w++) nx[v][w] |= src[w];
            }
        }
        row_t *t = cur; cur = nx; nx = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

typedef struct { int type, i, j, a, b, c, e; } Move;

/* type 1: switch, type 2: add edge, type 3: remove edge. */
static int propose(Move *mv) {
    double r = rnd01();
    mv->type = 0;
    if (r < 0.6) {
        if (M_ < 2) return 0;
        int i = rndint(M_), j = rndint(M_);
        if (i == j) return 0;
        int a = ea[i], b = eb[i], c = ea[j], e = eb[j];
        if (a == c || b == e) return 0;
        if (adj[a][e] || adj[c][b]) return 0;
        adj[a][b] = adj[b][a] = 0;
        adj[c][e] = adj[e][c] = 0;
        adj[a][e] = adj[e][a] = 1;
        adj[c][b] = adj[b][c] = 1;
        eb[i] = e; eb[j] = b;
        mv->type = 1; mv->i = i; mv->j = j;
        mv->a = a; mv->b = b; mv->c = c; mv->e = e;
        return 1;
    }
    if (r < 0.92) {
        int c0 = 0, c1 = 0;
        for (int v = 0; v < n_; v++) {
            if (deg[v] < d_) {
                if (col[v] == 0) s0[c0++] = v; else s1[c1++] = v;
            }
        }
        if (!c0 || !c1) return 0;
        for (int t = 0; t < 40; t++) {
            int x = s0[rndint(c0)], y = s1[rndint(c1)];
            if (!adj[x][y]) {
                add_edge(x, y);
                mv->type = 2;
                return 1;
            }
        }
        return 0;
    }
    if (M_ == 0) return 0;
    int i = rndint(M_);
    mv->type = 3; mv->a = ea[i]; mv->b = eb[i];
    remove_index(i);
    return 1;
}

static void undo(const Move *mv) {
    if (mv->type == 1) {
        int a = mv->a, b = mv->b, c = mv->c, e = mv->e, i = mv->i, j = mv->j;
        adj[a][e] = adj[e][a] = 0;
        adj[c][b] = adj[b][c] = 0;
        adj[a][b] = adj[b][a] = 1;
        adj[c][e] = adj[e][c] = 1;
        eb[i] = b; eb[j] = e;
    } else if (mv->type == 2) {
        remove_index(M_ - 1);
    } else if (mv->type == 3) {
        add_edge(mv->a, mv->b);
    }
}

/* Insert a new vertex joined to up to d_ spare vertices of the opposite colour. */
static void grow(void) {
    if (n_ >= MAXN - 1) return;
    static int cand[MAXN];
    int nc = rndint(2);
    int cnt = 0;
    for (int attempt = 0; attempt < 2 && cnt == 0; attempt++) {
        int cc = (attempt == 0) ? 1 - nc : nc;
        cnt = 0;
        for (int v = 0; v < n_; v++)
            if (col[v] == cc && deg[v] < d_) cand[cnt++] = v;
        if (cnt > 0) nc = 1 - cc;
    }
    int take = cnt < d_ ? cnt : d_;
    for (int t = 0; t < take; t++) {
        int k = t + rndint(cnt - t);
        int tmp = cand[t]; cand[t] = cand[k]; cand[k] = tmp;
    }
    int v = n_++;
    col[v] = nc; deg[v] = 0;
    for (int t = 0; t < take; t++) {
        int u = cand[t];
        if (nc == 0) add_edge(v, u); else add_edge(u, v);
    }
}

static void save_best(void) {
    best_n = n_; best_M = M_;
    memcpy(bea, ea, sizeof(int) * (size_t)M_);
    memcpy(beb, eb, sizeof(int) * (size_t)M_);
    memcpy(best_col, col, sizeof(int) * (size_t)n_);
}

static void load_best(void) {
    load_state(best_n, best_col, bea, beb, best_M);
}

static int ia[MAXE], ib[MAXE];
static int icol[MAXN], indeg[MAXN], tcnt[MAXN], qu[MAXN];
static int tadj[MAXN][MAXD];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d_ < 1 || d_ > MAXD || D_ < 1) { printf("1 0\n"); return 0; }
    if (D_ == 1) { printf("2 1\n0 1\n"); return 0; }

    /* ---- read optional start graph ---- */
    int n0 = 0, m0 = 0;
    int okin = 1;
    if (scanf("%d %d", &n0, &m0) != 2) okin = 0;
    if (okin && (n0 < 1 || n0 > MAXN - 1 || m0 < 0 || m0 > MAXE)) okin = 0;
    if (okin) {
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { okin = 0; break; }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { okin = 0; break; }
            ia[i] = u; ib[i] = v;
        }
    }
    if (okin) {
        for (int v = 0; v < n0; v++) indeg[v] = 0;
        for (int i = 0; i < m0; i++) { indeg[ia[i]]++; indeg[ib[i]]++; }
        for (int v = 0; v < n0; v++) if (indeg[v] > d_) okin = 0;
    }
    if (okin) {
        /* bipartite 2-colouring by BFS */
        for (int v = 0; v < n0; v++) { tcnt[v] = 0; icol[v] = -1; }
        for (int i = 0; i < m0; i++) {
            int a = ia[i], b = ib[i];
            tadj[a][tcnt[a]++] = b;
            tadj[b][tcnt[b]++] = a;
        }
        for (int s = 0; s < n0 && okin; s++) {
            if (icol[s] >= 0) continue;
            icol[s] = 0;
            int qh = 0, qt = 0;
            qu[qt++] = s;
            while (qh < qt && okin) {
                int u = qu[qh++];
                for (int k = 0; k < tcnt[u]; k++) {
                    int w = tadj[u][k];
                    if (icol[w] < 0) { icol[w] = 1 - icol[u]; qu[qt++] = w; }
                    else if (icol[w] == icol[u]) { okin = 0; break; }
                }
            }
        }
    }
    if (okin) {
        /* duplicate-edge check using adj, then clear it */
        int dup = 0;
        for (int i = 0; i < m0; i++) {
            int u = ia[i], v = ib[i];
            if (adj[u][v]) dup = 1;
            else adj[u][v] = adj[v][u] = 1;
        }
        for (int i = 0; i < m0; i++) {
            adj[ia[i]][ib[i]] = adj[ib[i]][ia[i]] = 0;
        }
        if (dup) okin = 0;
    }
    if (okin) {
        for (int i = 0; i < m0; i++) {
            if (icol[ia[i]] == 1) { int t = ia[i]; ia[i] = ib[i]; ib[i] = t; }
        }
        load_state(n0, icol, ia, ib, m0);
        if (cost_eval() != 0) okin = 0;
    }
    if (!okin) {
        /* fallback start: K_{d,d}, valid for D >= 2 */
        clear_state();
        n_ = 2 * d_;
        for (int v = 0; v < n_; v++) { col[v] = (v < d_) ? 0 : 1; deg[v] = 0; }
        for (int a = 0; a < d_; a++)
            for (int b = 0; b < d_; b++)
                add_edge(a, d_ + b);
    }

    long cur = cost_eval();
    save_best();

    /* ---- annealing with growth ---- */
    clock_t c0 = clock();
    long iters = 0;
    int stall = 0;
    long lvl = cur;
    Move mv;
    for (;;) {
        if ((iters & 63) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        iters++;
        if (cur == 0) {
            if (n_ > best_n) save_best();
            grow();
            cur = cost_eval();
            lvl = cur;
            stall = 0;
            continue;
        }
        if (!propose(&mv)) continue;
        long nc = cost_eval();
        long delta = nc - cur;
        double T = 0.12 + 2.0 * exp(-3.0 * (double)stall / STALL);
        int acc = (delta <= 0) || (rnd01() < exp(-(double)delta / T));
        if (acc) cur = nc;
        else undo(&mv);

        if (cur < lvl) { lvl = cur; stall = 0; }
        else stall++;

        if (stall > STALL) {
            load_best();
            grow();
            cur = cost_eval();
            lvl = cur;
            stall = 0;
        }
    }
    if (cur == 0 && n_ > best_n) save_best();

    printf("%d %d\n", best_n, best_M);
    for (int i = 0; i < best_M; i++) printf("%d %d\n", bea[i], beb[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                best_n = n_c

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best_n and lib.is_valid(gq[0], gq[1], d, D):
            best = gq
            best_n = gq[0]

    # Vertex-insertion annealing in C, started from the best valid graph found so far.
    elapsed = time.monotonic() - t0
    budget = 0.8 * time_limit - elapsed - 1.0
    if budget >= 0.3:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 2.0)
            n_c, e_c = lib.parse_graph_text(out)
            if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                best_n = n_c
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
