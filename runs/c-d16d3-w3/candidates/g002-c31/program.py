import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), then a C engine
# that grows the best graph by one vertex at a time.
#
# Python: start from PG(2, q) with side sets SA (points) and SB (lines) that add
# one new vertex per element. Also a W(q) quadrangle baseline for D >= 4.
#
# C engine (new in this version): incremental vertex growth.
#   * Exact insertion test: a new vertex x on side X with neighbourhood T is
#     valid iff the balls of radius D-1 around T cover every old vertex. Greedy
#     set cover on bitset balls picks T with spare degree.
#   * If greedy cover fails, the partial vertex is kept and a simulated
#     annealing repair runs on degree-preserving edge switches, plus single
#     edge additions and removals. The cost is the number of vertex pairs at
#     distance > D, computed by bit-parallel ball expansion. The attempt is
#     reverted if the cost does not reach 0.
#   * Only zero-cost states are kept, so every printed graph is valid.
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
    """Plateau local search on a feasible set S0: insert or swap elements while keeping loads <= s."""
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
# C engine: incremental vertex growth with exact set-cover insertion and
# annealed edge-switch repair. Cost = number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXD 64
#define MAXW 25
#define ITERS 1500

typedef uint64_t u64;

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} State;

typedef struct { int type, a, b; } Op;

static int d_, D_;
static u64 rs_ = 88172645463325252ULL;
static State cur_, save_, best_;
static u64 B1[MAXN][MAXW];
static u64 PA[MAXN][MAXW], PB[MAXN][MAXW];
static int A_[MAXN], B_[MAXN];
static int ch_[MAXD];

static u64 rnd64(void) {
    rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17;
    return rs_;
}
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Fills B1 (radius D-1 balls) and returns number of unordered pairs at distance > D_. */
static long long compute_balls(const State *S) {
    int n = S->n, Wn = (n + 63) / 64;
    u64 (*X)[MAXW] = PA;
    u64 (*Y)[MAXW] = PB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < Wn; w++) X[v][w] = 0;
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 1; r <= D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < Wn; w++) Y[v][w] = X[v][w];
            for (int k = 0; k < S->deg[v]; k++) {
                const u64 *src = X[S->adj[v][k]];
                for (int w = 0; w < Wn; w++) Y[v][w] |= src[w];
            }
        }
        if (r == D_ - 1) {
            for (int v = 0; v < n; v++)
                for (int w = 0; w < Wn; w++) B1[v][w] = Y[v][w];
        }
        u64 (*t)[MAXW] = X; X = Y; Y = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < Wn; w++) c += pc64(X[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(const State *S, int a, int b) {
    for (int k = 0; k < S->deg[a]; k++) if (S->adj[a][k] == b) return 1;
    return 0;
}

static void raw_add(State *S, int a, int b) {
    S->adj[a][S->deg[a]++] = b;
    S->adj[b][S->deg[b]++] = a;
}

static void raw_del1(State *S, int a, int b) {
    for (int k = 0; k < S->deg[a]; k++) {
        if (S->adj[a][k] == b) {
            S->adj[a][k] = S->adj[a][--S->deg[a]];
            return;
        }
    }
}

static void raw_del(State *S, int a, int b) {
    raw_del1(S, a, b);
    raw_del1(S, b, a);
}

static void setop(Op *o, int type, int a, int b) { o->type = type; o->a = a; o->b = b; }

static void apply_ops(State *S, const Op *ops, int k) {
    for (int i = 0; i < k; i++) {
        if (ops[i].type == 0) raw_add(S, ops[i].a, ops[i].b);
        else raw_del(S, ops[i].a, ops[i].b);
    }
}

static void undo_ops(State *S, const Op *ops, int k) {
    for (int i = k - 1; i >= 0; i--) {
        if (ops[i].type == 0) raw_del(S, ops[i].a, ops[i].b);
        else raw_add(S, ops[i].a, ops[i].b);
    }
}

/* mode 0: vertices of side with deg > 0; mode 1: vertices of side with deg < d_. */
static int collect(const State *S, int side, int mode, int *out) {
    int c = 0;
    for (int v = 0; v < S->n; v++) {
        if (S->side[v] != side) continue;
        int ok = (mode == 0) ? (S->deg[v] > 0) : (S->deg[v] < d_);
        if (ok) out[c++] = v;
    }
    return c;
}

static int mv_switch(State *S, Op *ops) {
    int c = collect(S, 0, 0, A_);
    if (c < 2) return 0;
    int a1 = A_[rndint(c)], a2 = A_[rndint(c)];
    if (a1 == a2) return 0;
    int b1 = S->adj[a1][rndint(S->deg[a1])];
    int b2 = S->adj[a2][rndint(S->deg[a2])];
    if (b1 == b2) return 0;
    if (has_edge(S, a1, b2) || has_edge(S, a2, b1)) return 0;
    setop(&ops[0], 1, a1, b1);
    setop(&ops[1], 1, a2, b2);
    setop(&ops[2], 0, a1, b2);
    setop(&ops[3], 0, a2, b1);
    return 4;
}

static int mv_add(State *S, Op *ops) {
    int ca = collect(S, 0, 1, A_);
    if (ca == 0) return 0;
    int cb = collect(S, 1, 1, B_);
    if (cb == 0) return 0;
    int a = A_[rndint(ca)], b = B_[rndint(cb)];
    if (has_edge(S, a, b)) return 0;
    setop(&ops[0], 0, a, b);
    return 1;
}

static int mv_remove(State *S, Op *ops) {
    int c = collect(S, 0, 0, A_);
    if (c == 0) return 0;
    int a = A_[rndint(c)];
    int b = S->adj[a][rndint(S->deg[a])];
    setop(&ops[0], 1, a, b);
    return 1;
}

/* Simulated annealing on edge moves; returns final cost. Leaves B1 valid only if cost is 0 on return. */
static long long anneal(State *S, long long cost, int iters, clock_t tlim) {
    Op ops[4];
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && clock() > tlim) break;
        double T = pow(0.08, (double)it / (double)iters);
        double r = rnd01();
        int k;
        if (r < 0.6) k = mv_switch(S, ops);
        else if (r < 0.9) k = mv_add(S, ops);
        else k = mv_remove(S, ops);
        if (k == 0) continue;
        apply_ops(S, ops, k);
        long long nc = compute_balls(S);
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = nc;
        else undo_ops(S, ops, k);
    }
    return cost;
}

static int color_graph(State *S) {
    static int stk[MAXN];
    int n = S->n;
    for (int v = 0; v < n; v++) S->side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (S->side[s] >= 0) continue;
        S->side[s] = 0;
        int top = 0;
        stk[top++] = s;
        while (top > 0) {
            int u = stk[--top];
            for (int k = 0; k < S->deg[u]; k++) {
                int v = S->adj[u][k];
                if (S->side[v] < 0) {
                    S->side[v] = 1 - S->side[u];
                    stk[top++] = v;
                } else if (S->side[v] == S->side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Greedy set cover of old vertices by balls of chosen opposite-side vertices with spare degree. */
static int greedy(const State *S, int sx, int noise, int *ch, int *full) {
    int n = S->n, Wn = (n + 63) / 64;
    u64 cov[MAXW];
    static char used[MAXN];
    for (int w = 0; w < Wn; w++) cov[w] = 0;
    for (int v = 0; v < n; v++) used[v] = 0;
    int nch = 0;
    for (int step = 0; step < d_; step++) {
        int bt = -1;
        long long bs = -1;
        for (int t = 0; t < n; t++) {
            if (S->side[t] == sx || S->deg[t] >= d_ || used[t]) continue;
            int gain = 0;
            for (int w = 0; w < Wn; w++) gain += pc64(B1[t][w] & ~cov[w]);
            if (gain == 0) continue;
            long long score = (long long)gain * 4096;
            if (noise) score += rndint(4096);
            if (score > bs) { bs = score; bt = t; }
        }
        if (bt < 0) break;
        used[bt] = 1;
        ch[nch++] = bt;
        for (int w = 0; w < Wn; w++) cov[w] |= B1[bt][w];
    }
    int pop = 0;
    for (int w = 0; w < Wn; w++) pop += pc64(cov[w]);
    *full = (pop == n && nch > 0);
    return nch;
}

static void push_vertex(State *S, int sx, const int *ch, int nch) {
    int x = S->n++;
    S->side[x] = sx;
    S->deg[x] = 0;
    for (int k = 0; k < nch; k++) raw_add(S, x, ch[k]);
}

static void print_state(const State *S) {
    int m = 0;
    for (int a = 0; a < S->n; a++)
        for (int k = 0; k < S->deg[a]; k++)
            if (S->adj[a][k] > a) m++;
    printf("%d %d\n", S->n, m);
    for (int a = 0; a < S->n; a++)
        for (int k = 0; k < S->deg[a]; k++) {
            int b = S->adj[a][k];
            if (b > a) printf("%d %d\n", a, b);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    double tl = atof(argv[4]);
    clock_t tlim = clock() + (clock_t)(tl * CLOCKS_PER_SEC);
    if (d_ < 1 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    int ok = 0;
    memset(&cur_, 0, sizeof(cur_));
    if (scanf("%d %d", &n, &m) == 2 && n >= 2 && n < MAXN - 2) {
        cur_.n = n;
        int good = 1;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { good = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { good = 0; break; }
            if (cur_.deg[u] >= d_ || cur_.deg[v] >= d_ || has_edge(&cur_, u, v)) { good = 0; break; }
            raw_add(&cur_, u, v);
        }
        ok = good && color_graph(&cur_) && compute_balls(&cur_) == 0;
    }
    if (!ok) {
        memset(&cur_, 0, sizeof(cur_));
        cur_.n = 2;
        cur_.side[0] = 0;
        cur_.side[1] = 1;
        raw_add(&cur_, 0, 1);
        compute_balls(&cur_);
    }
    best_ = cur_;

    while (cur_.n < MAXN - 2 && clock() < tlim) {
        int sx = rndint(2);
        int noise = (int)(rnd64() % 3 == 0);
        int full = 0;
        int nch = greedy(&cur_, sx, noise, ch_, &full);
        if (full) {
            save_ = cur_;
            push_vertex(&cur_, sx, ch_, nch);
            if (compute_balls(&cur_) == 0) {
                best_ = cur_;
            } else {
                cur_ = save_;
                compute_balls(&cur_);
            }
            continue;
        }
        save_ = cur_;
        push_vertex(&cur_, sx, ch_, nch);
        long long c = compute_balls(&cur_);
        c = anneal(&cur_, c, ITERS, tlim);
        if (c == 0) {
            best_ = cur_;
        } else {
            cur_ = save_;
            compute_balls(&cur_);
        }
    }
    print_state(&best_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C engine: grow the best graph by inserting vertices (exact set cover)
    # and annealed edge repair. Skipped when the Moore bound is already met.
    if best_n < lib.moore_bound(d, D) and time_limit > 4:
        elapsed = time.monotonic() - start
        budget = 0.72 * time_limit - elapsed - 1.0
        if budget >= 1.0:
            timeout = 0.9 * time_limit - elapsed
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=timeout)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
