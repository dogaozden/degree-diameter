"""Diameter-3 bipartite search with a repair-based annealing engine.

Change from the parent: the augmentation is no longer only greedy set cover. The C engine
has two modes that share one graph representation:

  mode 0: the parent's greedy vertex addition (guaranteed to keep the graph valid).
  mode 1: a repair search. After each successful addition the new vertex is joined to
          d vertices, which may create bad pairs (pairs at distance > D). Simulated
          annealing then rewires edges, adds edges into spare capacity, and moves edge
          endpoints to repair them. Only a state with zero bad pairs is kept as the
          new snapshot. A failed repair restores the snapshot and tries another addition.

Python runs greedy first, then repair from the best result. Every output is re-checked with
lib.is_valid, and K_{d,d} remains the fallback.
"""
import itertools
import random
import time

import lib

MAX_C_DEG = 32

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WORDS (MAXN / 64)
#define MAXDEG 32

typedef uint64_t Row[WORDS];

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static Row RA[MAXN], RB[MAXN], BL[MAXN];
static uint64_t rs = 88172645463325252ULL;

/* snapshot */
static int S_N;
static int S_deg[MAXN];
static int S_adj[MAXN][MAXDEG];
static int S_side[MAXN];

typedef struct { int type, u, v; } Op;
static Op oplog[16];
static int nops = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void raw_add(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void raw_del(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

static void op_add(int u, int v) {
    raw_add(u, v);
    oplog[nops].type = 0; oplog[nops].u = u; oplog[nops].v = v; nops++;
}

static void op_del(int u, int v) {
    raw_del(u, v);
    oplog[nops].type = 1; oplog[nops].u = u; oplog[nops].v = v; nops++;
}

static void undo_ops(void) {
    while (nops > 0) {
        Op o = oplog[--nops];
        if (o.type == 0) raw_del(o.u, o.v);
        else raw_add(o.u, o.v);
    }
}

/* Bitsets of vertices reachable within `rounds` steps; returns the array holding the result. */
static Row *reach_all(int rounds) {
    Row *cur = RA, *nxt = RB;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < rounds; r++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) nxt[v][i] = cur[v][i];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int i = 0; i < W; i++) nxt[v][i] |= cur[u][i];
            }
        }
        Row *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > Dist (unreachable counts). */
static long evaluate(void) {
    Row *cur = reach_all(Dist);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < W; i++) c += popc(cur[v][i]);
        bad += N - c;
    }
    return bad / 2;
}

static void save_snap(void) {
    S_N = N;
    memcpy(S_deg, deg, sizeof(deg));
    memcpy(S_adj, adj, sizeof(adj));
    memcpy(S_side, side, sizeof(side));
}

static void load_snap(void) {
    N = S_N;
    W = (N + 63) / 64;
    memcpy(deg, S_deg, sizeof(deg));
    memcpy(adj, S_adj, sizeof(adj));
    memcpy(side, S_side, sizeof(side));
}

/* Add a new vertex on side X joined to up to Dd vertices of the other side.
   Full vertices give up one random edge, so their old neighbour gets spare capacity. */
static void add_vertex(int X) {
    static int chosen[MAXN];
    int cand[MAXN], nc = 0;
    int x = N++;
    W = (N + 63) / 64;
    side[x] = X;
    deg[x] = 0;
    memset(chosen, 0, sizeof(chosen));
    for (int v = 0; v < x; v++)
        if (side[v] != X) cand[nc++] = v;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int taken = 0;
    for (int i = 0; i < nc && taken < Dd; i++) {
        int v = cand[i];
        if (deg[v] < Dd) {
            raw_add(x, v);
            chosen[v] = 1;
            taken++;
        }
    }
    for (int i = 0; i < nc && taken < Dd; i++) {
        int v = cand[i];
        if (chosen[v] || deg[v] < Dd || deg[v] == 0) continue;
        int a = adj[v][rndint(deg[v])];
        raw_del(v, a);
        raw_add(x, v);
        chosen[v] = 1;
        taken++;
    }
}

/* Parent's greedy augmentation: a new vertex whose neighbours cover everything within Dist-1. */
static int try_add_greedy(int X) {
    static int sel[MAXN];
    int T[MAXDEG], nt = 0;
    Row U;
    if (N + 2 >= MAXN) return 0;
    Row *c = reach_all(Dist - 1);
    for (int v = 0; v < N; v++) memcpy(BL[v], c[v], sizeof(Row));
    memset(U, 0, sizeof(U));
    for (int v = 0; v < N; v++) U[v >> 6] |= 1ULL << (v & 63);
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(BL[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) { bestsc = sc; best = v; }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~BL[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N++;
    W = (N + 63) / 64;
    side[x] = X;
    deg[x] = 0;
    for (int k = 0; k < nt; k++) raw_add(x, T[k]);
    return 1;
}

/* Random local move. Returns 1 if a move was applied (logged in oplog). */
static int try_move(void) {
    nops = 0;
    int t = rndint(10);
    if (t < 5) {
        int a1 = rndint(N);
        if (deg[a1] == 0) return 0;
        int b1 = adj[a1][rndint(deg[a1])];
        int a2 = rndint(N);
        if (a2 == a1 || side[a2] != side[a1] || deg[a2] == 0) return 0;
        int b2 = adj[a2][rndint(deg[a2])];
        if (b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) return 0;
        op_del(a1, b1);
        op_del(a2, b2);
        op_add(a1, b2);
        op_add(a2, b1);
        return 1;
    }
    if (t < 8) {
        int a = rndint(N);
        if (deg[a] == 0) return 0;
        int b = adj[a][rndint(deg[a])];
        int bp = rndint(N);
        if (side[bp] == side[a] || bp == b || deg[bp] >= Dd || has_edge(a, bp)) return 0;
        op_del(a, b);
        op_add(a, bp);
        return 1;
    }
    int a = rndint(N), b = rndint(N);
    if (a == b || side[a] == side[b] || deg[a] >= Dd || deg[b] >= Dd || has_edge(a, b)) return 0;
    op_add(a, b);
    return 1;
}

/* Simulated annealing on the bad-pair count. Returns the final count (0 means valid). */
static long anneal(long steps, double t_end) {
    long cur = evaluate();
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 1023) == 0 && now() > t_end) break;
        if (!try_move()) continue;
        double T = 1.2 * (1.0 - (double)s / (double)steps) + 0.03;
        long nb = evaluate();
        long delta = nb - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nb;
        else undo_ops();
        nops = 0;
    }
    return cur;
}

static void emit(void) {
    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    static int bq[MAXN];
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int mode = (argc >= 6) ? atoi(argv[5]) : 1;
    if (Dd < 1 || Dd > MAXDEG || Dist < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 64) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd || has_edge(u, v)) continue;
        raw_add(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                } else if (side[v] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    W = (N + 63) / 64;

    double t_end = now() + budget;

    if (mode == 0) {
        int fails = 0;
        while (now() < t_end && fails < 3000 && N < MAXN - 2) {
            if (try_add_greedy(rndint(2))) fails = 0;
            else fails++;
        }
        emit();
        return 0;
    }

    save_snap();
    int haveValid = (evaluate() == 0);
    if (haveValid) save_snap();
    int fails = 0;
    while (now() < t_end && N < MAXN - 2) {
        if (evaluate() == 0) {
            save_snap();
            haveValid = 1;
            fails = 0;
            add_vertex(rndint(2));
            continue;
        }
        long steps = 6000 + 2000L * (fails < 20 ? fails : 20);
        long left = anneal(steps, t_end);
        if (left == 0) continue;
        if (!haveValid) continue;
        fails++;
        load_snap();
        add_vertex(rndint(2));
    }
    if (haveValid) load_snap();
    emit();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane starts (diameter 3), from the parent program.
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# C engine driver.
# ----------------------------------------------------------------------------

def _run_engine(src, d, D, seed, mode, budget):
    """Run the C engine (mode 0 greedy, mode 1 repair) from the start graph src."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", mode],
                     stdin_graph=(src[0], src[1]), timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        fallback = (2, [(0, 1)]) if lib.is_valid(2, [(0, 1)], d, D) else (1, [])

    rng = random.Random(seed * 7919 + d)
    starts = []
    if D == 3:
        starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    elif D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)

    best = fallback
    for g in starts:
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    # Greedy augmentation first, then repair search from the best graph so far.
    if d <= MAX_C_DEG and best[0] > 1:
        for mode, frac in ((0, 0.2), (1, 1.0)):
            remaining = end - time.monotonic()
            if remaining < 5.0:
                break
            budget = remaining * frac if mode == 0 else remaining - 4.0
            try:
                n1, e1 = _run_engine(best, d, D, seed * 31 + mode, mode, budget)
            except Exception:
                continue
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
