import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# A-side: a set SA of points, each gets a new vertex joined to its q+1 lines.
#         Every line holds <= s SA points, where s = d - q - 1.
# B-side: a set SB of lines, each gets a new vertex joined to its q+1 points.
#         Every point lies on <= s SB lines.
# This gives a valid diameter-3 graph of order 2(q^2+q+1) + |SA| + |SB|.
#
# Stage 2 (new in this version): a C engine takes that graph and grows it one
# vertex at a time. Each growth step attaches a new vertex to spare-degree
# vertices of the opposite colour, then runs simulated annealing over
# bipartite-preserving edge moves (double swaps, endpoint redirects, and
# edge insertions). The cost is the number of vertex pairs at distance > D.
# A step succeeds when the cost reaches zero; the engine then keeps the larger
# graph and tries again. Otherwise it restores the last valid graph and retries.
# Every move preserves bipartiteness and the degree cap, so every reported graph
# is valid by construction. Python still checks it with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXD 64

static int N = 0, Dg = 3, DIAM = 3;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int sN = 0;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];
static int scol[MAXN];
static int have_best = 0;

typedef struct { int op, u, v; } Op;
static Op ops[16];
static int nops = 0;

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

static void do_add(int u, int v) {
    add_edge(u, v);
    ops[nops].op = 0; ops[nops].u = u; ops[nops].v = v; nops++;
}

static void do_rem(int u, int v) {
    remove_edge(u, v);
    ops[nops].op = 1; ops[nops].u = u; ops[nops].v = v; nops++;
}

static void undo_ops(void) {
    while (nops > 0) {
        nops--;
        if (ops[nops].op == 0) remove_edge(ops[nops].u, ops[nops].v);
        else add_edge(ops[nops].u, ops[nops].v);
    }
}

/* Number of unordered vertex pairs at distance > DIAM (unreachable counts as bad). */
static long long bad_pairs(void) {
    int n = N;
    int W = (n + 63) / 64;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < DIAM; step++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
            for (int w = 0; w < W; w++)
                if (nxt[v][w] != cur[v][w]) changed = 1;
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Double swap: (a,b),(c,e) -> (a,e),(c,b). Keeps every degree and the bipartition. */
static int move_swap(void) {
    for (int tries = 0; tries < 30; tries++) {
        int a = rndint(N);
        if (deg[a] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int c = rndint(N);
        if (c == a || col[c] != col[a] || deg[c] == 0) continue;
        int e = adj[c][rndint(deg[c])];
        if (b == e) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        do_rem(a, b);
        do_rem(c, e);
        do_add(a, e);
        do_add(c, b);
        return 1;
    }
    return 0;
}

/* Move one endpoint of an edge to another vertex of the same colour that has spare degree. */
static int move_redirect(void) {
    for (int tries = 0; tries < 30; tries++) {
        int a = rndint(N);
        if (deg[a] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int x = rndint(N);
        if (x == a || col[x] != col[a] || deg[x] >= Dg || has_edge(x, b)) continue;
        do_rem(a, b);
        do_add(x, b);
        return 1;
    }
    return 0;
}

/* Insert an edge between two spare-degree vertices of opposite colour. */
static int move_add(void) {
    for (int tries = 0; tries < 30; tries++) {
        int a = rndint(N);
        if (deg[a] >= Dg) continue;
        int b = rndint(N);
        if (b == a || col[b] == col[a] || deg[b] >= Dg || has_edge(a, b)) continue;
        do_add(a, b);
        return 1;
    }
    return 0;
}

static int propose(void) {
    double r = rnd01();
    if (r < 0.5) {
        if (move_swap()) return 1;
        if (move_redirect()) return 1;
        return move_add();
    }
    if (r < 0.8) {
        if (move_redirect()) return 1;
        if (move_swap()) return 1;
        return move_add();
    }
    if (move_add()) return 1;
    if (move_redirect()) return 1;
    return move_swap();
}

/* Simulated annealing on the bad-pair count until cost 0, the time limit, or the slice end. */
static long long anneal(double until, double slice, double T0, double T1) {
    double t0 = now_sec();
    long long cur = bad_pairs();
    double T = T0;
    unsigned long long it = 0;
    if (slice <= 0) slice = 1e-3;
    while (cur > 0) {
        if ((it & 31ULL) == 0) {
            double t = now_sec();
            if (t >= until) break;
            double frac = (t - t0) / slice;
            if (frac > 1.0) frac = 1.0;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        nops = 0;
        if (!propose()) {
            nops = 0;
            continue;
        }
        long long c2 = bad_pairs();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            nops = 0;
        } else {
            undo_ops();
        }
    }
    return cur;
}

static void save_best(void) {
    sN = N;
    for (int v = 0; v < N; v++) {
        sdeg[v] = deg[v];
        scol[v] = col[v];
        memcpy(sadj[v], adj[v], sizeof(int) * MAXD);
    }
    have_best = 1;
}

static void load_best(void) {
    N = sN;
    for (int v = 0; v < N; v++) {
        deg[v] = sdeg[v];
        col[v] = scol[v];
        memcpy(adj[v], sadj[v], sizeof(int) * MAXD);
    }
}

/* Append a vertex of colour c and attach it to up to Dg spare opposite-colour vertices. */
static int add_vertex(int c) {
    if (N == 0 || N >= MAXN - 1) return 0;
    int v = N++;
    deg[v] = 0;
    col[v] = c;
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < v; u++)
        if (col[u] != c && deg[u] < Dg) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int take = nc < Dg ? nc : Dg;
    for (int i = 0; i < take; i++) add_edge(v, cand[i]);
    if (take == 0) {
        /* No spare opposite-colour vertex: steal an edge from a random vertex. */
        int opp = -1;
        for (int tries = 0; tries < 200 && opp < 0; tries++) {
            int u = rndint(v);
            if (col[u] != c && deg[u] > 0) opp = u;
        }
        if (opp < 0) {
            N--;
            return 0;
        }
        int w = adj[opp][rndint(deg[opp])];
        remove_edge(opp, w);
        add_edge(v, opp);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    double t_start = now_sec();
    double deadline = t_start + tl;

    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    Dg = d;
    if (Dg > MAXD) Dg = MAXD;
    if (Dg < 1) Dg = 1;
    DIAM = D;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 <= 0 || n0 > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= Dg || deg[v] >= Dg || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* 2-colour by BFS. Any odd cycle means the start is not bipartite. */
    for (int v = 0; v < N; v++) col[v] = -1;
    static int queue[MAXN];
    int ok = 1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    queue[qt++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    /* Make the start graph valid if it is not already. */
    long long c0 = anneal(t_start + 0.3 * tl, 0.3 * tl, 4.0, 0.2);
    if (c0 == 0) save_best();

    /* Grow one vertex at a time, keeping the best valid graph. */
    if (have_best) {
        for (;;) {
            double now = now_sec();
            double remain = deadline - now;
            if (remain < 0.2) break;
            load_best();
            if (N >= MAXN - 2) break;
            if (!add_vertex(rndint(2))) break;
            double slice = remain * 0.25;
            if (slice > 8.0) slice = 8.0;
            if (slice < 0.2) slice = remain;
            double until = now_sec() + slice;
            if (until > deadline) until = deadline;
            long long c = anneal(until, slice, 4.0, 0.2);
            if (c == 0) save_best();
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int m = 0;
    for (int v = 0; v < sN; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (sadj[v][i] > v) m++;
    printf("%d %d\n", sN, m);
    for (int v = 0; v < sN; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (sadj[v][i] > v) printf("%d %d\n", v, sadj[v][i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python construction: arc-extended projective plane graphs.
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
    """Return (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs: valid for D >= 3.
    cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
    cands.sort(key=lambda t: -t[0])
    for n_c, e_c in cands:
        consider(n_c, e_c)

    # Growth search in C, started from the largest valid graph found so far.
    start = best
    elapsed = time.monotonic() - t0
    remaining = time_limit - elapsed
    budget = max(0.5, 0.75 * remaining - 1.0)
    timeout = max(budget + 1.0, 0.92 * remaining - 1.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, float(budget)],
                        stdin_graph=start, timeout=timeout)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
