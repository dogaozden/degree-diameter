import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: the main search is no longer a voltage-lift annealer. It is a
# C engine that repairs a diameter-3 bipartite graph by vertex insertion plus
# degree-preserving edge switches, with a bitset ball-counting cost (bad pairs).
#
# Python builds the start graph: the best arc-extended projective plane graph
# (valid for D >= 3, checked with lib.is_valid). For D = 3 the C engine then
# tries to insert vertices, repairing the graph after each insertion. A
# snapshot is kept only at zero cost, so the output is always a valid graph.
# Fallbacks: K_{d,d} (D >= 2) and the arc graph are always checked before use.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 40
#define MAXW (MAXN / 64)

static int d;
static int n;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];

static int s_n;
static int s_side[MAXN];
static int s_deg[MAXN];
static int s_adj[MAXN][MAXD];

static uint64_t BA[MAXN][MAXW];
static uint64_t BB[MAXN][MAXW];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static double t_end;
static int timed_out(void) { return now_s() >= t_end; }

static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

/* Number of unordered vertex pairs at distance > 3. Zero means diameter <= 3. */
static long bad_pairs(void) {
    int nw = (n + 63) / 64;
    uint64_t (*cur)[MAXW] = BA;
    uint64_t (*nxt)[MAXW] = BB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * MAXW);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < 3; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt[v];
            memcpy(o, cur[v], sizeof(uint64_t) * (size_t)nw);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *c = cur[adj[v][k]];
                for (int w = 0; w < nw; w++) o[w] |= c[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < nw; w++)
            tot += popc(cur[v][w]);
    return ((long)n * (long)n - tot) / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static void rem_half(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
    }
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void rem_edge(int a, int b) {
    rem_half(a, b);
    rem_half(b, a);
}

/* Add every legal opposite-side edge between vertices with spare degree. Never hurts. */
static void greedy_fill(void) {
    for (int a = 0; a < n; a++) {
        if (side[a] != 0) continue;
        for (int b = 0; b < n && deg[a] < d; b++) {
            if (side[b] != 1 || deg[b] >= d) continue;
            if (has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

static int pick_side_deg(int s) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(n);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

static int ua, ub, ua2, ub2;

/* Degree-preserving bipartite edge switch: (a,b),(a2,b2) -> (a,b2),(a2,b). */
static int propose_switch(void) {
    int a = pick_side_deg(0), a2 = pick_side_deg(0);
    if (a < 0 || a2 < 0 || a == a2) return 0;
    int b = adj[a][rndint(deg[a])];
    int b2 = adj[a2][rndint(deg[a2])];
    if (b == b2 || has_edge(a, b2) || has_edge(a2, b)) return 0;
    rem_edge(a, b);
    rem_edge(a2, b2);
    add_edge(a, b2);
    add_edge(a2, b);
    ua = a; ub = b; ua2 = a2; ub2 = b2;
    return 1;
}

static void undo_switch(void) {
    rem_edge(ua, ub2);
    rem_edge(ua2, ub);
    add_edge(ua, ub);
    add_edge(ua2, ub2);
}

/* Insert a new vertex on a random side, attached to d opposite vertices.
   A saturated target gives up one of its edges, which frees a slot on the
   other side. */
static void insert_vertex(void) {
    if (n >= MAXN - 1) return;
    int c = rndint(2);
    int y = n++;
    side[y] = c;
    deg[y] = 0;
    int tries = 0;
    while (deg[y] < d && tries < 50 * n) {
        tries++;
        int u = rndint(n - 1);
        if (side[u] == c || has_edge(y, u)) continue;
        if (deg[u] >= d) {
            int w = adj[u][rndint(deg[u])];
            rem_edge(u, w);
        }
        add_edge(y, u);
    }
}

/* Simulated annealing on edge switches; returns the final bad-pair count. */
static long attempt(long steps) {
    long cur = bad_pairs();
    for (long s = 0; s < steps && cur > 0; s++) {
        if (timed_out()) break;
        double T = 0.6 * (1.0 - (double)s / (double)steps) + 0.03;
        if (!propose_switch()) continue;
        long nc = bad_pairs();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nc;
        else undo_switch();
    }
    return cur;
}

static void save_state(void) {
    s_n = n;
    memcpy(s_side, side, sizeof(int) * (size_t)n);
    memcpy(s_deg, deg, sizeof(int) * (size_t)n);
    memcpy(s_adj, adj, sizeof(adj[0]) * (size_t)n);
}

static void restore_state(void) {
    n = s_n;
    memcpy(side, s_side, sizeof(int) * (size_t)n);
    memcpy(deg, s_deg, sizeof(int) * (size_t)n);
    memcpy(adj, s_adj, sizeof(adj[0]) * (size_t)n);
}

static void print_state(void) {
    long m = 0;
    for (int v = 0; v < s_n; v++)
        for (int k = 0; k < s_deg[v]; k++)
            if (v < s_adj[v][k]) m++;
    printf("%d %ld\n", s_n, m);
    for (int v = 0; v < s_n; v++)
        for (int k = 0; k < s_deg[v]; k++)
            if (v < s_adj[v][k]) printf("%d %d\n", v, s_adj[v][k]);
}

static int qbuf[MAXN];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    t_end = now_s() + tl * 0.85 - 0.3;

    if (d < 1 || d > MAXD || D != 3) { printf("0 0\n"); return 0; }

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { printf("0 0\n"); return 0; }

    if (nin == 0) {
        n = 2 * d;
        if (n > MAXN - 2) { printf("0 0\n"); return 0; }
        for (int i = 0; i < n; i++) { side[i] = (i < d) ? 0 : 1; deg[i] = 0; }
        for (int i = 0; i < d; i++)
            for (int j = d; j < 2 * d; j++) add_edge(i, j);
    } else {
        if (nin > MAXN - 200) { printf("0 0\n"); return 0; }
        n = nin;
        for (int i = 0; i < n; i++) deg[i] = 0;
        for (int i = 0; i < min_; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
        }
        /* 2-colour by BFS; reject non-bipartite input. */
        for (int i = 0; i < n; i++) side[i] = -1;
        int bad = 0;
        for (int s = 0; s < n && !bad; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int head = 0, tail = 0;
            qbuf[tail++] = s;
            while (head < tail && !bad) {
                int u = qbuf[head++];
                for (int k = 0; k < deg[u]; k++) {
                    int w = adj[u][k];
                    if (side[w] < 0) {
                        side[w] = 1 - side[u];
                        qbuf[tail++] = w;
                    } else if (side[w] == side[u]) {
                        bad = 1;
                        break;
                    }
                }
            }
        }
        if (bad) { printf("0 0\n"); return 0; }
    }

    save_state();
    while (!timed_out()) {
        insert_vertex();
        greedy_fill();
        long c = attempt(2500);
        if (c == 0) save_state();
        else restore_state();
    }
    print_state();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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


def _arc_graph(m, edges, point_lines, S, line_points):
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


def _arc_best(d, deadline, rng):
    """Largest valid arc-extended graph over prime powers q with q + 1 <= d, or None."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        if best is None or n_c > best[0]:
            best = (n_c, e_c)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def elapsed():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    bound = lib.moore_bound(d, D)

    # Arc-extended projective plane start (diameter 3, so valid for D >= 3).
    cand = _arc_best(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
    if cand is not None and cand[0] > best_n and lib.is_valid(cand[0], cand[1], d, D):
        best_n, best_e = cand

    # Bold step: C vertex-insertion repair search for D = 3, from the arc start.
    if D == 3 and best_n < bound:
        # Leave room for C compile time and output; the C engine self-limits.
        budget = time_limit * 0.85 - elapsed() - 1.5
        if budget > 0.5:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=max(1.0, time_limit * 0.93 - elapsed()))
                n2, e2 = lib.parse_graph_text(out)
                if n2 > best_n and lib.is_valid(n2, e2, d, D):
                    best_n, best_e = n2, e2
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
