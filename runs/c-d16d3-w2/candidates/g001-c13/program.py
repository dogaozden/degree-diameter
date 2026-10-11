import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over valid-ish bipartite graphs.
#
# State: bipartite graph with colour classes fixed, max degree d, and a free
# slot pool (alive flags). Objective to maximise:
#     f = (#alive vertices) - LAM * (#vertex pairs at distance > D)
# Moves: add vertex, remove vertex, 2-switch (keeps degrees and bipartition),
# add edge, remove edge. Distances are computed with bitset balls. The best
# state with zero bad pairs is kept and printed. Restarts from the best state
# every CYC iterations, with a geometric temperature schedule in each cycle.
# If no valid graph is ever found, the input graph is printed back unchanged.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 640
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int alive[MAXN];
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int nalive;
} State;

static State cur, sv, best, input;
static int d, D, have_best = 0, best_n = 0;
static double LAM = 0.6;
static uint64_t R[MAXN][MAXW], NX[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 11);
}

static int rnd_int(int k) {
    return (int)(rnd() % (uint32_t)k);
}

static double urand(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++)
        if (s->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(State *s, int u, int v) {
    s->adj[u][s->deg[u]++] = v;
    s->adj[v][s->deg[v]++] = u;
}

static void rm_half(State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) {
        if (s->adj[u][i] == v) {
            s->adj[u][i] = s->adj[u][--s->deg[u]];
            return;
        }
    }
}

static void del_edge(State *s, int u, int v) {
    rm_half(s, u, v);
    rm_half(s, v, u);
}

static void kill_vertex(State *s, int v) {
    while (s->deg[v] > 0) {
        int u = s->adj[v][s->deg[v] - 1];
        del_edge(s, v, u);
    }
    s->alive[v] = 0;
    s->nalive--;
}

static int new_vertex(State *s, int c) {
    for (int v = 0; v < MAXN; v++) {
        if (!s->alive[v]) {
            s->alive[v] = 1;
            s->col[v] = c;
            s->deg[v] = 0;
            s->nalive++;
            return v;
        }
    }
    return -1;
}

static int random_alive(const State *s) {
    if (s->nalive <= 0) return -1;
    int k = rnd_int(s->nalive);
    for (int v = 0; v < MAXN; v++) {
        if (s->alive[v]) {
            if (k == 0) return v;
            k--;
        }
    }
    return -1;
}

/* Number of unordered pairs of alive vertices at distance > D. */
static long eval_bad(const State *s) {
    int hi = 0;
    uint64_t mask[MAXW];
    for (int w = 0; w < MAXW; w++) mask[w] = 0;
    for (int v = 0; v < MAXN; v++) {
        if (s->alive[v]) {
            hi = v + 1;
            mask[v >> 6] |= 1ULL << (v & 63);
        }
    }
    if (hi == 0) return 0;
    int W = (hi + 63) >> 6;
    for (int v = 0; v < hi; v++) {
        for (int w = 0; w < W; w++) R[v][w] = 0;
        if (s->alive[v]) R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < hi; v++) {
            for (int w = 0; w < W; w++) NX[v][w] = R[v][w];
            if (s->alive[v]) {
                for (int i = 0; i < s->deg[v]; i++) {
                    int u = s->adj[v][i];
                    for (int w = 0; w < W; w++) NX[v][w] |= R[u][w];
                }
            }
            for (int w = 0; w < W; w++)
                if (NX[v][w] != R[v][w]) changed = 1;
        }
        for (int v = 0; v < hi; v++)
            for (int w = 0; w < W; w++) R[v][w] = NX[v][w];
        if (!changed) break;
    }
    long bad2 = 0;
    for (int v = 0; v < hi; v++) {
        if (!s->alive[v]) continue;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(R[v][w] & mask[w]);
        bad2 += s->nalive - c;
    }
    return bad2 / 2;
}

static void move_add_vertex(State *s) {
    int c = rnd_int(2);
    int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < MAXN; u++)
        if (s->alive[u] && s->col[u] != c && s->deg[u] < d) cand[nc++] = u;
    if (nc == 0) return;
    int k = (rnd() & 1u) ? d : 1 + rnd_int(d);
    if (k > nc) k = nc;
    for (int i = 0; i < k; i++) {
        int j = i + rnd_int(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int w = new_vertex(s, c);
    if (w < 0) return;
    for (int i = 0; i < k; i++) add_edge(s, w, cand[i]);
}

static void move_remove_vertex(State *s) {
    if (s->nalive <= 2) return;
    int v = random_alive(s);
    if (v >= 0) kill_vertex(s, v);
}

/* 2-switch: (a,b),(c,e) -> (a,e),(c,b); keeps degrees and bipartition. */
static void move_switch(State *s) {
    int a = random_alive(s);
    if (a < 0 || s->deg[a] == 0) return;
    int b = s->adj[a][rnd_int(s->deg[a])];
    int X = s->col[a];
    int c = random_alive(s);
    if (c < 0 || c == a || s->col[c] != X || s->deg[c] == 0) return;
    int e = s->adj[c][rnd_int(s->deg[c])];
    if (e == b) return;
    if (has_edge(s, a, e) || has_edge(s, c, b)) return;
    del_edge(s, a, b);
    del_edge(s, c, e);
    add_edge(s, a, e);
    add_edge(s, c, b);
}

static void move_add_edge(State *s) {
    for (int t = 0; t < 20; t++) {
        int u = random_alive(s), v = random_alive(s);
        if (u < 0 || v < 0 || u == v || s->col[u] == s->col[v]) continue;
        if (s->deg[u] >= d || s->deg[v] >= d || has_edge(s, u, v)) continue;
        add_edge(s, u, v);
        return;
    }
}

static void move_remove_edge(State *s) {
    int a = random_alive(s);
    if (a < 0 || s->deg[a] == 0) return;
    int b = s->adj[a][rnd_int(s->deg[a])];
    del_edge(s, a, b);
}

static void emit(const State *s) {
    static int id[MAXN];
    int n = 0;
    for (int v = 0; v < MAXN; v++) id[v] = s->alive[v] ? n++ : -1;
    int m = 0;
    for (int u = 0; u < MAXN; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++)
            if (s->adj[u][i] > u) m++;
    }
    printf("%d %d\n", n, m);
    for (int u = 0; u < MAXN; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) {
            int v = s->adj[u][i];
            if (v > u) printf("%d %d\n", id[u], id[v]);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (argc >= 6) LAM = atof(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN) {
        printf("0 0\n");
        return 0;
    }
    memset(&cur, 0, sizeof cur);
    for (int v = 0; v < N0; v++) cur.alive[v] = 1;
    cur.nalive = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(&cur, u, v)) continue;
        add_edge(&cur, u, v);
    }

    /* 2-colour the start graph by BFS; reject if it is not bipartite. */
    static int q[MAXN];
    for (int v = 0; v < MAXN; v++) cur.col[v] = -1;
    for (int s0 = 0; s0 < N0; s0++) {
        if (cur.col[s0] >= 0) continue;
        cur.col[s0] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s0;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < cur.deg[u]; i++) {
                int v = cur.adj[u][i];
                if (cur.col[v] < 0) {
                    cur.col[v] = 1 - cur.col[u];
                    q[qt++] = v;
                }
            }
        }
    }
    for (int u = 0; u < N0; u++)
        for (int i = 0; i < cur.deg[u]; i++)
            if (cur.col[u] == cur.col[cur.adj[u][i]]) { printf("0 0\n"); return 0; }

    input = cur;
    long bad = eval_bad(&cur);
    if (bad == 0) {
        best = cur;
        best_n = cur.nalive;
        have_best = 1;
    }
    double fcur = cur.nalive - LAM * bad;

    const double T0 = 1.0, Tmin = 0.03;
    const long CYC = 40000;
    long cyc = 0;
    clock_t t0 = clock();
    for (long it = 0; ; it++) {
        if ((it & 31) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        if (cyc >= CYC) {
            cyc = 0;
            if (have_best) cur = best;
            bad = eval_bad(&cur);
            fcur = cur.nalive - LAM * bad;
        }
        double T = T0 * pow(Tmin / T0, (double)cyc / (double)CYC);
        cyc++;
        sv = cur;
        int mv = rnd_int(100);
        if (mv < 12) move_add_vertex(&cur);
        else if (mv < 15) move_remove_vertex(&cur);
        else if (mv < 55) move_switch(&cur);
        else if (mv < 80) move_add_edge(&cur);
        else if (mv < 90) move_remove_edge(&cur);
        else continue;

        long nb = eval_bad(&cur);
        double fn = cur.nalive - LAM * nb;
        double dl = fn - fcur;
        if (dl >= 0 || urand() < exp(dl / T)) {
            fcur = fn;
            bad = nb;
            if (nb == 0 && (!have_best || cur.nalive > best_n)) {
                best = cur;
                best_n = cur.nalive;
                have_best = 1;
            }
        } else {
            cur = sv;
        }
    }

    emit(have_best ? &best : &input);
    return 0;
}
"""


def _c_anneal(graph, d, D, seed, budget, lam=0.6):
    """Run the C annealing engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 32 or graph[0] > 600:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lam],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 6.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. A new point-side vertex is joined to
# the q+1 lines through a chosen point; each line may serve at most s chosen
# points. Symmetrically for the line side. The sides are independent.
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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Driver.
#   D == 1: single edge. D == 2: K_{d,d}.
#   D >= 3: best of arc-extended PG graphs and the Araujo-Lopez graph (all have
#           diameter 3, hence are valid for any D >= 3), then C annealing from
#           the best valid start until about 82% of time_limit.
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
    if D == 2:
        return best

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    arcs = _arc_extensions(d, start + 0.10 * time_limit,
                           random.Random(seed * 7919 + d))
    arcs.sort(key=lambda t: -t[0])
    for g in arcs:
        consider(g)

    # Araujo-Lopez record-type graph for the largest prime power q <= d - 2.
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                consider(lib.araujo_lopez_graph(q))
            except Exception:
                pass
            break

    budget = 0.82 * time_limit - elapsed()
    if budget >= 0.5:
        consider(_c_anneal(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
