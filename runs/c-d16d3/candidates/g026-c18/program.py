import random
import time

import lib


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
#define MAXE 40000

typedef uint64_t u64;

static int d, Dist;
static int n, m, W;
static int side[MAXN];
static int deg[MAXN];
static int adjl[MAXN][MAXDEG];
static u64 bits[MAXN][MAXW];
static int ea[MAXE], eb[MAXE];          /* ea = side-0 endpoint, eb = side-1 endpoint */
static u64 R[2][MAXN][MAXW];
static u64 rs = 88172645463325252ULL;
static int bn, bm;
static int bea[MAXE], beb[MAXE];
static int bside[MAXN];
static int IU[MAXE], IV[MAXE];
static int nbrs_off[MAXN + 2];
static int nbrs[2 * MAXE];
static int queue_[MAXN];

static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) { return (int)((bits[a][b >> 6] >> (b & 63)) & 1ULL); }

static void del_from_list(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adjl[a][k] == b) { adjl[a][k] = adjl[a][--deg[a]]; break; }
}

static void remove_edge_idx(int i) {
    int a = ea[i], b = eb[i];
    del_from_list(a, b);
    del_from_list(b, a);
    bits[a][b >> 6] &= ~(1ULL << (b & 63));
    bits[b][a >> 6] &= ~(1ULL << (a & 63));
    m--;
    ea[i] = ea[m];
    eb[i] = eb[m];
}

static void remove_edge_ab(int a, int b) {
    for (int i = 0; i < m; i++)
        if (ea[i] == a && eb[i] == b) { remove_edge_idx(i); return; }
}

static void add_edge_raw(int a, int b) {
    adjl[a][deg[a]++] = b;
    adjl[b][deg[b]++] = a;
    bits[a][b >> 6] |= 1ULL << (b & 63);
    bits[b][a >> 6] |= 1ULL << (a & 63);
    ea[m] = a;
    eb[m] = b;
    m++;
}

static void clear_state(void) {
    for (int v = 0; v < MAXN; v++) {
        deg[v] = 0;
        memset(bits[v], 0, sizeof(bits[v]));
    }
    m = 0;
}

/* sd gives sides; (A[e], B[e]) are edges with A on side 0 and B on side 1 (either orientation accepted). */
static void load_graph(int nn, const int *sd, int mm, const int *A, const int *B) {
    clear_state();
    n = nn;
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) side[v] = sd[v];
    for (int e = 0; e < mm; e++) {
        int u = A[e], v = B[e];
        if (side[u] == 0) add_edge_raw(u, v);
        else add_edge_raw(v, u);
    }
}

/* Number of unordered pairs at distance > Dist. */
static long long cost_eval(void) {
    int w = W;
    int cur = 0;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) R[0][v][k] = 0;
        R[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < Dist; t++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            u64 tmp[MAXW];
            for (int k = 0; k < w; k++) tmp[k] = R[cur][v][k];
            for (int j = 0; j < deg[v]; j++) {
                int u = adjl[v][j];
                for (int k = 0; k < w; k++) tmp[k] |= R[cur][u][k];
            }
            for (int k = 0; k < w; k++) R[nx][v][k] = tmp[k];
        }
        cur = nx;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += __builtin_popcountll(R[cur][v][k]);
        total += n - c;
    }
    return total / 2;
}

/* Random vertex on side s with spare degree, or -1. */
static int pick_def(int s) {
    int cnt = 0, pick = -1;
    for (int v = 0; v < n; v++) {
        if (side[v] == s && deg[v] < d) {
            cnt++;
            if (rndint(cnt) == 0) pick = v;
        }
    }
    return pick;
}

static int accept(long long delta, double T) {
    return delta <= 0 || rnd01() < exp(-(double)delta / T);
}

static long long cur_cost;

/* Simulated annealing on the current fixed vertex set. Returns 1 if cost reached 0. */
static int sa_run(long long iters, double T0, double T1, double deadline) {
    cur_cost = cost_eval();
    for (long long it = 0; it < iters; it++) {
        if (cur_cost == 0) return 1;
        if ((it & 127) == 0 && now_sec() > deadline) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int r = rndint(100);
        long long c2;
        if (m >= 2 && r < 45) {
            /* degree-preserving 2-switch */
            int i = rndint(m), j = rndint(m);
            if (i == j) continue;
            int a = ea[i], b = eb[i], c = ea[j], e = eb[j];
            if (a == c || b == e || has_edge(a, e) || has_edge(c, b)) continue;
            remove_edge_ab(a, b);
            remove_edge_ab(c, e);
            add_edge_raw(a, e);
            add_edge_raw(c, b);
            c2 = cost_eval();
            if (accept(c2 - cur_cost, T)) cur_cost = c2;
            else {
                remove_edge_ab(a, e);
                remove_edge_ab(c, b);
                add_edge_raw(a, b);
                add_edge_raw(c, e);
            }
        } else if (m >= 1 && r < 80) {
            /* move one endpoint of an edge to a vertex with spare degree */
            int i = rndint(m);
            int a = ea[i], b = eb[i];
            if (rndint(2) == 0) {
                int x = pick_def(0);
                if (x < 0 || x == a || has_edge(x, b)) continue;
                remove_edge_ab(a, b);
                add_edge_raw(x, b);
                c2 = cost_eval();
                if (accept(c2 - cur_cost, T)) cur_cost = c2;
                else {
                    remove_edge_ab(x, b);
                    add_edge_raw(a, b);
                }
            } else {
                int y = pick_def(1);
                if (y < 0 || y == b || has_edge(a, y)) continue;
                remove_edge_ab(a, b);
                add_edge_raw(a, y);
                c2 = cost_eval();
                if (accept(c2 - cur_cost, T)) cur_cost = c2;
                else {
                    remove_edge_ab(a, y);
                    add_edge_raw(a, b);
                }
            }
        } else {
            /* add an edge between spare-degree vertices on opposite sides */
            int x = pick_def(0), y = pick_def(1);
            if (x < 0 || y < 0 || has_edge(x, y)) continue;
            add_edge_raw(x, y);
            c2 = cost_eval();
            if (accept(c2 - cur_cost, T)) cur_cost = c2;
            else remove_edge_ab(x, y);
        }
    }
    return cur_cost == 0;
}

/* BFS 2-colouring from CSR adjacency. Returns 1 if bipartite. */
static int bip_color(int nn, int mm, const int *U, const int *V, int *col) {
    memset(nbrs_off, 0, sizeof(nbrs_off));
    for (int e = 0; e < mm; e++) {
        nbrs_off[U[e] + 1]++;
        nbrs_off[V[e] + 1]++;
    }
    for (int v = 0; v < nn; v++) nbrs_off[v + 1] += nbrs_off[v];
    static int fillp[MAXN + 2];
    for (int v = 0; v < nn; v++) fillp[v] = nbrs_off[v];
    for (int e = 0; e < mm; e++) {
        nbrs[fillp[U[e]]++] = V[e];
        nbrs[fillp[V[e]]++] = U[e];
    }
    for (int v = 0; v < nn; v++) col[v] = -1;
    for (int s = 0; s < nn; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int k = nbrs_off[u]; k < nbrs_off[u + 1]; k++) {
                int w = nbrs[k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    queue_[qt++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    Dist = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (d > MAXDEG) d = MAXDEG;
    if (d < 1 || Dist < 1) { printf("0 0\n"); return 0; }
    double deadline = now_sec() + budget;

    int nn, mm;
    if (scanf("%d %d", &nn, &mm) != 2 || nn < 1 || nn > MAXN - 4 || mm < 0 || mm > MAXE / 2) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < mm; e++) {
        if (scanf("%d %d", &IU[e], &IV[e]) != 2) { printf("0 0\n"); return 0; }
        if (IU[e] < 0 || IU[e] >= nn || IV[e] < 0 || IV[e] >= nn) { printf("0 0\n"); return 0; }
    }
    static int col[MAXN];
    if (!bip_color(nn, mm, IU, IV, col)) { printf("0 0\n"); return 0; }

    bn = nn;
    bm = mm;
    for (int v = 0; v < nn; v++) bside[v] = col[v];
    for (int e = 0; e < mm; e++) {
        if (col[IU[e]] == 0) { bea[e] = IU[e]; beb[e] = IV[e]; }
        else { bea[e] = IV[e]; beb[e] = IU[e]; }
    }

    static int sd[MAXN];
    int attempt = 0;
    while (now_sec() < deadline && bn + 1 < MAXN - 4) {
        int nn2 = bn + 1;
        int ns = attempt & 1;
        for (int v = 0; v < bn; v++) sd[v] = bside[v];
        sd[bn] = ns;
        load_graph(nn2, sd, bm, bea, beb);
        int ok = sa_run(150000, 1.5, 0.15, deadline);
        if (ok) {
            bn = nn2;
            bm = m;
            for (int e = 0; e < m; e++) { bea[e] = ea[e]; beb[e] = eb[e]; }
            for (int v = 0; v < bn; v++) bside[v] = sd[v];
        }
        attempt++;
    }

    printf("%d %d\n", bn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", bea[e], beb[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Baseline: arc-extended projective plane incidence graphs (diameter 3).
#
# Incidence graph of PG(2, q) plus, for each point P in a set S, a new vertex
# joined to the q+1 lines through P, and for each j in S a new vertex joined to
# the q+1 points on line j. Loads on S must stay within the spare degree
# s = d - q - 1. Order 2(q^2+q+1) + 2|S|.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (n, edges, point_lines, line_points, index) for PG(2, q); lines are indexed like points."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new point-side vertex per P in S and a new line-side vertex per j in S."""
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


def _arc_candidates(d, rng, deadline):
    """Return a list of (n, edges) arc-extended graphs, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)] if s >= 1 else [[]]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Entry point.
#
# 1. Safe baseline: K_{d,d} (valid for D >= 2), upgraded to the best arc-extended
#    projective plane graph when D >= 3.
# 2. C engine: starting from the baseline, repeatedly add one vertex and run
#    simulated annealing over degree-preserving 2-switches and endpoint moves
#    until every pair is within distance D. Each success is kept; a failure
#    leaves the last valid graph as the answer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        deadline = t0 + 0.2 * time_limit
        cands = _arc_candidates(d, rng, deadline)
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            if n_c > best_n:
                consider(n_c, e_c)

    elapsed = time.monotonic() - t0
    budget = time_limit * 0.72 - elapsed
    if budget > 2.0 and best_n >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=(best_n, best_e), timeout=budget + 8.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
