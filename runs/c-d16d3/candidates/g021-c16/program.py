import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of voltage lifts, a bipartite-preserving edge-switching
# annealer in C grows a valid graph vertex pair by vertex pair. It starts from
# the best arc-extended projective-plane graph and keeps a cost equal to the
# number of vertex pairs at distance > D. Moves are edge adds, 2-switches
# (which keep degrees and bipartiteness) and edge removals. When the cost hits
# zero, it stores the graph and adds one A-vertex and one B-vertex.
# If it stalls, it reloads the best stored graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NC 2048
#define MAXD 64
#define WMAX 32
#define MAXE (NC * MAXD / 2)
#define STALL 40000
#define PERIOD 30000

static int d_, D_;
static int ncur, cap;
static int col[NC];
static int deg[NC];
static int adj[NC][MAXD];
static uint64_t bufA[NC][WMAX];
static uint64_t bufB[NC][WMAX];
static uint64_t rs;
static int best_n = 0, best_m = 0;
static int best_eu[MAXE], best_ev[MAXE];
static int in_eu[MAXE], in_ev[MAXE];
static int lastx, lasty;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int irand(int n) { return (int)(rnd() % (uint64_t)n); }

static int pc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
    return 0;
}
static void add_e(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}
static void rm_half(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) { adj[u][k] = adj[u][--deg[u]]; return; }
    }
}
static void del_e(int u, int v) { rm_half(u, v); rm_half(v, u); }

/* Number of unordered vertex pairs at distance > D_ among vertices 0..ncur-1. */
static int eval_bad(void) {
    int n = ncur;
    int W = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = bufA;
    uint64_t (*nxt)[WMAX] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*tmp)[WMAX] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long miss = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        miss += n - c;
    }
    return (int)(miss / 2);
}

static void save_best(void) {
    best_n = ncur;
    best_m = 0;
    for (int v = 0; v < ncur; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v && best_m < MAXE) {
                best_eu[best_m] = v;
                best_ev[best_m] = u;
                best_m++;
            }
        }
    }
}

static void load_from(int n, int m, const int *eu, const int *ev) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    ncur = n;
    for (int i = 0; i < m; i++) add_e(eu[i], ev[i]);
}

static int grow(void) {
    if (ncur + 2 > cap) return 0;
    col[ncur] = 0;
    col[ncur + 1] = 1;
    deg[ncur] = 0;
    deg[ncur + 1] = 0;
    ncur += 2;
    return 1;
}

static int try_add(void) {
    static int fa[NC], fb[NC];
    int na = 0, nb = 0;
    for (int v = 0; v < ncur; v++) {
        if (deg[v] < d_) {
            if (col[v] == 0) fa[na++] = v; else fb[nb++] = v;
        }
    }
    if (!na || !nb) return 0;
    for (int t = 0; t < 30; t++) {
        int x = fa[irand(na)], y = fb[irand(nb)];
        if (!has_edge(x, y)) {
            add_e(x, y);
            lastx = x;
            lasty = y;
            return 1;
        }
    }
    return 0;
}

/* Random edge oriented so that *a has colour 0 and *b colour 1. */
static int random_edge(int *a, int *b) {
    if (ncur < 2) return 0;
    for (int t = 0; t < 200; t++) {
        int v = irand(ncur);
        if (deg[v] > 0) {
            int u = adj[v][irand(deg[v])];
            if (col[v] == 0) { *a = v; *b = u; } else { *a = u; *b = v; }
            return 1;
        }
    }
    return 0;
}

static int color_graph(int n) {
    static int q[NC];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                if (col[u] == -1) { col[u] = 1 - col[v]; q[t++] = u; }
                else if (col[u] == col[v]) return 0;
            }
        }
    }
    return 1;
}

static void print_graph(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 < 0 || m0 < 0 || n0 > NC - 2 || m0 > MAXE) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &in_eu[i], &in_ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    if (d_ < 1 || d_ > MAXD || D_ < 1) {
        print_graph(n0, m0, in_eu, in_ev);
        return 0;
    }

    for (int v = 0; v < n0; v++) deg[v] = 0;
    ncur = n0;
    for (int i = 0; i < m0; i++) {
        int u = in_eu[i], v = in_ev[i];
        if (u < 0 || u >= n0 || v < 0 || v >= n0 || u == v) { printf("0 0\n"); return 0; }
        if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) { printf("0 0\n"); return 0; }
        add_e(u, v);
    }
    if (!color_graph(n0)) { printf("0 0\n"); return 0; }

    long long mo;
    if (d_ == 1) mo = 2;
    else if (d_ == 2) mo = 2LL * D_;
    else {
        mo = 0;
        long long p = 1;
        for (int i = 0; i < D_; i++) {
            mo += p;
            p *= (d_ - 1);
            if (p > 1000000) p = 1000000;
        }
        mo *= 2;
    }
    cap = NC;
    if (mo < cap) cap = (int)mo;
    if (cap < n0) cap = n0;

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    int cost = eval_bad();
    if (cost == 0) save_best();
    int bestc = cost, stall = 0;
    long cyc = 0;
    double T = 1.0;

    while (1) {
        double el = (double)clock() / CLOCKS_PER_SEC - t0;
        if (el > tl) break;

        if (cost == 0) {
            save_best();
            if (!grow()) break;
            cost = eval_bad();
            bestc = cost;
            stall = 0;
            cyc = 0;
            T = 1.0;
            continue;
        }
        if (stall > STALL) {
            load_from(best_n, best_m, best_eu, best_ev);
            cost = eval_bad();
            bestc = cost;
            stall = 0;
            cyc = 0;
            T = 1.0;
            continue;
        }

        cyc++;
        if (cyc > PERIOD) cyc = 0;
        T = pow(0.03, (double)cyc / PERIOD);

        int op = 0, a = 0, b = 0, c = 0, e = 0;
        double r = urand();
        if (r < 0.45) {
            if (try_add()) op = 1;
        } else if (r < 0.95) {
            if (random_edge(&a, &b) && random_edge(&c, &e) && a != c && b != e
                && !has_edge(a, e) && !has_edge(c, b)) {
                del_e(a, b);
                del_e(c, e);
                add_e(a, e);
                add_e(c, b);
                op = 2;
            }
        } else {
            if (random_edge(&a, &b)) {
                del_e(a, b);
                op = 3;
            }
        }
        if (!op) { stall++; continue; }

        int nc = eval_bad();
        int delta = nc - cost;
        if (delta <= 0 || urand() < exp(-delta / T)) {
            cost = nc;
            if (cost == 0) save_best();
        } else {
            if (op == 1) {
                del_e(lastx, lasty);
            } else if (op == 2) {
                del_e(a, e);
                del_e(c, b);
                add_e(a, b);
                add_e(c, e);
            } else {
                add_e(a, b);
            }
        }
        if (cost < bestc) { bestc = cost; stall = 0; }
        else stall++;
    }

    print_graph(best_n, best_m, best_eu, best_ev);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane start graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    pts = lib.projective_points(q)
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S (diameter 3)."""
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


def _arc_candidates(d, deadline, rng):
    """Return a list of (n, edges) arc-extended graphs, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            S = []
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Build: fallback, arc-extended start, then C annealing growth.
# ----------------------------------------------------------------------------

_MAX_C_D = 60


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3 and 3 <= d <= _MAX_C_D:
        try:
            rng = random.Random(seed * 7919 + d)
            cands = _arc_candidates(d, t0 + 0.2 * time_limit, rng)
            for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
                if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                    best = (n_c, e_c)
                    break
        except Exception:
            pass

        elapsed = time.monotonic() - t0
        c_budget = 0.8 * time_limit - elapsed - 2.5
        if c_budget >= 1.0 and best[0] <= 1500:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=best, timeout=c_budget + 3.0)
                n_c, e_c = lib.parse_graph_text(out)
                if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                    best = (n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
