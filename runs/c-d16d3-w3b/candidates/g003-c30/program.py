"""Arc-extended projective plane graphs, then a C search that grows the graph one vertex at a time.

Growth step (new idea): a new vertex x of colour c is attached to up to d opposite-colour
vertices chosen by greedy set cover, so that every colour-c vertex is adjacent to a neighbour
of x (distance 2). Any bipartite graph of diameter 3 already has the other distance-3 pairs.
If the cover is incomplete, the C engine runs simulated annealing on the number of ordered
pairs at distance > D. Moves rewire one edge to a random cross pair of spare-degree vertices.
Edges are only ever added between colour classes, so the graph stays bipartite.
"""
import itertools
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

#define MAXN 1400
#define MAXDEG 128
#define SNAPCAP (MAXN * MAXDEG / 2)

static int d_, D_, n_;
static int col_[MAXN];
static int deg_[MAXN];
static int nb_[MAXN][MAXDEG];
static unsigned char A_[MAXN][MAXN];
static int stamp_[MAXN];
static int curst_ = 0;
static int q_[MAXN];
static int spare_[2][MAXN];
static int nsp_[2];
static unsigned char unc_[MAXN];
static unsigned char used_[MAXN];
static uint64_t rs_ = 88172645463325252ULL;

static int snap_n, snap_m;
static int snap_col[MAXN];
static int snap_eu[SNAPCAP], snap_ev[SNAPCAP];

static clock_t t0_;
static double budget_;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17;
    return rs_;
}
static int rndi(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rndf(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0_) / CLOCKS_PER_SEC; }

static void add_edge(int u, int v) {
    A_[u][v] = 1; A_[v][u] = 1;
    nb_[u][deg_[u]++] = v;
    nb_[v][deg_[v]++] = u;
}

static void remove_at(int u, int k) {
    int v = nb_[u][k];
    A_[u][v] = 0; A_[v][u] = 0;
    deg_[u]--;
    nb_[u][k] = nb_[u][deg_[u]];
    for (int i = 0; i < deg_[v]; i++) {
        if (nb_[v][i] == u) {
            deg_[v]--;
            nb_[v][i] = nb_[v][deg_[v]];
            break;
        }
    }
}

/* Number of ordered pairs (s, t) with distance > D_. Zero means valid. */
static long cost(void) {
    long bad = 0;
    for (int s = 0; s < n_; s++) {
        curst_++;
        int head = 0, tail = 0;
        q_[tail++] = s;
        stamp_[s] = curst_;
        for (int lvl = 0; lvl < D_ && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = q_[head++];
                for (int k = 0; k < deg_[u]; k++) {
                    int v = nb_[u][k];
                    if (stamp_[v] != curst_) {
                        stamp_[v] = curst_;
                        q_[tail++] = v;
                    }
                }
            }
        }
        bad += n_ - tail;
    }
    return bad;
}

static void build_spare(void) {
    nsp_[0] = 0; nsp_[1] = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] < d_) spare_[col_[v]][nsp_[col_[v]]++] = v;
    }
}

static void shuffle_arr(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add every cross edge between spare vertices that is still missing. Never raises the cost. */
static void saturate(void) {
    build_spare();
    shuffle_arr(spare_[0], nsp_[0]);
    shuffle_arr(spare_[1], nsp_[1]);
    for (int i = 0; i < nsp_[0]; i++) {
        int a = spare_[0][i];
        for (int j = 0; j < nsp_[1]; j++) {
            if (deg_[a] >= d_) break;
            int b = spare_[1][j];
            if (deg_[b] < d_ && !A_[a][b]) add_edge(a, b);
        }
    }
}

/* Insert vertex n_ with colour c, joined by greedy set cover to opposite-colour vertices. */
static void attach(int c) {
    int x = n_++;
    col_[x] = c;
    deg_[x] = 0;
    int nleft = 0;
    for (int i = 0; i <= x; i++) {
        unc_[i] = (unsigned char)(i < x && col_[i] == c);
        used_[i] = 0;
        nleft += unc_[i];
    }
    int chosen = 0;
    while (chosen < d_ && nleft > 0) {
        int best = -1, bg = 0, ties = 0;
        for (int t = 0; t < x; t++) {
            if (col_[t] == c || deg_[t] >= d_ || used_[t]) continue;
            int g = 0;
            for (int k = 0; k < deg_[t]; k++) g += unc_[nb_[t][k]];
            if (g > bg) {
                bg = g; best = t; ties = 1;
            } else if (g == bg && g > 0) {
                ties++;
                if (rndi(ties) == 0) best = t;
            }
        }
        if (best < 0) break;
        used_[best] = 1;
        chosen++;
        for (int k = 0; k < deg_[best]; k++) {
            int y = nb_[best][k];
            if (unc_[y]) { unc_[y] = 0; nleft--; }
        }
        add_edge(x, best);
    }
}

/* One annealing move: remove a random edge, then add a random non-edge cross pair of spare vertices. */
static int move_once(double T, long *curp) {
    int u = -1;
    for (int tries = 0; tries < 200 && u < 0; tries++) {
        int x = rndi(n_);
        if (deg_[x] > 0) u = x;
    }
    if (u < 0) return 0;
    int k = rndi(deg_[u]);
    int v = nb_[u][k];
    remove_at(u, k);
    build_spare();
    int a = rndi(2);
    int p = -1, q = -1;
    if (nsp_[0] > 0 && nsp_[1] > 0) {
        for (int tries = 0; tries < 40; tries++) {
            int x = spare_[a][rndi(nsp_[a])];
            int y = spare_[1 - a][rndi(nsp_[1 - a])];
            if (x != y && !A_[x][y]) { p = x; q = y; break; }
        }
    }
    if (p < 0) {
        add_edge(u, v);
        return 0;
    }
    add_edge(p, q);
    long c2 = cost();
    long delta = c2 - *curp;
    if (delta <= 0 || rndf() < exp(-(double)delta / T)) {
        *curp = c2;
        return 1;
    }
    for (int i = 0; i < deg_[p]; i++) {
        if (nb_[p][i] == q) { remove_at(p, i); break; }
    }
    add_edge(u, v);
    return 0;
}

static void save_snap(void) {
    snap_n = n_;
    snap_m = 0;
    for (int i = 0; i < n_; i++) {
        snap_col[i] = col_[i];
        for (int k = 0; k < deg_[i]; k++) {
            int j = nb_[i][k];
            if (j > i && snap_m < SNAPCAP) {
                snap_eu[snap_m] = i;
                snap_ev[snap_m] = j;
                snap_m++;
            }
        }
    }
}

static void load_snap(void) {
    for (int i = 0; i < n_; i++) {
        deg_[i] = 0;
        memset(A_[i], 0, (size_t)n_);
    }
    n_ = snap_n;
    for (int i = 0; i < n_; i++) col_[i] = snap_col[i];
    for (int e = 0; e < snap_m; e++) add_edge(snap_eu[e], snap_ev[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)(atol(argv[3]) + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    budget_ = atof(argv[4]);
    t0_ = clock();
    if (d_ < 1 || d_ > MAXDEG - 8 || D_ < 2) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 == 0) {
        n0 = 2 * d_;
        m0 = 0;
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++) {
                snap_eu[m0] = i;
                snap_ev[m0] = d_ + j;
                m0++;
            }
    } else {
        if (n0 < 0 || n0 > MAXN - 400 || m0 < 0 || m0 > SNAPCAP) { printf("0 0\n"); return 0; }
        for (int e = 0; e < m0; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { printf("0 0\n"); return 0; }
            snap_eu[e] = u;
            snap_ev[e] = v;
        }
    }

    n_ = n0;
    for (int e = 0; e < m0; e++) {
        int u = snap_eu[e], v = snap_ev[e];
        if (A_[u][v]) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_) { printf("0 0\n"); return 0; }
        add_edge(u, v);
    }

    /* 2-colour the start graph; an odd cycle means we cannot grow it. */
    for (int i = 0; i < n_; i++) col_[i] = -1;
    int bip = 1;
    for (int s = 0; s < n_ && bip; s++) {
        if (col_[s] >= 0) continue;
        col_[s] = 0;
        int h = 0, t = 0;
        q_[t++] = s;
        while (h < t && bip) {
            int u = q_[h++];
            for (int k = 0; k < deg_[u]; k++) {
                int v = nb_[u][k];
                if (col_[v] < 0) {
                    col_[v] = 1 - col_[u];
                    q_[t++] = v;
                } else if (col_[v] == col_[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }
    if (cost() != 0) { printf("0 0\n"); return 0; }

    save_snap();
    const int ITERS = 1000;
    while (elapsed() < budget_ && n_ + 2 < MAXN) {
        int c = rndi(2);
        attach(c);
        saturate();
        long cur = cost();
        for (int it = 0; it < ITERS && cur > 0; it++) {
            if ((it & 15) == 0 && elapsed() >= budget_) break;
            double T = 0.3 + 3.0 * (1.0 - (double)it / ITERS);
            move_once(T, &cur);
        }
        if (cur == 0) save_snap();
        else load_snap();
    }

    printf("%d %d\n", snap_n, snap_m);
    for (int e = 0; e < snap_m; e++) printf("%d %d\n", snap_eu[e], snap_ev[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every vertex has degree q+1, so with
# d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S such that every
# line holds at most s points of S and every point lies on at most s lines indexed by S.
# For each P in S add an A-vertex joined to the q+1 lines through P; for each j in S add
# a B-vertex joined to the q+1 points on line j. The diameter stays 3.
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
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
        out.append(_arc_graph(m, edges, point_lines, S, line_points))
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
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        deadline = t_start + 0.2 * time_limit
        for n_c, e_c in _arc_extensions(d, deadline, random.Random(seed * 7919 + d)):
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    # New search stage: C vertex insertion with annealing repair, starting from the best graph.
    budget = 0.85 * time_limit - (time.monotonic() - t_start) - 1.5
    if budget >= 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                            stdin_graph=best, timeout=budget + 15.0)
            n2, e2 = lib.parse_graph_text(out)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
