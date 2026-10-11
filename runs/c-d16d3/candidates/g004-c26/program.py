import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Start constructions (Python side). The C engine does the heavy search.
#
# Arc-extended projective plane graphs (diameter 3): start from the incidence
# graph of PG(2, q). Every old vertex has degree q+1, so with d >= q+1 it has
# spare s = d - q - 1. Add an A-vertex per point of SA (joined to the q+1 lines
# through it) and a B-vertex per line of SB (joined to the q+1 points on it),
# where every line meets <= s points of SA and every point lies on <= s lines
# of SB.
#
# Generalized quadrangle W(q) (diameter 4) is the start for D >= 4.
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
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so every target is hit <= s times."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: grow-and-repair search on bipartite graphs.
#
# State: a bipartite graph with fixed sides, possibly with degree excess.
# Cost = (unordered pairs at distance > D) + 3 * (sum of degree excess over d).
# Moves: degree-preserving double-edge swaps and single endpoint moves.
# Simulated annealing repairs the state to cost 0. On success the graph is
# saved as the best valid graph. Growth: add one vertex to the best graph,
# attach it to spare-capacity vertices, anneal again. Repeat until time runs out.
# Output: best valid graph found (or the input graph if none).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 80
#define MAXE (MAXN * MAXDEG / 2 + 16)
#define ITERS 30000

static int d_, D_;
static double budget_;
static clock_t t0_;

static uint64_t rs_ = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0_) / CLOCKS_PER_SEC; }

static int N;
static int side_[MAXN];
static int deg_[MAXN];
static int nb_[MAXN][MAXDEG];
static unsigned char adj_[MAXN][MAXN];
static int S_[2][MAXN];
static int cnt_[2];
static int capdeg_;
static uint64_t BUF_[2][MAXN][MAXW];

static int bestN_ = -1, bestM_ = 0;
static int bu_[MAXE], bv_[MAXE];

static int mv_type, mv_a1, mv_b1, mv_a2, mv_b2;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long eval_cost(void) {
    int w = (N + 63) / 64;
    int cur = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < w; k++) BUF_[0][v][k] = 0;
        BUF_[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < D_; it++) {
        int nx = cur ^ 1;
        for (int v = 0; v < N; v++) {
            uint64_t *dst = BUF_[nx][v];
            const uint64_t *src = BUF_[cur][v];
            for (int k = 0; k < w; k++) dst[k] = src[k];
            for (int i = 0; i < deg_[v]; i++) {
                const uint64_t *o = BUF_[cur][nb_[v][i]];
                for (int k = 0; k < w; k++) dst[k] |= o[k];
            }
        }
        cur = nx;
    }
    long long reach = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < w; k++) reach += popc64(BUF_[cur][v][k]);
    long long bad = ((long long)N * N - reach) / 2;
    long long ex = 0;
    for (int v = 0; v < N; v++)
        if (deg_[v] > d_) ex += deg_[v] - d_;
    return bad + 3 * ex;
}

static void add_edge(int a, int b) {
    adj_[a][b] = 1;
    adj_[b][a] = 1;
    nb_[a][deg_[a]++] = b;
    nb_[b][deg_[b]++] = a;
}

static void del_one(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (nb_[a][i] == b) {
            nb_[a][i] = nb_[a][--deg_[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    adj_[a][b] = 0;
    adj_[b][a] = 0;
    del_one(a, b);
    del_one(b, a);
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg_[v]; i++) adj_[v][nb_[v][i]] = 0;
        deg_[v] = 0;
    }
}

static void rebuild_S(void) {
    cnt_[0] = 0;
    cnt_[1] = 0;
    for (int v = 0; v < N; v++) S_[side_[v]][cnt_[side_[v]]++] = v;
}

static void save_best(void) {
    bestN_ = N;
    bestM_ = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg_[v]; i++) {
            int u = nb_[v][i];
            if (u > v && bestM_ < MAXE) {
                bu_[bestM_] = v;
                bv_[bestM_] = u;
                bestM_++;
            }
        }
    }
}

static void restore_best(void) {
    clear_graph();
    N = bestN_;
    for (int i = 0; i < bestM_; i++) add_edge(bu_[i], bv_[i]);
    rebuild_S();
}

static void add_new_vertex(void) {
    int s = (cnt_[0] <= cnt_[1]) ? 0 : 1;
    int v = N++;
    side_[v] = s;
    deg_[v] = 0;
    memset(adj_[v], 0, (size_t)N);
    for (int u = 0; u < N; u++) adj_[u][v] = 0;
    S_[s][cnt_[s]++] = v;
    int opp = 1 - s;
    int c = cnt_[opp];
    if (c == 0) return;
    int off = rndint(c);
    int want = d_ < c ? d_ : c;
    for (int pass = 0; pass < 2 && deg_[v] < want; pass++) {
        for (int j = 0; j < c && deg_[v] < want; j++) {
            int x = S_[opp][(off + j) % c];
            if (adj_[v][x]) continue;
            if (deg_[x] >= capdeg_) continue;
            if (pass == 0 && deg_[x] >= d_) continue;
            add_edge(v, x);
        }
    }
}

static int do_swap(void) {
    if (cnt_[0] == 0) return 0;
    int a1 = S_[0][rndint(cnt_[0])];
    int a2 = S_[0][rndint(cnt_[0])];
    if (a1 == a2 || deg_[a1] == 0 || deg_[a2] == 0) return 0;
    int b1 = nb_[a1][rndint(deg_[a1])];
    int b2 = nb_[a2][rndint(deg_[a2])];
    if (b1 == b2 || adj_[a1][b2] || adj_[a2][b1]) return 0;
    del_edge(a1, b1);
    del_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    mv_type = 1;
    mv_a1 = a1; mv_b1 = b1; mv_a2 = a2; mv_b2 = b2;
    return 1;
}

static void undo_swap(void) {
    del_edge(mv_a1, mv_b2);
    del_edge(mv_a2, mv_b1);
    add_edge(mv_a1, mv_b1);
    add_edge(mv_a2, mv_b2);
}

static int do_endpoint(void) {
    if (cnt_[0] == 0 || cnt_[1] == 0) return 0;
    int s = rndint(2);
    int x = S_[s][rndint(cnt_[s])];
    if (deg_[x] == 0) return 0;
    int y = nb_[x][rndint(deg_[x])];
    int z = S_[1 - s][rndint(cnt_[1 - s])];
    if (z == y || adj_[x][z] || deg_[z] >= capdeg_) return 0;
    del_edge(x, y);
    add_edge(x, z);
    mv_type = 2;
    mv_a1 = x; mv_b1 = y; mv_b2 = z;
    return 1;
}

static void undo_endpoint(void) {
    del_edge(mv_a1, mv_b2);
    add_edge(mv_a1, mv_b1);
}

static int anneal(long long iters, double T0, double T1) {
    long long cost = eval_cost();
    for (long long it = 0; it < iters; it++) {
        if (cost == 0) return 1;
        if ((it & 63) == 0 && elapsed() > budget_) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int ok;
        int type;
        if (rnd01() < 0.5) {
            ok = do_swap();
            type = 1;
        } else {
            ok = do_endpoint();
            type = 2;
        }
        if (!ok) continue;
        long long c2 = eval_cost();
        long long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else if (type == 1) {
            undo_swap();
        } else {
            undo_endpoint();
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    budget_ = atof(argv[4]);
    rs_ ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 10; i++) rnd64();
    capdeg_ = d_ + 6;
    if (capdeg_ > MAXDEG - 2) capdeg_ = MAXDEG - 2;
    t0_ = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (m0 < 0) m0 = 0;
    int *iu = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
    int m_read = 0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        iu[m_read] = a;
        iv[m_read] = b;
        m_read++;
    }

    int ok = 0;
    N = 0;
    if (d_ < 1) {
        ok = 0;
    } else if (n0 == 0) {
        N = 2 * d_;
        if (N <= MAXN - 400) {
            for (int i = 0; i < d_; i++) side_[i] = 0;
            for (int j = 0; j < d_; j++) side_[d_ + j] = 1;
            for (int i = 0; i < d_; i++)
                for (int j = 0; j < d_; j++) add_edge(i, d_ + j);
            ok = 1;
        }
    } else if (n0 > 0 && n0 <= MAXN - 400) {
        N = n0;
        for (int v = 0; v < N; v++) { deg_[v] = 0; }
        memset(adj_, 0, sizeof(adj_));
        for (int i = 0; i < m_read; i++) {
            int a = iu[i], b = iv[i];
            if (a < 0 || b < 0 || a >= N || b >= N || a == b) continue;
            if (adj_[a][b]) continue;
            if (deg_[a] >= MAXDEG - 1 || deg_[b] >= MAXDEG - 1) continue;
            add_edge(a, b);
        }
        int col[MAXN];
        for (int v = 0; v < N; v++) col[v] = -1;
        int *stack = (int *)malloc(sizeof(int) * (size_t)(N + 1));
        int bip = 1;
        for (int s = 0; s < N && bip; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int sp = 0;
            stack[sp++] = s;
            while (sp > 0 && bip) {
                int u = stack[--sp];
                for (int i = 0; i < deg_[u]; i++) {
                    int w = nb_[u][i];
                    if (col[w] == -1) {
                        col[w] = 1 - col[u];
                        stack[sp++] = w;
                    } else if (col[w] == col[u]) {
                        bip = 0;
                        break;
                    }
                }
            }
        }
        free(stack);
        if (bip) {
            for (int v = 0; v < N; v++) side_[v] = col[v];
            ok = 1;
        }
    }

    if (ok) {
        rebuild_S();
        if (cnt_[0] == 0 || cnt_[1] == 0) {
            ok = 0;
        }
    }

    if (ok) {
        if (eval_cost() == 0) save_best();
        int have = (bestN_ >= 0);
        while (elapsed() < budget_) {
            if (!have) {
                if (anneal(ITERS * 4, 3.0, 0.2)) {
                    save_best();
                    have = 1;
                }
                continue;
            }
            if (bestN_ + 2 >= MAXN) break;
            restore_best();
            add_new_vertex();
            if (anneal(ITERS, 2.5, 0.2)) save_best();
        }
        if (have) {
            printf("%d %d\n", bestN_, bestM_);
            for (int i = 0; i < bestM_; i++) printf("%d %d\n", bu_[i], bv_[i]);
            free(iu);
            free(iv);
            return 0;
        }
    }

    printf("%d %d\n", n0, m_read);
    for (int i = 0; i < m_read; i++) printf("%d %d\n", iu[i], iv[i]);
    free(iu);
    free(iv);
    return 0;
}
"""


def _c_search(d, D, seed, start, budget):
    """Run the C grow-and-repair engine from `start` for about `budget` seconds."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                     stdin_graph=start, timeout=budget + 6.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end_by = t_start + 0.85 * time_limit

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

    # Diameter 3 start: arc-extended projective plane graphs.
    if D >= 3:
        deadline = t_start + 0.25 * time_limit
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Diameter 4 start: generalized quadrangle.
    if D >= 4 and time.monotonic() < t_start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Search: grow-and-repair in C, starting from the best valid graph.
    # Skip when the Moore bound is already reached (e.g. d3D3 = 14).
    if best_n < lib.moore_bound(d, D):
        budget = end_by - time.monotonic() - 2.0
        if budget > 1.0:
            try:
                n2, e2 = _c_search(d, D, seed, best, budget)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
