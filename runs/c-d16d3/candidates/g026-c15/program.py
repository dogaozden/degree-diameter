import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: bipartite annealing with vertex growth.
#
# State: a bipartite graph (sides fixed per vertex) with max degree d.
# Cost: number of unordered vertex pairs at distance > D (unreachable counts).
# Moves (all keep bipartiteness and degree <= d):
#   swap      - degree-preserving double edge swap across the bipartition
#   transfer  - move one endpoint of an edge to another same-side vertex with spare degree
#   add       - add an edge between spare-degree vertices on opposite sides
#   remove    - delete a random edge (rarely, for escape)
# When cost reaches 0 the state is valid: save it, then add one new vertex
# (greedily joined to spare opposite-side vertices) and keep annealing.
# If a size stalls, restart from the best valid graph with a new random vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1024
#define DMAX 128
#define EMAX (NMAX * DMAX / 2 + 16)
#define LOGMAX 16
#define STALL 1500

static int d_ = 0, D_ = 0;
static int n_ = 0, m_ = 0;
static int side_[NMAX];
static int deg_[NMAX];
static int adj_[NMAX][DMAX];
static int eidx_[NMAX][NMAX];
static int Ea_[EMAX], Eb_[EMAX];
static int best_n_ = 0, best_m_ = 0;
static int bestEa_[EMAX], bestEb_[EMAX];

static int st_[NMAX], dist_[NMAX], qu_[NMAX], cs_ = 0;
static int lt_[LOGMAX], la_[LOGMAX], lb_[LOGMAX], ln_ = 0;
static int cand_[NMAX], candB_[NMAX];
static uint64_t rs_ = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double runif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) { return eidx_[a][b] >= 0; }

static void remove_from(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (adj_[a][i] == b) {
            adj_[a][i] = adj_[a][--deg_[a]];
            return;
        }
    }
}

static void add_edge(int a, int b) {
    eidx_[a][b] = eidx_[b][a] = m_;
    Ea_[m_] = a;
    Eb_[m_] = b;
    m_++;
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}

static void remove_edge(int a, int b) {
    int k = eidx_[a][b], last = m_ - 1;
    if (k != last) {
        Ea_[k] = Ea_[last];
        Eb_[k] = Eb_[last];
        eidx_[Ea_[k]][Eb_[k]] = eidx_[Eb_[k]][Ea_[k]] = k;
    }
    m_--;
    eidx_[a][b] = eidx_[b][a] = -1;
    remove_from(a, b);
    remove_from(b, a);
}

/* logged operations, so a rejected move can be undone */
static void op_add(int a, int b) {
    add_edge(a, b);
    lt_[ln_] = 0; la_[ln_] = a; lb_[ln_] = b; ln_++;
}

static void op_rem(int a, int b) {
    remove_edge(a, b);
    lt_[ln_] = 1; la_[ln_] = a; lb_[ln_] = b; ln_++;
}

static void undo_log(void) {
    while (ln_ > 0) {
        ln_--;
        if (lt_[ln_] == 0) remove_edge(la_[ln_], lb_[ln_]);
        else add_edge(la_[ln_], lb_[ln_]);
    }
}

/* number of unordered pairs at distance > D_ (unreachable pairs included) */
static long long bad_count(void) {
    long long total = 0;
    for (int s = 0; s < n_; s++) {
        cs_++;
        int h = 0, t = 0;
        qu_[t++] = s;
        st_[s] = cs_;
        dist_[s] = 0;
        while (h < t) {
            int u = qu_[h++];
            if (dist_[u] >= D_) continue;
            for (int i = 0; i < deg_[u]; i++) {
                int v = adj_[u][i];
                if (st_[v] != cs_) {
                    st_[v] = cs_;
                    dist_[v] = dist_[u] + 1;
                    qu_[t++] = v;
                }
            }
        }
        total += n_ - t;
    }
    return total / 2;
}

static void move_swap(void) {
    if (m_ < 2) return;
    int i = rint_(m_), j = rint_(m_);
    if (i == j) return;
    int a1 = Ea_[i], b1 = Eb_[i], a2 = Ea_[j], b2 = Eb_[j];
    if (a1 == a2 || b1 == b2) return;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return;
    op_rem(a1, b1);
    op_rem(a2, b2);
    op_add(a1, b2);
    op_add(a2, b1);
}

static void move_transfer(void) {
    if (m_ < 1) return;
    int i = rint_(m_);
    int a = Ea_[i], b = Eb_[i];
    int cnt = 0;
    if (runif() < 0.5) {
        for (int x = 0; x < n_; x++)
            if (side_[x] == 0 && x != a && deg_[x] < d_ && !has_edge(x, b)) cand_[cnt++] = x;
        if (cnt == 0) return;
        int x = cand_[rint_(cnt)];
        op_rem(a, b);
        op_add(x, b);
    } else {
        for (int y = 0; y < n_; y++)
            if (side_[y] == 1 && y != b && deg_[y] < d_ && !has_edge(a, y)) cand_[cnt++] = y;
        if (cnt == 0) return;
        int y = cand_[rint_(cnt)];
        op_rem(a, b);
        op_add(a, y);
    }
}

static void move_add(void) {
    int ca = 0, cb = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] < d_) {
            if (side_[v] == 0) cand_[ca++] = v;
            else candB_[cb++] = v;
        }
    }
    if (ca == 0 || cb == 0) return;
    for (int t = 0; t < 20; t++) {
        int a = cand_[rint_(ca)], b = candB_[rint_(cb)];
        if (!has_edge(a, b)) {
            op_add(a, b);
            return;
        }
    }
}

static void move_remove(void) {
    if (m_ < 1) return;
    int i = rint_(m_);
    op_rem(Ea_[i], Eb_[i]);
}

static void save_best(void) {
    if (n_ <= best_n_) return;
    best_n_ = n_;
    best_m_ = m_;
    memcpy(bestEa_, Ea_, sizeof(int) * (size_t)m_);
    memcpy(bestEb_, Eb_, sizeof(int) * (size_t)m_);
}

static void restore_best(void) {
    while (m_ > 0) remove_edge(Ea_[m_ - 1], Eb_[m_ - 1]);
    n_ = best_n_;
    for (int k = 0; k < best_m_; k++) add_edge(bestEa_[k], bestEb_[k]);
}

/* append a vertex on the side that most needs partners, join it greedily */
static void grow_state(void) {
    if (n_ >= NMAX - 2) return;
    int spA = 0, spB = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] < d_) {
            if (side_[v] == 0) spA += d_ - deg_[v];
            else spB += d_ - deg_[v];
        }
    }
    int s;
    if (spA + spB == 0) s = rint_(2);
    else s = (rint_(spA + spB) < spB) ? 0 : 1;
    int x = n_++;
    side_[x] = s;
    deg_[x] = 0;
    int cnt = 0;
    for (int v = 0; v < x; v++)
        if (side_[v] != s && deg_[v] < d_) cand_[cnt++] = v;
    for (int i = cnt - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int tmp = cand_[i];
        cand_[i] = cand_[j];
        cand_[j] = tmp;
    }
    for (int i = 0; i < cnt && deg_[x] < d_; i++) {
        int y = cand_[i];
        if (deg_[y] >= d_ || has_edge(x, y)) continue;
        int a = (s == 0) ? x : y;
        int b = (s == 0) ? y : x;
        add_edge(a, b);
    }
}

static int load_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > NMAX - 4 || m < 0 || m > EMAX) return 0;
    static int ua[EMAX], ub[EMAX];
    for (int k = 0; k < m; k++) {
        if (scanf("%d %d", &ua[k], &ub[k]) != 2) return 0;
        if (ua[k] < 0 || ua[k] >= n || ub[k] < 0 || ub[k] >= n || ua[k] == ub[k]) return 0;
    }
    int col[NMAX];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int v = 0; v < n; v++) {
        if (col[v] >= 0) continue;
        col[v] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int k = 0; k < m; k++) {
                int u = ua[k], w = ub[k];
                if (col[u] >= 0 && col[w] < 0) { col[w] = 1 - col[u]; changed = 1; }
                else if (col[w] >= 0 && col[u] < 0) { col[u] = 1 - col[w]; changed = 1; }
            }
        }
    }
    for (int k = 0; k < m; k++)
        if (col[ua[k]] == col[ub[k]]) return 0;
    n_ = n;
    for (int v = 0; v < n; v++) {
        side_[v] = col[v];
        deg_[v] = 0;
    }
    for (int k = 0; k < m; k++) {
        int a = (col[ua[k]] == 0) ? ua[k] : ub[k];
        int b = (col[ua[k]] == 0) ? ub[k] : ua[k];
        if (has_edge(a, b)) continue;
        if (deg_[a] >= d_ || deg_[b] >= d_) return 0;
        add_edge(a, b);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    double limit = atof(argv[4]);
    if (d_ < 1 || D_ < 1 || d_ >= DMAX) {
        printf("0 0\n");
        return 0;
    }
    memset(eidx_, 0xff, sizeof(eidx_));
    if (!load_input()) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    long long cur = bad_count();
    double T0 = 2.0, T1 = 0.15, T = T0;
    long long iter = 0;
    int since = 0;
    double elapsed = 0.0;

    while (1) {
        if ((iter & 31) == 0) {
            elapsed = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (elapsed >= limit) break;
            double frac = elapsed / limit;
            T = T0 * pow(T1 / T0, frac);
        }
        iter++;
        since++;

        if (cur == 0) {
            save_best();
            if (n_ >= NMAX - 3) break;
            grow_state();
            cur = bad_count();
            since = 0;
            continue;
        }
        if (since > STALL) {
            since = 0;
            if (best_n_ > 0) {
                restore_best();
                grow_state();
                cur = bad_count();
                continue;
            }
        }

        ln_ = 0;
        int r = rint_(100);
        if (r < 40) move_swap();
        else if (r < 75) move_transfer();
        else if (r < 97) move_add();
        else move_remove();
        if (ln_ == 0) continue;

        long long nb = bad_count();
        long long delta = nb - cur;
        if (delta <= 0 || runif() < exp(-(double)delta / T)) cur = nb;
        else undo_log();
    }

    if (best_n_ == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n_, best_m_);
    for (int k = 0; k < best_m_; k++) printf("%d %d\n", bestEa_[k], bestEb_[k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. A new vertex on the A-side joins
# all q+1 lines through a chosen point (each line may serve <= s A-vertices);
# symmetrically for the B-side. Diameter stays 3.
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
# Build: best algebraic start, then the C annealing engine grows it.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
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

    if D >= 3:
        cands = _arc_extensions(d, t_start + 0.3 * time_limit,
                                random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases already at the Moore bound cannot be improved.
    if best_n >= lib.moore_bound(d, D):
        return best

    elapsed = time.monotonic() - t_start
    budget = 0.80 * time_limit - elapsed - 2.5
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 20.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
