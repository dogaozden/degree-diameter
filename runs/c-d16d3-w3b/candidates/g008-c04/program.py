import random
import time

import lib


# Native search engine. Starts from a valid bipartite graph and runs an
# iterated local search that only accepts valid graphs, checked exactly.
#
# New idea in this version: "insertion with ball cover". A new vertex x on
# side c is joined to a set T of spare-degree vertices on the other side,
# chosen greedily so that the radius-(D-1) balls of T cover every existing
# vertex. Adding vertices and edges never increases distances between old
# vertices, so only x's reachability needs checking. The search perturbs an
# accepted state by deleting a few random edges, re-inserts vertices, and
# re-saturates spare cross edges. It keeps the state only if the vertex count
# does not drop and a full diameter check passes.
C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int d_, D_, n_, cap_;
static int *adj_, *deg_, *sadj_, *sdeg_, *badj_, *bdeg_;
static int sn_, bn_;
static unsigned char *col_;
static int *dist_, *queue_, *mk_, *qb_, *db_;
static int stamp_ = 0;
static unsigned char *unc_;
static int *cands_, *chosen_, *sp0_, *sp1_;
static int left_;
static uint64_t rs_ = 88172645463325252ULL;
static double t_end_;

static uint64_t rnd_(void) {
    rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17;
    return rs_;
}
static int rint_(int k) { return k <= 1 ? 0 : (int)(rnd_() % (uint64_t)k); }
static double now_(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg_[u]; k++)
        if (adj_[u * d_ + k] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    adj_[u * d_ + deg_[u]++] = v;
    adj_[v * d_ + deg_[v]++] = u;
}
static void rm_from(int u, int v) {
    for (int k = 0; k < deg_[u]; k++)
        if (adj_[u * d_ + k] == v) {
            adj_[u * d_ + k] = adj_[u * d_ + deg_[u] - 1];
            deg_[u]--;
            return;
        }
}
static void del_edge(int u, int v) { rm_from(u, v); rm_from(v, u); }

static void shuffle_(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static int color_graph(void) {
    for (int v = 0; v < n_; v++) col_[v] = 2;
    for (int s = 0; s < n_; s++) {
        if (col_[s] != 2) continue;
        col_[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < deg_[u]; k++) {
                int v = adj_[u * d_ + k];
                if (col_[v] == 2) { col_[v] = 1 - col_[u]; queue_[t++] = v; }
                else if (col_[v] == col_[u]) return 0;
            }
        }
    }
    return 1;
}

static int reach_count(int s) {
    for (int i = 0; i < n_; i++) dist_[i] = -1;
    int h = 0, t = 0;
    queue_[t++] = s;
    dist_[s] = 0;
    while (h < t) {
        int u = queue_[h++];
        if (dist_[u] >= D_) continue;
        for (int k = 0; k < deg_[u]; k++) {
            int v = adj_[u * d_ + k];
            if (dist_[v] < 0) { dist_[v] = dist_[u] + 1; queue_[t++] = v; }
        }
    }
    return t;
}

static int full_valid(void) {
    for (int s = 0; s < n_; s++)
        if (reach_count(s) != n_) return 0;
    return 1;
}

/* BFS ball of radius r around s. Counts uncovered old vertices in it;
   if mode == 1 they are marked covered. */
static int ball_apply(int s, int r, int mode) {
    stamp_++;
    int h = 0, t = 0, g = 0;
    qb_[t] = s; db_[t] = 0; t++;
    mk_[s] = stamp_;
    while (h < t) {
        int u = qb_[h], du = db_[h];
        h++;
        if (unc_[u]) {
            g++;
            if (mode) { unc_[u] = 0; left_--; }
        }
        if (du >= r) continue;
        for (int k = 0; k < deg_[u]; k++) {
            int v = adj_[u * d_ + k];
            if (mk_[v] != stamp_) {
                mk_[v] = stamp_;
                qb_[t] = v; db_[t] = du + 1; t++;
            }
        }
    }
    return g;
}

/* Insert a new vertex on side c. Its neighbourhood is chosen greedily so the
   radius-(D-1) balls cover all old vertices; accepted only if it reaches all. */
static int try_insert(int c) {
    if (n_ >= cap_) return 0;
    int nold = n_, x = n_;
    int nc = 0;
    for (int v = 0; v < nold; v++) {
        unc_[v] = 1;
        if (col_[v] != c && deg_[v] < d_) cands_[nc++] = v;
    }
    left_ = nold;
    int r = D_ - 1, nch = 0;
    while (left_ > 0 && nch < d_) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int t = cands_[i];
            if (deg_[t] >= d_) continue;
            int g = ball_apply(t, r, 0);
            if (g > bg) { bg = g; best = t; }
            else if (g == bg && g > 0 && rint_(2) == 0) best = t;
        }
        if (best < 0) break;
        chosen_[nch++] = best;
        ball_apply(best, r, 1);
    }
    if (left_ > 0) return 0;
    col_[x] = (unsigned char)c;
    deg_[x] = 0;
    n_++;
    for (int j = 0; j < nch; j++) add_edge(x, chosen_[j]);
    if (reach_count(x) == n_) return 1;
    for (int j = 0; j < nch; j++) del_edge(x, chosen_[j]);
    deg_[x] = 0;
    n_--;
    return 0;
}

/* Add random cross edges between spare-degree vertices of opposite colours. */
static void cross_fill(void) {
    int a0 = 0, a1 = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] >= d_) continue;
        if (col_[v] == 0) sp0_[a0++] = v; else sp1_[a1++] = v;
    }
    shuffle_(sp0_, a0);
    shuffle_(sp1_, a1);
    for (int i = 0; i < a0; i++) {
        int a = sp0_[i];
        for (int j = 0; j < a1 && deg_[a] < d_; j++) {
            int b = sp1_[j];
            if (deg_[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void save_state(void) {
    sn_ = n_;
    memcpy(sadj_, adj_, sizeof(int) * (size_t)n_ * d_);
    memcpy(sdeg_, deg_, sizeof(int) * (size_t)n_);
}
static void restore_state(void) {
    n_ = sn_;
    memcpy(adj_, sadj_, sizeof(int) * (size_t)n_ * d_);
    memcpy(deg_, sdeg_, sizeof(int) * (size_t)n_);
}
static void save_best(void) {
    bn_ = n_;
    memcpy(badj_, adj_, sizeof(int) * (size_t)n_ * d_);
    memcpy(bdeg_, deg_, sizeof(int) * (size_t)n_);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs_) rs_ = 1;
    double budget = atof(argv[4]);
    t_end_ = now_() + budget;

    if (d_ < 1 || D_ < 1) { printf("1 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 == 0) {
        if (D_ == 1) { printf("2 1\n0 1\n"); return 0; }
        n0 = 2 * d_;
        m0 = d_ * d_;
    }
    int ecap = (m0 > d_ * d_ ? m0 : d_ * d_) + 1;
    int *eu = malloc(sizeof(int) * (size_t)ecap);
    int *ev = malloc(sizeof(int) * (size_t)ecap);
    int ne = 0;
    /* Re-read: the first branch needs K_{d,d} when input was empty. */
    {
        /* If the original input was empty, scanf returned nothing, so build K_{d,d}. */
        int given = (m0 == d_ * d_ && n0 == 2 * d_);
        (void)given;
    }
    if (n0 == 2 * d_ && m0 == d_ * d_) {
        /* Input may be K_{d,d} from the generator, or empty; both are handled as K_{d,d}. */
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++) {
                eu[ne] = i; ev[ne] = d_ + j; ne++;
            }
    } else {
        for (int i = 0; i < m0; i++) {
            int a, b;
            if (scanf("%d %d", &a, &b) != 2) break;
            if (ne < ecap) { eu[ne] = a; ev[ne] = b; ne++; }
        }
    }

    cap_ = n0 + n0 / 2 + 64;
    adj_ = calloc((size_t)cap_ * d_, sizeof(int));
    sadj_ = calloc((size_t)cap_ * d_, sizeof(int));
    badj_ = calloc((size_t)cap_ * d_, sizeof(int));
    deg_ = calloc((size_t)cap_, sizeof(int));
    sdeg_ = calloc((size_t)cap_, sizeof(int));
    bdeg_ = calloc((size_t)cap_, sizeof(int));
    col_ = calloc((size_t)cap_, 1);
    dist_ = calloc((size_t)cap_, sizeof(int));
    queue_ = calloc((size_t)cap_, sizeof(int));
    mk_ = calloc((size_t)cap_, sizeof(int));
    qb_ = calloc((size_t)cap_, sizeof(int));
    db_ = calloc((size_t)cap_, sizeof(int));
    unc_ = calloc((size_t)cap_, 1);
    cands_ = calloc((size_t)cap_, sizeof(int));
    chosen_ = calloc((size_t)d_ + 2, sizeof(int));
    sp0_ = calloc((size_t)cap_, sizeof(int));
    sp1_ = calloc((size_t)cap_, sizeof(int));

    n_ = n0;
    for (int i = 0; i < ne; i++) {
        int u = eu[i], v = ev[i];
        if (u == v || u < 0 || v < 0 || u >= n0 || v >= n0) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    int ok = color_graph() && full_valid();
    save_best();

    if (ok && D_ >= 2) {
        cross_fill();
        if (n_ > bn_) save_best();
        while (now_() < t_end_) {
            save_state();
            int r = 1 + rint_(3);
            for (int q = 0; q < r; q++) {
                int v = rint_(n_);
                if (deg_[v] == 0) continue;
                int u = adj_[v * d_ + rint_(deg_[v])];
                del_edge(v, u);
            }
            for (int q = 0; q < 3; q++) try_insert(rint_(2));
            cross_fill();
            for (int q = 0; q < 2; q++) try_insert(rint_(2));
            cross_fill();
            if (n_ >= sn_ && full_valid()) {
                if (n_ > bn_) save_best();
            } else {
                restore_state();
            }
        }
    }

    int m = 0;
    for (int u = 0; u < bn_; u++)
        for (int k = 0; k < bdeg_[u]; k++)
            if (badj_[u * d_ + k] > u) m++;
    printf("%d %d\n", bn_, m);
    for (int u = 0; u < bn_; u++)
        for (int k = 0; k < bdeg_[u]; k++) {
            int v = badj_[u * d_ + k];
            if (v > u) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line holding <= s points of S and every point on <= s lines
# indexed by S. For each P in S add an A-vertex joined to the q+1 lines
# through P; for each j in S add a B-vertex joined to the q+1 points on j.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
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


def _greedy_arc(m, s, point_lines, line_points, rng, trials):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
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
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _arc_extensions(d, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d, 24)):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40))
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    # Arc-extended projective plane graphs (diameter 3): start point for the search.
    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        for n_c, e_c in _arc_extensions(d, rng):
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)

    elapsed = time.monotonic() - t0
    budget = max(0.5, 0.75 * time_limit - elapsed - 1.0)
    timeout = max(1.0, 0.92 * time_limit - elapsed)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=best, timeout=timeout)
        n, e = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
