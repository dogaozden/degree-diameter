import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: growth by vertex insertion, repaired by simulated annealing.
#
# State: a bipartite graph with max degree d and "bad pairs" = pairs at
# distance > D (bitset balls, recomputed per move). Each growth step adds one
# vertex whose neighbourhood greedily covers old vertices by R-balls (R = D-1),
# with the new vertex kept as a "pivot" so reattach moves can pull edges onto
# it. Annealing uses degree-preserving 2-switches, endpoint reattachments and
# spare-spare edge additions. A zero-cost state is snapshotted; a failed
# attempt restores the last valid snapshot and retries with more iterations.
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
#define MAXD 64
#define MAXW (MAXN / 64)

typedef uint64_t Bits[MAXW];

static int dmax_, R_, n_, pivot_ = -1;
static int col_[MAXN], deg_[MAXN], adj_[MAXN][MAXD];
static Bits bufA[MAXN], bufB[MAXN];

static int snap_n_, snap_col_[MAXN], snap_deg_[MAXN], snap_adj_[MAXN][MAXD];

static uint64_t rs_ = 88172645463325252ULL;
static double t_origin_, budget_;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17;
    return rs_;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec - t_origin_;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* balls(R)[v] = bitset of vertices within distance R of v. */
static Bits *balls(int R) {
    Bits *cur = bufA, *nxt = bufB;
    int W = (n_ + 63) >> 6;
    for (int v = 0; v < n_; v++) {
        memset(cur[v], 0, sizeof(Bits));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n_; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * W);
            for (int i = 0; i < deg_[v]; i++) {
                const uint64_t *src = cur[adj_[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        Bits *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

static long long bad_pairs(void) {
    Bits *b = balls(R_);
    int W = (n_ + 63) >> 6;
    long long bad = 0;
    for (int v = 0; v < n_; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(b[v][w]);
        bad += n_ - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) if (adj_[a][i] == b) return 1;
    return 0;
}
static void arc_add(int a, int b) { adj_[a][deg_[a]++] = b; }
static void arc_del(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (adj_[a][i] == b) { adj_[a][i] = adj_[a][--deg_[a]]; return; }
    }
}
static void edge_add(int a, int b) { arc_add(a, b); arc_add(b, a); }
static void edge_del(int a, int b) { arc_del(a, b); arc_del(b, a); }

typedef struct {
    int nd, da[2], db[2];
    int na, aa[2], ab[2];
} Move;

static void apply_move(const Move *mv) {
    for (int i = 0; i < mv->nd; i++) edge_del(mv->da[i], mv->db[i]);
    for (int i = 0; i < mv->na; i++) edge_add(mv->aa[i], mv->ab[i]);
}
static void undo_move(const Move *mv) {
    for (int i = 0; i < mv->na; i++) edge_del(mv->aa[i], mv->ab[i]);
    for (int i = 0; i < mv->nd; i++) edge_add(mv->da[i], mv->db[i]);
}

/* Random edge oriented as (a in colour 0, b in colour 1). */
static int rand_edge(int *a, int *b) {
    for (int t = 0; t < 50; t++) {
        int v = rndint(n_);
        if (!deg_[v]) continue;
        int u = adj_[v][rndint(deg_[v])];
        if (col_[v] == 0) { *a = v; *b = u; } else { *a = u; *b = v; }
        return 1;
    }
    return 0;
}

static int rand_spare(int side, int exclude) {
    for (int t = 0; t < 400; t++) {
        int v = rndint(n_);
        if (v != exclude && col_[v] == side && deg_[v] < dmax_) return v;
    }
    return -1;
}

static int propose(Move *mv) {
    int a1, b1, a2, b2, x, y, t;
    mv->nd = 0; mv->na = 0;
    int r = rndint(100);
    if (r < 45) {  /* degree-preserving 2-switch */
        if (!rand_edge(&a1, &b1) || !rand_edge(&a2, &b2)) return 0;
        if (a1 == a2 || b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) return 0;
        mv->nd = 2; mv->da[0] = a1; mv->db[0] = b1; mv->da[1] = a2; mv->db[1] = b2;
        mv->na = 2; mv->aa[0] = a1; mv->ab[0] = b2; mv->aa[1] = a2; mv->ab[1] = b1;
        return 1;
    }
    if (r < 85) {  /* reattach one endpoint of an edge, possibly onto the pivot */
        if (!rand_edge(&a1, &b1)) return 0;
        int use_pivot = (pivot_ >= 0 && deg_[pivot_] < dmax_ && pivot_ != a1 &&
                         pivot_ != b1 && rnd01() < 0.5);
        int keep_a = (rnd01() < 0.5);
        if (use_pivot) keep_a = (col_[pivot_] == 1);
        if (keep_a) {
            t = use_pivot ? pivot_ : rand_spare(1, b1);
            if (t < 0 || t == b1 || has_edge(a1, t)) return 0;
            mv->nd = 1; mv->da[0] = a1; mv->db[0] = b1;
            mv->na = 1; mv->aa[0] = a1; mv->ab[0] = t;
        } else {
            t = use_pivot ? pivot_ : rand_spare(0, a1);
            if (t < 0 || t == a1 || has_edge(t, b1)) return 0;
            mv->nd = 1; mv->da[0] = a1; mv->db[0] = b1;
            mv->na = 1; mv->aa[0] = t; mv->ab[0] = b1;
        }
        return 1;
    }
    /* add an edge between two spare vertices */
    x = rand_spare(0, -1);
    y = rand_spare(1, -1);
    if (x < 0 || y < 0 || has_edge(x, y)) return 0;
    mv->na = 1; mv->aa[0] = x; mv->ab[0] = y;
    return 1;
}

/* Metropolis annealing on bad-pair count. Returns 1 if a valid state is reached. */
static int anneal(long long iters, double T0, double T1) {
    long long cur = bad_pairs();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if (elapsed() > budget_) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        Move mv;
        if (!propose(&mv)) continue;
        apply_move(&mv);
        long long nw = bad_pairs();
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nw;
        else undo_move(&mv);
    }
    return cur == 0;
}

/* Insert vertex n_ on colour `side`, greedily covering old vertices by (R-1)-balls. */
static void grow_vertex(int side) {
    int n = n_;
    int W = (n + 63) >> 6;
    Bits *b = balls(R_ - 1);
    Bits unc;
    memset(unc, 0, sizeof(Bits));
    for (int v = 0; v < n; v++) unc[v >> 6] |= 1ULL << (v & 63);
    int chosen[MAXD], nc = 0;
    while (nc < dmax_) {
        int anyleft = 0;
        for (int w = 0; w < W; w++) if (unc[w]) { anyleft = 1; break; }
        if (!anyleft) break;
        int best = -1, bestg = 0;
        int start = rndint(n);
        for (int k = 0; k < n; k++) {
            int u = (start + k) % n;
            if (col_[u] == side || deg_[u] >= dmax_) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(b[u][w] & unc[w]);
            if (g > bestg) { bestg = g; best = u; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) unc[w] &= ~b[best][w];
    }
    int w = n;
    col_[w] = side;
    deg_[w] = 0;
    n_ = n + 1;
    for (int i = 0; i < nc; i++) edge_add(w, chosen[i]);
    pivot_ = w;
}

static void save_snap(void) {
    snap_n_ = n_;
    memcpy(snap_col_, col_, sizeof(int) * n_);
    memcpy(snap_deg_, deg_, sizeof(int) * n_);
    memcpy(snap_adj_, adj_, sizeof(int) * MAXD * n_);
}

static void restore_snap(void) {
    n_ = snap_n_;
    memcpy(col_, snap_col_, sizeof(int) * n_);
    memcpy(deg_, snap_deg_, sizeof(int) * n_);
    memcpy(adj_, snap_adj_, sizeof(int) * MAXD * n_);
}

static void print_snap(void) {
    long long m = 0;
    for (int v = 0; v < snap_n_; v++) if (snap_col_[v] == 0) m += snap_deg_[v];
    printf("%d %lld\n", snap_n_, m);
    for (int v = 0; v < snap_n_; v++) {
        if (snap_col_[v] != 0) continue;
        for (int i = 0; i < snap_deg_[v]; i++) printf("%d %d\n", v, snap_adj_[v][i]);
    }
    fflush(stdout);
}

int main(int argc, char **argv) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    t_origin_ = (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    R_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget_ = atof(argv[4]);
    dmax_ = d;
    rs_ = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    rs_ |= 1;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n >= MAXN - 2 || d < 1 || d > MAXD || R_ < 1) {
        printf("0 0\n");
        return 0;
    }
    n_ = n;
    for (int i = 0; i < n; i++) { deg_[i] = 0; col_[i] = -1; }
    int bad_input = 0;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) { bad_input = 1; break; }
        if (a < 0 || a >= n || b < 0 || b >= n || a == b ||
            deg_[a] >= d || deg_[b] >= d || has_edge(a, b)) { bad_input = 1; break; }
        edge_add(a, b);
    }
    if (!bad_input) {
        int *q = malloc(sizeof(int) * n);
        for (int s = 0; s < n && !bad_input; s++) {
            if (col_[s] >= 0) continue;
            col_[s] = 0;
            int head = 0, tail = 0;
            q[tail++] = s;
            while (head < tail && !bad_input) {
                int u = q[head++];
                for (int i = 0; i < deg_[u]; i++) {
                    int v = adj_[u][i];
                    if (col_[v] < 0) { col_[v] = 1 - col_[u]; q[tail++] = v; }
                    else if (col_[v] == col_[u]) bad_input = 1;
                }
            }
        }
        free(q);
    }
    if (bad_input) {
        printf("0 0\n");
        return 0;
    }

    int ok = (bad_pairs() == 0);
    save_snap();
    if (!ok) {
        ok = anneal(400000, 1.0, 0.05);
        if (ok) save_snap(); else restore_snap();
    }

    if (ok) {
        long long iters = 3000;
        int fails = 0;
        while (elapsed() < budget_ && snap_n_ < MAXN - 2) {
            grow_vertex(rndint(2));
            int got = anneal(iters, 1.0, 0.05);
            pivot_ = -1;
            if (got) {
                save_snap();
                iters = 3000;
                fails = 0;
            } else {
                restore_snap();
                if (++fails % 3 == 0 && iters < 40000) iters += 2000;
            }
        }
    }
    print_snap();
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Build: best constructed start, then C growth and repair.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
        arcs = _arc_extensions(d, start + 0.08 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.15 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C growth and repair from the best start found so far.
    if d <= 60 and D >= 2:
        remaining = 0.9 * time_limit - (time.monotonic() - start)
        budget = remaining - 2.0
        if budget >= 0.5:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                                 stdin_graph=best, timeout=remaining)
                n_c, e_c = lib.parse_graph_text(text)
                consider(n_c, e_c)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
