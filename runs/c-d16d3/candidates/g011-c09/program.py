import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: graph-level annealing with growth.
#
# State: a simple bipartite graph (side 0 / side 1) with max degree d and a
# bad-pair count (pairs at distance > D, unreachable counted). Moves keep the
# edge count and sides: degree-preserving 2-switches and "slack" moves that
# re-hang one edge end onto a vertex with spare degree. Growth inserts a pair
# of new vertices v (side 0), w (side 1) with edge v-w, joined to d-1 slots
# taken from spare capacity or from removed matching edges. The engine anneals
# back to zero bad pairs, snapshots, and retries growth; a failed attempt
# restores the last valid snapshot. Output is the largest valid snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1600
#define DMAX 64
#define WMAX ((NMAX + 63) / 64)
#define SNAPMAX (NMAX * DMAX / 2)

static int d_, D_, n_;
static int side_[NMAX];
static int deg_[NMAX];
static int nb_[NMAX][DMAX];
static uint64_t rs_;
static clock_t t0_;
static double budget_;
static uint64_t bufA_[NMAX][WMAX], bufB_[NMAX][WMAX];

static int snap_n_, snap_m_;
static int snap_side_[NMAX];
static int snap_u_[SNAPMAX], snap_v_[SNAPMAX];
static int have_best_;

typedef struct { int type, a1, b1, a2, b2; } Move;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0_) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg_[a]; i++)
        if (nb_[a][i] == b) return 1;
    return 0;
}
static void add_arc(int a, int b) { nb_[a][deg_[a]++] = b; }
static void add_edge(int a, int b) { add_arc(a, b); add_arc(b, a); }
static void del_arc(int a, int b) {
    for (int i = 0; i < deg_[a]; i++)
        if (nb_[a][i] == b) { nb_[a][i] = nb_[a][--deg_[a]]; return; }
}
static void rem_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

static void shuffle_arr(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Number of unordered pairs at distance > D_ (unreachable counts). */
static long long bad_pairs(void) {
    int W = (n_ + 63) / 64;
    uint64_t (*cur)[WMAX] = bufA_;
    uint64_t (*nxt)[WMAX] = bufB_;
    for (int v = 0; v < n_; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n_; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg_[v]; i++) {
                const uint64_t *src = cur[nb_[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long long unreached = 0;
    for (int v = 0; v < n_; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc(cur[v][w]);
        unreached += n_ - cnt;
    }
    return unreached / 2;
}

static int pick_edge(int *a, int *b) {
    for (int t = 0; t < 1000; t++) {
        int v = rndint(n_);
        if (side_[v] == 0 && deg_[v] > 0) {
            *a = v;
            *b = nb_[v][rndint(deg_[v])];
            return 1;
        }
    }
    return 0;
}

static int propose(Move *M) {
    if (rnd01() < 0.15) {
        int a, b, bp = -1;
        if (!pick_edge(&a, &b)) return 0;
        for (int t = 0; t < 60; t++) {
            int x = rndint(n_);
            if (side_[x] == 1 && deg_[x] < d_ && x != b && !has_edge(a, x)) { bp = x; break; }
        }
        if (bp < 0) return 0;
        M->type = 1; M->a1 = a; M->b1 = b; M->a2 = 0; M->b2 = bp;
        return 1;
    }
    int a1, b1, a2, b2;
    if (!pick_edge(&a1, &b1) || !pick_edge(&a2, &b2)) return 0;
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    M->type = 0; M->a1 = a1; M->b1 = b1; M->a2 = a2; M->b2 = b2;
    return 1;
}

static void apply_move(const Move *M) {
    if (M->type == 0) {
        rem_edge(M->a1, M->b1);
        rem_edge(M->a2, M->b2);
        add_edge(M->a1, M->b2);
        add_edge(M->a2, M->b1);
    } else {
        rem_edge(M->a1, M->b1);
        add_edge(M->a1, M->b2);
    }
}

static void undo_move(const Move *M) {
    if (M->type == 0) {
        rem_edge(M->a1, M->b2);
        rem_edge(M->a2, M->b1);
        add_edge(M->a1, M->b1);
        add_edge(M->a2, M->b2);
    } else {
        rem_edge(M->a1, M->b2);
        add_edge(M->a1, M->b1);
    }
}

/* Simulated annealing at fixed n_. Returns 1 when bad pairs reach 0. */
static int anneal(int K, double T0) {
    long long cur = bad_pairs();
    if (cur == 0) return 1;
    Move M;
    for (int it = 0; it < K; it++) {
        if ((it & 15) == 0 && elapsed() >= budget_) return 0;
        if (!propose(&M)) continue;
        double T = T0 * (1.0 - (double)it / (double)K) + 0.02;
        apply_move(&M);
        long long c2 = bad_pairs();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            undo_move(&M);
        }
    }
    return 0;
}

/* Insert a new pair (v on side 0, w on side 1) joined by an edge; each gets d-1 more
   neighbours from spare capacity, or from removed full matching edges. */
static int insert_pair(void) {
    int need = d_ - 1;
    if (need < 1 || n_ + 2 > NMAX) return 0;
    static int fa[NMAX], fb[NMAX];
    int na = 0, nbb = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] < d_) {
            if (side_[v] == 0) fa[na++] = v;
            else fb[nbb++] = v;
        }
    }
    shuffle_arr(fa, na);
    shuffle_arr(fb, nbb);
    int avail = na < nbb ? na : nbb;
    int k = need - avail;
    if (k < 0) k = 0;
    int ra[DMAX], rb[DMAX], cnt = 0;
    int tries = 0;
    while (cnt < k && tries < 4000) {
        tries++;
        int a, b;
        if (!pick_edge(&a, &b)) break;
        if (deg_[a] != d_ || deg_[b] != d_) continue;
        int dup = 0;
        for (int i = 0; i < cnt; i++)
            if (ra[i] == a || rb[i] == b) { dup = 1; break; }
        if (dup) continue;
        ra[cnt] = a; rb[cnt] = b; cnt++;
    }
    if (cnt < k) return 0;

    int v = n_, w = n_ + 1;
    side_[v] = 0; side_[w] = 1;
    deg_[v] = 0; deg_[w] = 0;
    n_ += 2;
    for (int i = 0; i < cnt; i++) rem_edge(ra[i], rb[i]);
    for (int i = 0; i < cnt; i++) {
        add_edge(v, rb[i]);
        add_edge(w, ra[i]);
    }
    int ext = need - cnt;
    for (int i = 0; i < ext; i++) {
        add_edge(v, fb[i]);
        add_edge(w, fa[i]);
    }
    add_edge(v, w);
    return 1;
}

static void take_snapshot(void) {
    snap_n_ = n_;
    snap_m_ = 0;
    for (int v = 0; v < n_; v++) snap_side_[v] = side_[v];
    for (int a = 0; a < n_; a++) {
        if (side_[a] != 0) continue;
        for (int i = 0; i < deg_[a]; i++) {
            snap_u_[snap_m_] = a;
            snap_v_[snap_m_] = nb_[a][i];
            snap_m_++;
        }
    }
}

static void restore_snapshot(void) {
    n_ = snap_n_;
    for (int v = 0; v < n_; v++) {
        deg_[v] = 0;
        side_[v] = snap_side_[v];
    }
    for (int i = 0; i < snap_m_; i++) add_edge(snap_u_[i], snap_v_[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    budget_ = atof(argv[4]);
    rs_ = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 8; i++) rnd64();
    t0_ = clock();

    if (d_ < 1 || d_ > DMAX || D_ < 1) { printf("0 0\n"); return 0; }
    if (D_ == 1) { printf("2 1\n0 1\n"); return 0; }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }

    if (n == 0) {
        /* No start graph: K_{d,d} has diameter 2. */
        if (2 * d_ > NMAX) { printf("0 0\n"); return 0; }
        n_ = 2 * d_;
        for (int a = 0; a < d_; a++)
            for (int b = 0; b < d_; b++)
                add_edge(a, d_ + b);
    } else {
        if (n < 0 || n > NMAX || m < 0 || m > SNAPMAX) { printf("0 0\n"); return 0; }
        n_ = n;
        int ok = 1;
        for (int i = 0; i < m && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
            if (deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
        if (!ok) { printf("0 0\n"); return 0; }
    }

    /* Bipartition by BFS; reject odd cycles. */
    {
        static int color[NMAX];
        static int queue[NMAX];
        int ok = 1;
        for (int v = 0; v < n_; v++) color[v] = -1;
        for (int s = 0; s < n_ && ok; s++) {
            if (color[s] >= 0) continue;
            color[s] = 0;
            int head = 0, tail = 0;
            queue[tail++] = s;
            while (head < tail && ok) {
                int u = queue[head++];
                for (int i = 0; i < deg_[u]; i++) {
                    int v = nb_[u][i];
                    if (color[v] < 0) {
                        color[v] = 1 - color[u];
                        queue[tail++] = v;
                    } else if (color[v] == color[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        if (!ok) { printf("0 0\n"); return 0; }
        for (int v = 0; v < n_; v++) side_[v] = color[v];
    }

    if (bad_pairs() == 0) {
        take_snapshot();
        have_best_ = 1;
    }
    const int K = 6000;
    const double T0 = 1.5;

    /* Repair the start graph if it is not yet valid. */
    while (!have_best_ && elapsed() < budget_) {
        if (anneal(K, T0)) {
            take_snapshot();
            have_best_ = 1;
        }
    }

    /* Grow by a vertex pair, repair, snapshot; restore on failure. */
    int fails = 0;
    while (have_best_ && elapsed() < budget_) {
        if (!insert_pair()) {
            fails++;
            if (fails > 200) break;
            continue;
        }
        if (anneal(K, T0)) {
            take_snapshot();
            fails = 0;
        } else {
            restore_snapshot();
            fails++;
            if (fails > 100000) break;
        }
    }

    if (!have_best_) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snap_n_, snap_m_);
    for (int i = 0; i < snap_m_; i++) printf("%d %d\n", snap_u_[i], snap_v_[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective planes (diameter 3) and
# W(q) generalized quadrangle (diameter 4). Used as C starting graphs.
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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
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
    """Candidate (n, edges) graphs of diameter 3 from PG(2, q) plus arc-type extensions."""
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t_start)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = None

    def consider(cand):
        nonlocal best
        n, e = cand
        if best is not None and n <= best[0]:
            return
        if lib.is_valid(n, e, d, D):
            best = (n, e)

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    consider(lib.haar_graph(d, range(d)))

    if D >= 3:
        for cand in _arc_extensions(d, t_start + 0.2 * time_limit, random.Random(seed * 7919 + d)):
            consider(cand)

    if D >= 4 and left() > 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if best is None:
        return 1, []

    # Main search: C graph-level annealing with vertex-pair growth.
    rem = left() - 4.0
    if rem > 3.0 and d <= 64:
        budget = max(1.0, 0.85 * rem - 1.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=rem)
            n2, e2 = lib.parse_graph_text(out)
            consider((n2, e2))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
