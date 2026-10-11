"""Graph builder: best known algebraic base, then a C grow-and-repair search.

Base graphs: projective-plane incidence graphs extended by arcs (diameter 3),
cyclic Haar graphs from difference covers, and K_{d,d} as a universal fallback.
New in this version: a C engine that grows a valid bipartite graph one vertex at
a time. Each new vertex steals degree from saturated neighbours, and simulated
annealing repairs the diameter with degree-preserving 2-switches and spare-degree
edge insertions. The cost is the exact number of vertex pairs at distance > D.
The best valid state is kept, and the search restarts from it after a stall.
"""
import itertools
import math
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

#define NMAX 1200
#define WMAX 19
#define DMAX 64
#define STALL 4000

static int d_, D_, n_;
static int deg_[NMAX];
static int nb_[NMAX][DMAX];
static int col_[NMAX];
static uint64_t ball_[2][NMAX][WMAX];
static int bn_ = 0;
static int bdeg_[NMAX];
static int bnb_[NMAX][DMAX];
static int bcol_[NMAX];
static uint64_t rs_ = 88172645463325252ULL;
static int bfs_q_[NMAX];
static int cand_[NMAX];

typedef struct { int type, a, b, c, d; } Move;

static uint64_t rnd(void) { rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17; return rs_; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int u, int v) {
    for (int i = 0; i < deg_[u]; i++) if (nb_[u][i] == v) return 1;
    return 0;
}
static void del_arc(int u, int v) {
    for (int i = 0; i < deg_[u]; i++) {
        if (nb_[u][i] == v) { nb_[u][i] = nb_[u][--deg_[u]]; return; }
    }
}
static void add_edge(int u, int v) { nb_[u][deg_[u]++] = v; nb_[v][deg_[v]++] = u; }
static void del_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D_. Zero means valid. */
static long long cost_(void) {
    int W = (n_ + 63) / 64;
    int cur = 0;
    for (int v = 0; v < n_; v++) {
        for (int w = 0; w < W; w++) ball_[0][v][w] = 0;
        ball_[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D_; step++) {
        int nx = 1 - cur;
        for (int v = 0; v < n_; v++) {
            for (int w = 0; w < W; w++) ball_[nx][v][w] = ball_[cur][v][w];
            for (int i = 0; i < deg_[v]; i++) {
                int u = nb_[v][i];
                for (int w = 0; w < W; w++) ball_[nx][v][w] |= ball_[cur][u][w];
            }
        }
        cur = nx;
    }
    long long bad = 0;
    for (int v = 0; v < n_; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(ball_[cur][v][w]);
        bad += n_ - c;
    }
    return bad / 2;
}

static int color_all(void) {
    for (int v = 0; v < n_; v++) col_[v] = -1;
    for (int s = 0; s < n_; s++) {
        if (col_[s] != -1) continue;
        col_[s] = 0;
        int h = 0, t = 0;
        bfs_q_[t++] = s;
        while (h < t) {
            int u = bfs_q_[h++];
            for (int i = 0; i < deg_[u]; i++) {
                int v = nb_[u][i];
                if (col_[v] == -1) { col_[v] = 1 - col_[u]; bfs_q_[t++] = v; }
                else if (col_[v] == col_[u]) return 0;
            }
        }
    }
    return 1;
}

static void save_best(void) {
    bn_ = n_;
    for (int v = 0; v < n_; v++) {
        bdeg_[v] = deg_[v];
        bcol_[v] = col_[v];
        for (int i = 0; i < deg_[v]; i++) bnb_[v][i] = nb_[v][i];
    }
}

static void restore_best(void) {
    n_ = bn_;
    for (int v = 0; v < n_; v++) {
        deg_[v] = bdeg_[v];
        col_[v] = bcol_[v];
        for (int i = 0; i < deg_[v]; i++) nb_[v][i] = bnb_[v][i];
    }
}

/* Add a vertex on a random side, joined to up to d_ opposite-side vertices.
   A saturated neighbour first gives up one random incident edge. */
static void grow(void) {
    int w = n_++;
    deg_[w] = 0;
    int c = rndi(2);
    col_[w] = c;
    int k = 0;
    for (int v = 0; v < w; v++) if (col_[v] != c) cand_[k++] = v;
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand_[i]; cand_[i] = cand_[j]; cand_[j] = t;
    }
    int take = k < d_ ? k : d_;
    for (int i = 0; i < take; i++) {
        int v = cand_[i];
        if (deg_[v] >= d_) {
            int x = nb_[v][rndi(deg_[v])];
            del_edge(v, x);
        }
        add_edge(w, v);
    }
}

static int random_move(Move *mv) {
    if (rndf() < 0.4) {
        static int sp[2][NMAX];
        int ns[2] = {0, 0};
        for (int v = 0; v < n_; v++) if (deg_[v] < d_) sp[col_[v]][ns[col_[v]]++] = v;
        if (ns[0] == 0 || ns[1] == 0) return 0;
        int u = sp[0][rndi(ns[0])], v = sp[1][rndi(ns[1])];
        if (has_edge(u, v)) return 0;
        mv->type = 1; mv->a = u; mv->b = v;
        return 1;
    }
    int a = -1;
    for (int t = 0; t < 60 && a < 0; t++) {
        int x = rndi(n_);
        if (deg_[x] > 0) a = x;
    }
    if (a < 0) return 0;
    int b = nb_[a][rndi(deg_[a])];
    int c = -1;
    for (int t = 0; t < 60 && c < 0; t++) {
        int x = rndi(n_);
        if (x != a && col_[x] == col_[a] && deg_[x] > 0) c = x;
    }
    if (c < 0) return 0;
    int dd = nb_[c][rndi(deg_[c])];
    if (dd == b || has_edge(a, dd) || has_edge(c, b)) return 0;
    mv->type = 2; mv->a = a; mv->b = b; mv->c = c; mv->d = dd;
    return 1;
}

static void apply(const Move *m) {
    if (m->type == 2) {
        del_edge(m->a, m->b);
        del_edge(m->c, m->d);
        add_edge(m->a, m->d);
        add_edge(m->c, m->b);
    } else {
        add_edge(m->a, m->b);
    }
}

static void undo(const Move *m) {
    if (m->type == 2) {
        del_edge(m->a, m->d);
        del_edge(m->c, m->b);
        add_edge(m->a, m->b);
        add_edge(m->c, m->d);
    } else {
        del_edge(m->a, m->b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs_ == 0) rs_ = 1;
    double budget = atof(argv[4]);
    if (d_ > DMAX) d_ = DMAX;
    if (d_ < 1) d_ = 1;
    if (D_ < 1) D_ = 1;

    int ok = 0, n = 0, m = 0;
    if (scanf("%d %d", &n, &m) == 2 && n >= 2 && n <= NMAX - 200 && m >= 0) {
        ok = 1;
        n_ = n;
        for (int v = 0; v < n; v++) deg_[v] = 0;
        for (int i = 0; i < m && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
                deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
    }
    if (ok && !color_all()) ok = 0;
    if (!ok) {
        n_ = 2;
        deg_[0] = deg_[1] = 0;
        add_edge(0, 1);
        color_all();
    }

    clock_t t0 = clock();
    long long cur = cost_();
    if (cur == 0) save_best();
    double T = 0.5;
    long long since = 0;
    Move mv;
    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        if (cur == 0) {
            if (n_ > bn_) save_best();
            if (n_ >= NMAX - 2) break;
            grow();
            cur = cost_();
            T = 0.5;
            since = 0;
            continue;
        }
        if (!random_move(&mv)) { since++; continue; }
        apply(&mv);
        long long c2 = cost_();
        long long delta = c2 - cur;
        if (delta <= 0 || rndf() < exp(-(double)delta / T)) cur = c2;
        else undo(&mv);
        T *= 0.9995;
        if (T < 0.08) T = 0.08;
        since++;
        if (since > STALL) {
            if (bn_ > 0) { restore_best(); cur = 0; }
            since = 0;
            T = 0.5;
        }
    }

    if (bn_ == 0) {
        printf("2 1\n0 1\n");
        return 0;
    }
    long long me = 0;
    for (int v = 0; v < bn_; v++) me += bdeg_[v];
    me /= 2;
    printf("%d %lld\n", bn_, me);
    for (int v = 0; v < bn_; v++)
        for (int i = 0; i < bdeg_[v]; i++)
            if (bnb_[v][i] > v) printf("%d %d\n", v, bnb_[v][i]);
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
# Cyclic Haar graphs from difference covers (diameter 3 when S - S covers Z_m).
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    return cnt, zeros


def _move(S, cnt, i, y, m, zeros):
    k = len(S)
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            a = (old - t) % m
            b = (t - old) % m
            cnt[a] -= 1
            if cnt[a] == 0:
                zeros += 1
            cnt[b] -= 1
            if cnt[b] == 0:
                zeros += 1
    S[i] = y
    for j in range(k):
        if j != i:
            t = S[j]
            a = (y - t) % m
            b = (t - y) % m
            if cnt[a] == 0:
                zeros -= 1
            cnt[a] += 1
            if cnt[b] == 0:
                zeros -= 1
            cnt[b] += 1
    return zeros


def _cover_search(k, m, deadline, rng):
    if k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    cnt, zeros = _diff_counts(S, m)
    T = 0.3
    moves = 0
    while zeros > 0:
        moves += 1
        if moves % 512 == 0 and time.monotonic() > deadline:
            return None
        if moves % 200000 == 0:
            S = rng.sample(range(m), k)
            cnt, zeros = _diff_counts(S, m)
            continue
        i = rng.randrange(k)
        y = rng.randrange(m)
        if y in S:
            continue
        old = S[i]
        z = _move(S, cnt, i, y, m, zeros)
        delta = z - zeros
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            zeros = z
        else:
            _move(S, cnt, i, old, m, z)
    return sorted(S)


def _difference_graph(d, deadline, rng):
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best_m, best_S = 0, None
    cur = max(k + 1, int(0.8 * cap))
    fails = 0
    while time.monotonic() < deadline and cur <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
        S = _cover_search(k, cur, slice_end, rng)
        if S is not None:
            best_m, best_S = cur, S
            cur += 1
            fails = 0
        else:
            fails += 1
            if best_S is None:
                cur = max(k + 1, cur - 3)
            elif fails >= 3:
                break
    if best_S is None:
        return None
    return lib.haar_graph(best_m, best_S)


# ----------------------------------------------------------------------------
# C search driver.
# ----------------------------------------------------------------------------

def _c_search(start, d, D, seed, deadline):
    """Run the C grow-and-repair engine from a valid start graph; return a valid (n, edges) or None."""
    left = deadline - time.monotonic()
    budget = left - 2.0
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=start, timeout=left)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if lib.is_valid(n, e, d, D):
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.9 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(c):
        nonlocal best, best_n
        if c is None:
            return
        n, e = c
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for c in arcs[:3]:
            consider(c)
    if D == 3:
        consider(_difference_graph(d, start + 0.20 * time_limit, rng))

    # Main new step: C grow-and-repair search starting from the best valid graph.
    if best_n >= 4:
        consider(_c_search(best, d, D, seed, end))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
