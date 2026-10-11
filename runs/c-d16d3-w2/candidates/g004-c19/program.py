import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: repair/insertion search on general bipartite graphs.
#
# Starting from a valid graph, it repeatedly inserts a new vertex on one side,
# joined to as many spare-degree vertices of the other side as possible, then
# runs simulated annealing over degree-preserving 2-switches. The cost is the
# number of unordered vertex pairs at distance > D (computed with bitsets).
# If the cost reaches 0 the graph is valid with one more vertex and becomes
# the new base. Edges are added greedily whenever both endpoints have spare
# degree, which never hurts validity.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXD 64
#define MAXE (MAXN * MAXD / 2 + 16)
#define ITERS 4000

static int N_, DEG_, DIAM_, M_;
static unsigned char side_[MAXN];
static int deg_[MAXN];
static int nb_[MAXN][MAXD];
static unsigned char adj_[MAXN][MAXN];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static int best_n, best_m;
static unsigned char best_side[MAXN];
static int best_eu[MAXE], best_ev[MAXE];
static int col_[MAXN], queue_[MAXN];

static uint64_t rng_s = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t_start;
static double t_budget;
static int time_up(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC > t_budget;
}

static void add_edge(int a, int b) {
    adj_[a][b] = 1;
    adj_[b][a] = 1;
    nb_[a][deg_[a]++] = b;
    nb_[b][deg_[b]++] = a;
    M_++;
}

static void del_from(int a, int b) {
    int k;
    for (k = 0; k < deg_[a]; k++)
        if (nb_[a][k] == b) break;
    nb_[a][k] = nb_[a][deg_[a] - 1];
    deg_[a]--;
}

static void remove_edge(int a, int b) {
    adj_[a][b] = 0;
    adj_[b][a] = 0;
    del_from(a, b);
    del_from(b, a);
    M_--;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIAM_ (unreachable counts as bad). */
static long long cost_bad(void) {
    int W = (N_ + 63) >> 6;
    uint64_t (*cur)[MAXW] = bufA, (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N_; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < DIAM_; step++) {
        for (int v = 0; v < N_; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg_[v]; k++) {
                int u = nb_[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N_; v++)
        for (int w = 0; w < W; w++)
            tot += popc64(cur[v][w]);
    long long ordered_bad = (long long)N_ * N_ - tot;
    return ordered_bad / 2;
}

static void spare_fill(void) {
    int start = rndint(N_ > 0 ? N_ : 1);
    for (int i = 0; i < N_; i++) {
        int a = (start + i) % N_;
        if (side_[a] != 0 || deg_[a] >= DEG_) continue;
        for (int j = 0; j < N_ && deg_[a] < DEG_; j++) {
            int b = (start + j) % N_;
            if (side_[b] == 1 && deg_[b] < DEG_ && !adj_[a][b]) add_edge(a, b);
        }
    }
}

/* Insert a new vertex on side s, joined to up to DEG_ spare vertices of the other side. */
static int insert_vertex(int s) {
    if (N_ >= MAXN - 2) return 0;
    int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < N_; v++)
        if (side_[v] == 1 - s && deg_[v] < DEG_) cand[nc++] = v;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int want = DEG_ < nc ? DEG_ : nc;
    int x = N_;
    N_++;
    side_[x] = (unsigned char)s;
    deg_[x] = 0;
    for (int u = 0; u < x; u++) adj_[u][x] = 0;
    memset(adj_[x], 0, (size_t)(x + 1));
    for (int i = 0; i < want; i++) add_edge(x, cand[i]);
    return 1;
}

static void save_best(void) {
    best_n = N_;
    memcpy(best_side, side_, (size_t)N_);
    best_m = 0;
    for (int v = 0; v < N_; v++)
        for (int k = 0; k < deg_[v]; k++) {
            int u = nb_[v][k];
            if (u > v && best_m < MAXE) {
                best_eu[best_m] = v;
                best_ev[best_m] = u;
                best_m++;
            }
        }
}

static void load_best(void) {
    int lim = N_ > best_n ? N_ : best_n;
    for (int v = 0; v < lim; v++) {
        memset(adj_[v], 0, (size_t)lim);
        deg_[v] = 0;
    }
    N_ = best_n;
    memcpy(side_, best_side, (size_t)best_n);
    M_ = 0;
    for (int i = 0; i < best_m; i++) add_edge(best_eu[i], best_ev[i]);
}

static int pick_edge(int *a, int *b) {
    for (int tries = 0; tries < 200; tries++) {
        int v = rndint(N_);
        if (side_[v] != 0 || deg_[v] == 0) continue;
        *a = v;
        *b = nb_[v][rndint(deg_[v])];
        return 1;
    }
    return 0;
}

static int color_graph(void) {
    for (int v = 0; v < N_; v++) col_[v] = -1;
    for (int s = 0; s < N_; s++) {
        if (col_[s] >= 0) continue;
        int qh = 0, qt = 0;
        col_[s] = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int k = 0; k < deg_[u]; k++) {
                int v = nb_[u][k];
                if (col_[v] < 0) {
                    col_[v] = 1 - col_[u];
                    queue_[qt++] = v;
                } else if (col_[v] == col_[u]) {
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < N_; v++) side_[v] = (unsigned char)col_[v];
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG_ = atoi(argv[1]);
    DIAM_ = atoi(argv[2]);
    uint64_t sd = (uint64_t)strtoull(argv[3], NULL, 10);
    rng_s ^= sd * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rng_s == 0) rng_s = 1;
    t_budget = atof(argv[4]);
    t_start = clock();
    if (DEG_ < 1 || DEG_ > MAXD || DIAM_ < 1) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    N_ = 0;
    M_ = 0;
    if (n == 0) {
        int k = DEG_;
        N_ = 2 * k;
        for (int i = 0; i < N_; i++) side_[i] = (unsigned char)(i < k ? 0 : 1);
        for (int i = 0; i < k; i++)
            for (int j = 0; j < k; j++)
                add_edge(i, k + j);
    } else {
        if (n < 1 || n > MAXN - 2) {
            printf("0 0\n");
            return 0;
        }
        N_ = n;
        for (int i = 0; i < m; i++) {
            int a, b;
            if (scanf("%d %d", &a, &b) != 2) break;
            if (a < 0 || b < 0 || a >= n || b >= n || a == b) continue;
            if (adj_[a][b] || deg_[a] >= DEG_ || deg_[b] >= DEG_) continue;
            add_edge(a, b);
        }
        if (!color_graph()) {
            printf("0 0\n");
            return 0;
        }
    }
    if (cost_bad() != 0) {
        printf("0 0\n");
        return 0;
    }
    spare_fill();
    save_best();

    while (!time_up()) {
        load_best();
        int s = rndint(2);
        if (!insert_vertex(s) && !insert_vertex(1 - s)) break;
        spare_fill();
        long long c = cost_bad();
        double T = 0.8;
        for (int it = 0; it < ITERS && c > 0; it++) {
            if ((it & 7) == 0 && time_up()) break;
            int a, b, x, y;
            if (!pick_edge(&a, &b)) break;
            if (!pick_edge(&x, &y)) break;
            if (a == x || b == y || adj_[a][y] || adj_[x][b]) continue;
            remove_edge(a, b);
            remove_edge(x, y);
            add_edge(a, y);
            add_edge(x, b);
            long long c2 = cost_bad();
            long long delta = c2 - c;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                c = c2;
            } else {
                remove_edge(a, y);
                remove_edge(x, b);
                add_edge(a, b);
                add_edge(x, y);
            }
            T *= 0.999;
            if (T < 0.2) T = 0.2;
        }
        if (c == 0) save_best();
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add an A-vertex per point of SA
# (joined to the lines through it) and a B-vertex per line of SB (joined to the
# points on it), with each line in <= s of SA and each point on <= s lines of SB.
# ----------------------------------------------------------------------------

_LS_ITERS = 20000


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
    """Randomized greedy load-constrained selection."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus A-vertices (per SA point) and B-vertices (per SB line)."""
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
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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
        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) baseline (D = 4).
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Structured starts (diameter 3 for arc extensions).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C repair/insertion search starting from the best valid graph found so far.
    remaining = 0.9 * time_limit - (time.monotonic() - t0)
    if remaining > 3.0 and d <= 64:
        budget = remaining - 2.0
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=remaining)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
