import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: repair annealing that grows a valid graph one vertex at a time.
#
# Start from a valid bipartite graph. Repeatedly add one vertex (on a random
# side, joined to spare vertices of the other side), then anneal the edge set at
# the new size. The cost is the number of vertex pairs at distance > D, computed
# with bitset ball expansion. Moves keep the bipartition and never exceed degree d:
#   swap2  : replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1)  (degrees unchanged)
#   rewire : delete an edge, add a random spare-spare edge
#   attach : move one spare slot from some vertex to a spare vertex on the other side
#   add    : add a spare-spare edge
# When cost reaches 0 the graph is saved as the best valid one and grown again.
# Stagnation restores the last valid graph and grows it with fresh randomness.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int d_, D_, N, cap, Wcap, bN;
static int *side, *deg, *adj;
static int *bside, *bdeg, *badj;
static u64 *RA, *RB;
static int *cand;
static u64 rs;
static int lop[32], lu[32], lv[32], logn;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (u64)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    const int *a = adj + (size_t)u * d_;
    for (int k = 0; k < deg[u]; k++)
        if (a[k] == v) return 1;
    return 0;
}
static void add_arc(int u, int v) {
    adj[(size_t)u * d_ + deg[u]] = v;
    deg[u]++;
}
static void del_arc(int u, int v) {
    int *a = adj + (size_t)u * d_;
    for (int k = 0; k < deg[u]; k++)
        if (a[k] == v) {
            a[k] = a[deg[u] - 1];
            deg[u]--;
            return;
        }
}
static void add_edge(int u, int v) { add_arc(u, v); add_arc(v, u); }
static void remove_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

static void op_add(int u, int v) {
    add_edge(u, v);
    lop[logn] = 1; lu[logn] = u; lv[logn] = v; logn++;
}
static void op_del(int u, int v) {
    remove_edge(u, v);
    lop[logn] = 0; lu[logn] = u; lv[logn] = v; logn++;
}
static void undo(void) {
    while (logn > 0) {
        logn--;
        if (lop[logn]) remove_edge(lu[logn], lv[logn]);
        else add_edge(lu[logn], lv[logn]);
    }
}

/* Number of unordered vertex pairs at distance > D_. Zero means valid diameter. */
static long long bad_cost(void) {
    int n = N, W = (n + 63) >> 6;
    u64 *A = RA, *B = RB;
    memset(A, 0, sizeof(u64) * (size_t)n * W);
    for (int v = 0; v < n; v++) A[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            u64 *bv = B + (size_t)v * W;
            const u64 *av = A + (size_t)v * W;
            memcpy(bv, av, sizeof(u64) * (size_t)W);
            const int *nb = adj + (size_t)v * d_;
            for (int k = 0; k < deg[v]; k++) {
                const u64 *au = A + (size_t)nb[k] * W;
                for (int w = 0; w < W; w++) bv[w] |= au[w];
            }
        }
        u64 *tmp = A; A = B; B = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        const u64 *av = A + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(av[w]);
        tot += n - c;
    }
    return tot / 2;
}

static void save_state(void) {
    memcpy(bside, side, sizeof(int) * (size_t)cap);
    memcpy(bdeg, deg, sizeof(int) * (size_t)cap);
    memcpy(badj, adj, sizeof(int) * (size_t)cap * d_);
    bN = N;
}
static void restore_state(void) {
    memcpy(side, bside, sizeof(int) * (size_t)cap);
    memcpy(deg, bdeg, sizeof(int) * (size_t)cap);
    memcpy(adj, badj, sizeof(int) * (size_t)cap * d_);
    N = bN;
}

/* Random vertex on side s with spare degree, or -1. */
static int pick_spare(int s) {
    int c = 0;
    for (int v = 0; v < N; v++)
        if (side[v] == s && deg[v] < d_) cand[c++] = v;
    return c ? cand[rndint(c)] : -1;
}

/* Uniformly random edge, returned with a on side 0 and b on side 1. */
static int pick_edge(int *pa, int *pb) {
    long long tot = 0;
    for (int v = 0; v < N; v++)
        if (side[v] == 0) tot += deg[v];
    if (tot == 0) return 0;
    long long r = (long long)(rnd() % (u64)tot);
    for (int v = 0; v < N; v++) {
        if (side[v] != 0) continue;
        if (r < deg[v]) {
            *pa = v;
            *pb = adj[(size_t)v * d_ + (int)r];
            return 1;
        }
        r -= deg[v];
    }
    return 0;
}

static int move_swap(void) {
    int a1, b1, a2, b2;
    if (!pick_edge(&a1, &b1) || !pick_edge(&a2, &b2)) return 0;
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    op_del(a1, b1);
    op_del(a2, b2);
    op_add(a1, b2);
    op_add(a2, b1);
    return 1;
}

static int move_rewire(void) {
    int a, b;
    if (!pick_edge(&a, &b)) return 0;
    op_del(a, b);
    for (int t = 0; t < 4; t++) {
        int x = pick_spare(0), y = pick_spare(1);
        if (x < 0 || y < 0) break;
        if (!has_edge(x, y)) {
            op_add(x, y);
            return 1;
        }
    }
    return 0;
}

static int move_attach(void) {
    int s = rndint(2);
    int x = pick_spare(s);
    if (x < 0) return 0;
    int c = 0;
    for (int v = 0; v < N; v++)
        if (side[v] == 1 - s && deg[v] > 0 && !has_edge(x, v)) cand[c++] = v;
    if (!c) return 0;
    int q = cand[rndint(c)];
    int r = adj[(size_t)q * d_ + rndint(deg[q])];
    op_del(q, r);
    op_add(x, q);
    return 1;
}

static int move_add(void) {
    for (int t = 0; t < 4; t++) {
        int x = pick_spare(0), y = pick_spare(1);
        if (x < 0 || y < 0) return 0;
        if (!has_edge(x, y)) {
            op_add(x, y);
            return 1;
        }
    }
    return 0;
}

/* Append a vertex and join it to up to d spare vertices of the opposite side. */
static void grow(void) {
    int v = N++;
    deg[v] = 0;
    side[v] = rndint(2);
    int c = 0;
    for (int u = 0; u < v; u++)
        if (side[u] == 1 - side[v] && deg[u] < d_) cand[c++] = u;
    if (c == 0) {
        side[v] = 1 - side[v];
        for (int u = 0; u < v; u++)
            if (side[u] == 1 - side[v] && deg[u] < d_) cand[c++] = u;
    }
    for (int i = 0; i < c && deg[v] < d_; i++) {
        int j = i + rndint(c - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
        add_edge(v, cand[i]);
    }
}

static void print_pairs(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

static void print_best(void) {
    long long m = 0;
    for (int v = 0; v < bN; v++)
        for (int k = 0; k < bdeg[v]; k++)
            if (v < badj[(size_t)v * d_ + k]) m++;
    printf("%d %lld\n", bN, m);
    for (int v = 0; v < bN; v++)
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[(size_t)v * d_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = (u64)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    clock_t t0 = clock();

    if (d_ < 1 || D_ < 1) {
        printf("1 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0) { n0 = 0; m0 = 0; }
    int *eu = malloc(sizeof(int) * ((size_t)m0 + 2));
    int *ev = malloc(sizeof(int) * ((size_t)m0 + 2));
    int mread = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        mread++;
    }
    m0 = mread;
    if (n0 == 0) {
        n0 = 2; m0 = 1; eu[0] = 0; ev[0] = 1;
    }

    int *dg = calloc((size_t)n0 + 1, sizeof(int));
    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { bad = 1; break; }
        dg[u]++; dg[v]++;
    }
    for (int v = 0; v < n0 && !bad; v++)
        if (dg[v] > d_) bad = 1;
    if (bad) {
        print_pairs(n0, m0, eu, ev);
        return 0;
    }

    cap = 2 * n0 + 256;
    Wcap = (cap + 63) >> 6;
    side = malloc(sizeof(int) * (size_t)cap);
    deg = calloc((size_t)cap, sizeof(int));
    adj = calloc((size_t)cap * d_, sizeof(int));
    bside = malloc(sizeof(int) * (size_t)cap);
    bdeg = malloc(sizeof(int) * (size_t)cap);
    badj = calloc((size_t)cap * d_, sizeof(int));
    RA = malloc(sizeof(u64) * (size_t)cap * Wcap);
    RB = malloc(sizeof(u64) * (size_t)cap * Wcap);
    cand = malloc(sizeof(int) * (size_t)cap);
    int *queue = malloc(sizeof(int) * (size_t)cap);

    N = n0;
    for (int i = 0; i < m0; i++) add_edge(eu[i], ev[i]);
    for (int v = 0; v < n0; v++) side[v] = -1;
    int ok_bip = 1;
    for (int s0 = 0; s0 < n0 && ok_bip; s0++) {
        if (side[s0] >= 0) continue;
        side[s0] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s0;
        while (head < tail && ok_bip) {
            int x = queue[head++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[(size_t)x * d_ + k];
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    queue[tail++] = y;
                } else if (side[y] == side[x]) {
                    ok_bip = 0;
                    break;
                }
            }
        }
    }
    if (!ok_bip) {
        print_pairs(n0, m0, eu, ev);
        return 0;
    }

    save_state();
    long long cur = bad_cost();
    int best_valid = (cur == 0);
    const double T0 = 1.5;
    double T = T0;
    long long bestcur = cur, since = 0, iter = 0;
    const long long STAG = 5000;

    while (1) {
        if ((iter & 7) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        iter++;
        if (cur == 0) {
            if (!best_valid || N > bN) {
                save_state();
                best_valid = 1;
            }
            if (N >= cap) break;
            grow();
            cur = bad_cost();
            T = T0;
            bestcur = cur;
            since = 0;
            continue;
        }
        logn = 0;
        int r = rndint(100), ok;
        if (r < 35) ok = move_swap();
        else if (r < 55) ok = move_rewire();
        else if (r < 75) ok = move_attach();
        else ok = move_add();
        if (!ok) {
            undo();
            since++;
            continue;
        }
        long long nc = bad_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            logn = 0;
        } else {
            undo();
        }
        if (cur < bestcur) { bestcur = cur; since = 0; }
        else since++;
        T *= 0.9995;
        if (T < 0.15) T = 0.15;
        if (since > STAG) {
            restore_state();
            cur = bad_cost();
            bestcur = cur;
            since = 0;
            T = T0;
        }
    }
    if (cur == 0 && (!best_valid || N > bN)) save_state();
    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective planes (diameter 3) and the
# generalized quadrangle W(q) (diameter 4). Both are fed to the C engine.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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

    if D >= 3:
        deadline = t0 + 0.15 * time_limit
        for n_c, e_c in _arc_extensions(d, deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Spend most of the budget in the C repair-growth engine, starting from the best graph.
    remaining = time_limit * 0.85 - (time.monotonic() - t0) - 2.0
    if d <= 4:
        remaining = min(remaining, 5.0)
    if remaining > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            stdin_graph=best, timeout=remaining + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
