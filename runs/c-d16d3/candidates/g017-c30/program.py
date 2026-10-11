import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cover-insertion plus bad-pair annealing (new in this version).
#
# State: a bipartite graph (colour 0 / colour 1), max degree d, diameter <= D.
# Cost = number of ordered vertex pairs at distance > D (0 = valid).
#
# Insertion. A new vertex x of colour c with neighbour set N (colour 1-c, spare
# degree) is valid iff every existing vertex w is within distance D-1 of some
# u in N. This is a set-cover problem over the radius-(D-1) balls, solved by a
# randomised greedy with bitsets. Adding x never lengthens an old path, so the
# insertion keeps a valid graph valid and grows the order by one.
#
# Moves. Degree-preserving double-edge swaps (a-b, c-e -> a-e, c-b) and single
# edge deletions (which create spare degree). Both are accepted by Metropolis on
# the bad-pair cost, so the walk can cross invalid states. Whenever the cost is
# 0 the insertion step is attempted, so spare degree that the walk creates is
# turned into new vertices.
#
# Best valid graph is kept and printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define CAP_EXTRA 700
#define TRIES 6

static int d, D;
static int n, CAP, WC;
static int *deg, *adj, *col, *mark, *nbuf, *best_e, *queue_buf;
static u64 *bufT, *bufR, *ball, *ubuf;
static int best_m, best_n;
static int stamp = 0;
static u64 rs = 88172645463325252ULL;
static int *in_u, *in_v, in_n, in_m;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd64() % (u64)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pop64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * d;
    for (int k = 0; k < deg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    int *p = adj + (size_t)a * d;
    for (int k = 0; k < deg[a]; k++) {
        if (p[k] == b) {
            p[k] = p[deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_arc(int a, int b) {
    adj[(size_t)a * d + deg[a]] = b;
    deg[a]++;
}

static void add_edge(int a, int b) {
    add_arc(a, b);
    add_arc(b, a);
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* out[v] = bitset of vertices within distance r of v. */
static void reach(int r, u64 *out) {
    int wn = (n + 63) >> 6;
    u64 *a = out, *b = bufT;
    memset(out, 0, sizeof(u64) * (size_t)n * WC);
    for (int v = 0; v < n; v++)
        a[(size_t)v * WC + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < r; t++) {
        for (int v = 0; v < n; v++) {
            u64 *bv = b + (size_t)v * WC;
            const u64 *av = a + (size_t)v * WC;
            for (int w = 0; w < wn; w++) bv[w] = av[w];
            const int *p = adj + (size_t)v * d;
            for (int k = 0; k < deg[v]; k++) {
                const u64 *au = a + (size_t)p[k] * WC;
                for (int w = 0; w < wn; w++) bv[w] |= au[w];
            }
        }
        u64 *tmp = a;
        a = b;
        b = tmp;
    }
    if (a != out) memcpy(out, a, sizeof(u64) * (size_t)n * WC);
}

/* Number of ordered pairs at distance > D. Zero means valid. */
static long long cost_full(void) {
    reach(D, bufR);
    int wn = (n + 63) >> 6;
    long long c = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        const u64 *rv = bufR + (size_t)v * WC;
        for (int w = 0; w < wn; w++) cnt += pop64(rv[w]);
        c += n - cnt;
    }
    return c;
}

static int pick0(void) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(n);
        if (col[v] == 0 && deg[v] > 0) return v;
    }
    return -1;
}

/* Randomised greedy cover: add a vertex whose neighbours' (D-1)-balls cover everything. */
static int try_insert(void) {
    if (n >= CAP) return 0;
    int wn = (n + 63) >> 6;
    reach(D - 1, ball);
    for (int t = 0; t < TRIES; t++) {
        stamp++;
        int c = rndint(2);
        for (int w = 0; w < wn; w++) ubuf[w] = ~0ULL;
        if (n & 63) ubuf[wn - 1] = (1ULL << (n & 63)) - 1ULL;
        int nn = 0;
        while (nn < d) {
            int bu = -1, bs = 0, ties = 0;
            for (int u = 0; u < n; u++) {
                if (col[u] != 1 - c || deg[u] >= d || mark[u] == stamp) continue;
                const u64 *bl = ball + (size_t)u * WC;
                int s = 0;
                for (int w = 0; w < wn; w++) s += pop64(bl[w] & ubuf[w]);
                if (s > bs) {
                    bs = s;
                    bu = u;
                    ties = 1;
                } else if (s == bs && s > 0) {
                    ties++;
                    if (rndint(ties) == 0) bu = u;
                }
            }
            if (bs == 0) break;
            nbuf[nn++] = bu;
            mark[bu] = stamp;
            const u64 *bl = ball + (size_t)bu * WC;
            for (int w = 0; w < wn; w++) ubuf[w] &= ~bl[w];
        }
        int empty = 1;
        for (int w = 0; w < wn; w++)
            if (ubuf[w]) {
                empty = 0;
                break;
            }
        if (empty) {
            int x = n;
            n++;
            col[x] = c;
            deg[x] = 0;
            for (int k = 0; k < nn; k++) add_edge(x, nbuf[k]);
            return 1;
        }
    }
    return 0;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] != 0) continue;
        for (int k = 0; k < deg[v]; k++) {
            best_e[2 * m] = v;
            best_e[2 * m + 1] = adj[(size_t)v * d + k];
            m++;
        }
    }
    best_m = m;
    best_n = n;
}

static void emit_best(void) {
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++)
        printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
}

static void emit_input(void) {
    printf("%d %d\n", in_n, in_m);
    for (int i = 0; i < in_m; i++) printf("%d %d\n", in_u[i], in_v[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    clock_t t0 = clock();

    if (scanf("%d %d", &in_n, &in_m) != 2) {
        in_n = 0;
        in_m = 0;
    }
    if (in_n < 0 || in_m < 0) {
        in_n = 0;
        in_m = 0;
    }
    in_u = malloc(sizeof(int) * (size_t)(in_m + 1));
    in_v = malloc(sizeof(int) * (size_t)(in_m + 1));
    for (int i = 0; i < in_m; i++) {
        if (scanf("%d %d", &in_u[i], &in_v[i]) != 2) {
            in_m = i;
            break;
        }
    }
    if (d < 1 || D < 2 || in_n <= 0) {
        emit_input();
        return 0;
    }

    CAP = in_n + CAP_EXTRA;
    WC = (CAP + 63) >> 6;
    deg = calloc((size_t)CAP, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)CAP * (size_t)d);
    col = malloc(sizeof(int) * (size_t)CAP);
    mark = calloc((size_t)CAP, sizeof(int));
    nbuf = malloc(sizeof(int) * (size_t)(d + 1));
    bufT = malloc(sizeof(u64) * (size_t)CAP * WC);
    bufR = malloc(sizeof(u64) * (size_t)CAP * WC);
    ball = malloc(sizeof(u64) * (size_t)CAP * WC);
    ubuf = malloc(sizeof(u64) * (size_t)WC);
    best_e = malloc(sizeof(int) * (2 * (size_t)CAP * d + 2));
    queue_buf = malloc(sizeof(int) * (size_t)CAP);
    if (!deg || !adj || !col || !mark || !nbuf || !bufT || !bufR || !ball ||
        !ubuf || !best_e || !queue_buf) {
        emit_input();
        return 0;
    }

    /* Load the start graph, checking degree, simplicity and bipartiteness. */
    n = in_n;
    int bad = 0;
    for (int i = 0; i < in_m && !bad; i++) {
        int u = in_u[i], v = in_v[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) {
            bad = 1;
            break;
        }
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) {
            bad = 1;
            break;
        }
        add_edge(u, v);
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && !bad; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue_buf[qt++] = s;
        while (qh < qt && !bad) {
            int u = queue_buf[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * d + k];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    queue_buf[qt++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) {
        emit_input();
        return 0;
    }

    save_best();
    long long cur = cost_full();
    long long iter = 0;
    const long long CYC = 40000;

    while (1) {
        if ((iter & 31) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        iter++;
        double phase = (double)(iter % CYC) / (double)CYC;
        double T = 0.12 + 1.6 * (1.0 - phase);

        if (cur == 0 && try_insert()) {
            cur = cost_full();
            if (cur == 0 && n > best_n) save_best();
            continue;
        }

        if (rnd01() < 0.85) {
            int a = pick0();
            int c = pick0();
            if (a < 0 || c < 0 || a == c) continue;
            int b = adj[(size_t)a * d + rndint(deg[a])];
            int e = adj[(size_t)c * d + rndint(deg[c])];
            if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            long long nc = cost_full();
            long long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                del_edge(a, e);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        } else {
            int a = pick0();
            if (a < 0) continue;
            int b = adj[(size_t)a * d + rndint(deg[a])];
            del_edge(a, b);
            long long nc = cost_full();
            long long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                add_edge(a, b);
            }
        }
    }

    emit_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (glue and starting graphs).
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
    """Randomised greedy: choose elements x so that every target is hit by <= s chosen elements."""
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
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Starting graphs: arc-extended projective planes (D >= 3), W(q) (D >= 4).
    if D >= 3:
        for n_c, e_c in _arc_extensions(d, t0 + 0.05 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Main search: C cover-insertion plus bad-pair annealing from the best start.
    budget = 0.75 * time_limit - 1.0 - (time.monotonic() - t0)
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=time_limit * 0.9)
            n_out, e_out = lib.parse_graph_text(text)
            consider(n_out, e_out)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
