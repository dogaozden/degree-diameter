import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine (one program, two phases, shared state):
#   Phase 1, ball-cover insertion: for R = D-1, a new vertex w joined to opposite-colour
#     vertices N is at distance <= D from every old vertex lying in the R-ball of some
#     u in N. Adding vertices and cross edges never increases old distances, so validity
#     is preserved. Each round computes R-balls as bitsets, greedily covers all vertices
#     with spare-degree candidates (randomised), and inserts a vertex on success. On
#     failure it adds a random spare cross edge to change the spare pattern.
#   Phase 2, bad-pair annealing: cost = unordered pairs at distance > D. Moves are focused
#     on defect vertices. When cost reaches 0 the graph is saved and a new vertex is
#     appended and greedily attached to minimise bad pairs.
# The engine always prints the best valid graph it saw (the input if nothing better).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXE (MAXN * MAXD)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t tmpr[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0;
static int curbl[MAXN], ncurbl = 0;
static int tmpbl[MAXN], ntmp = 0;
static int cand[MAXN], used[MAXN];
static clock_t T0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)((rnd64() >> 11) % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}
static void rm1(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}
static void del_edge(int u, int v) {
    rm1(u, v);
    rm1(v, u);
}

/* reach[v] = bitset of vertices within distance R of v. */
static void compute_balls(int R) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) tmpr[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = reach[adj[v][i]];
                for (int w = 0; w < W; w++) tmpr[v][w] |= s[w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = tmpr[v][w];
    }
}

/* Number of unordered pairs at distance > D. Fills bl with defect vertices if given. */
static int bad_pairs(int *bl, int *nbl) {
    compute_balls(D);
    long bad = 0;
    int k = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(reach[v][w]);
        int miss = n - c;
        bad += miss;
        if (miss > 0 && bl) bl[k++] = v;
    }
    if (nbl) *nbl = k;
    return (int)(bad / 2);
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

/* Insert a new vertex of colour `side` with neighbours covering all of the R-balls. */
static int try_insert(int side) {
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < nc; i++) used[cand[i]] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int bestc = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; bestc = u; }
        }
        if (bestc < 0) break;
        used[bestc] = 1;
        chosen[nch++] = bestc;
        for (int w = 0; w < W; w++) cov[w] |= reach[bestc][w];
    }
    if (!covers_all(cov)) return 0;
    if (n >= MAXN - 1) return 0;
    int x = n++;
    col[x] = side;
    deg[x] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], x);
    return 1;
}

static void phase_insert(double until) {
    int fails = 0;
    while (fails < 300 && n < MAXN - 1 && elapsed() < until) {
        compute_balls(D - 1);
        int first = (int)(rnd64() & 1);
        int ok = try_insert(first);
        if (!ok) ok = try_insert(1 - first);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = rint_(n), v = rint_(n);
            if (u == v || col[u] == col[v] || deg[u] >= d || deg[v] >= d || has_edge(u, v))
                continue;
            add_edge(u, v);
            break;
        }
    }
}

static void save_state(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (adj[u][i] > u && m < MAXE) {
                bestU[m] = u;
                bestV[m] = adj[u][i];
                m++;
            }
        }
    }
    best_n = n;
    best_m = m;
}

static int pick_vertex(void) {
    if (ncurbl > 0 && rdbl() < 0.6) return curbl[rint_(ncurbl)];
    return rint_(n);
}

/* Applies one random move; returns 0 if none was possible. */
static int do_move(int *kind, int *ma, int *mb, int *mw) {
    int r = rint_(100);
    if (r < 55) {
        *kind = 0;
        int a = -1;
        for (int t = 0; t < 64 && a < 0; t++) {
            int c = pick_vertex();
            if (deg[c] > 0) a = c;
        }
        if (a < 0) return 0;
        int b = adj[a][rint_(deg[a])];
        int w = -1;
        for (int t = 0; t < 64; t++) {
            int c = rint_(n);
            if (c != b && col[c] == col[b] && deg[c] < d && !has_edge(a, c)) { w = c; break; }
        }
        if (w < 0) return 0;
        del_edge(a, b);
        add_edge(a, w);
        *ma = a; *mb = b; *mw = w;
        return 1;
    } else if (r < 90) {
        *kind = 1;
        int x = -1;
        for (int t = 0; t < 64; t++) {
            int c = pick_vertex();
            if (deg[c] < d) { x = c; break; }
        }
        if (x < 0) return 0;
        int y = -1;
        for (int t = 0; t < 64; t++) {
            int c = rint_(n);
            if (col[c] != col[x] && deg[c] < d && !has_edge(x, c)) { y = c; break; }
        }
        if (y < 0) return 0;
        add_edge(x, y);
        *ma = x; *mb = y; *mw = -1;
        return 1;
    } else {
        *kind = 2;
        int a = -1;
        for (int t = 0; t < 64; t++) {
            int c = rint_(n);
            if (deg[c] > 0) { a = c; break; }
        }
        if (a < 0) return 0;
        int b = adj[a][rint_(deg[a])];
        del_edge(a, b);
        *ma = a; *mb = b; *mw = -1;
        return 1;
    }
}

static void undo_move(int kind, int a, int b, int w) {
    if (kind == 0) { del_edge(a, w); add_edge(a, b); }
    else if (kind == 1) { del_edge(a, b); }
    else { add_edge(a, b); }
}

/* Attach the newest (isolated) vertex x = n-1 greedily, judged by bad pairs. */
static void grow_attach(void) {
    int x = n - 1;
    for (int e = 0; e < d; e++) {
        int bc = -1, bb = 1 << 30;
        for (int t = 0; t < 24; t++) {
            int c = rint_(n);
            if (c == x || col[c] == col[x] || deg[c] >= d || has_edge(x, c)) continue;
            add_edge(x, c);
            int b = bad_pairs(NULL, NULL);
            del_edge(x, c);
            if (b < bb) { bb = b; bc = c; }
        }
        if (bc < 0) break;
        add_edge(x, bc);
    }
}

static void phase_sa(double until) {
    int bad = bad_pairs(curbl, &ncurbl);
    long it = 0;
    for (;;) {
        if ((it & 127) == 0 && elapsed() > until) break;
        it++;
        if (bad == 0) {
            save_state();
            if (n >= MAXN - 2) break;
            col[n] = (int)(rnd64() & 1);
            deg[n] = 0;
            n++;
            grow_attach();
            bad = bad_pairs(curbl, &ncurbl);
            continue;
        }
        double phase = (double)(it % 60000) / 60000.0;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);
        int kind = 0, ma = 0, mb = 0, mw = -1;
        if (!do_move(&kind, &ma, &mb, &mw)) continue;
        int nbad = bad_pairs(tmpbl, &ntmp);
        int delta = nbad - bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            bad = nbad;
            memcpy(curbl, tmpbl, sizeof(int) * (size_t)ntmp);
            ncurbl = ntmp;
        } else {
            undo_move(kind, ma, mb, mw);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double total = atof(argv[4]);
    double frac = atof(argv[5]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    T0 = clock();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 300 || M0 < 0) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    save_state();
    int b0 = bad_pairs(curbl, &ncurbl);
    if (b0 == 0) phase_insert(total * frac);
    phase_sa(total);

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) (points 0..m-1, lines m..2m-1). Each vertex has degree q+1,
# so spare capacity is s = d - q - 1. Choose SA (points) and SB (lines):
#   every SA point P gets a new vertex joined to the q+1 lines through P,
#   every SB line j gets a new vertex joined to the q+1 points on j,
# with every line hit by <= s chosen points and every point hit by <= s chosen lines.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomised greedy choice of elements with all target loads <= s."""
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
    """Plateau/improvement search for the same load-constrained set problem."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d, largest bound first."""
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
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
# C run wrapper.
# ----------------------------------------------------------------------------

def _c_improve(graph, d, D, seed, budget, frac):
    """Run the C engine from graph within `budget` seconds of C time; return (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), frac],
                        stdin_graph=(graph[0], list(graph[1])), timeout=budget + 3.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Build
# Time plan (fractions of time_limit, with a safety margin):
#   0.00-0.25  arc-extended PG graphs with local search (SA and SB independent)
#   0.25-0.30  GQ baseline for D >= 4
#   rest       C engine: insertion phase (35% of its budget), then bad-pair annealing
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit - 2.0
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    if D >= 3:
        arc_end = t0 + 0.25 * time_limit
        cands = _arc_extensions(d, arc_end, random.Random(seed * 7919 + d))
        cands.sort(key=lambda g: -g[0])
        for g in cands[:3]:
            consider(g)

    if D >= 4 and time.monotonic() < t0 + 0.30 * time_limit:
        consider(_best_gq(d))

    if D >= 2 and best[0] < lib.moore_bound(d, D):
        budget = end - time.monotonic()
        if budget > 1.0:
            consider(_c_improve(best, d, D, seed, budget, 0.35))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])

