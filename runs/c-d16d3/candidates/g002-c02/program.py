import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: double-edge-swap annealing with greedy ball-cover vertex insertion.
#
# The state is a bipartite graph with max degree d. Cost = number of unordered
# pairs at distance > D (bitset balls). Vertex insertion: a new vertex w of
# colour s takes neighbours of colour 1-s chosen greedily to cover the
# (D-1)-balls of all vertices, so the new vertex reaches everything within D.
# When cost hits 0 the graph is valid and is saved, then a vertex is inserted.
# Moves are degree-preserving double-edge swaps, one-end rewires and free edge
# additions. Metropolis acceptance. After a long stall the best valid graph is
# restored and insertion is retried with new random tie-breaks.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXD 64
#define WN ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXD / 2)
#define STALL 8000

static int n, d, D;
static int deg[MAXN];
static int adjv[MAXN][MAXD];
static int col[MAXN];
static uint64_t BA[MAXN][WN], BB[MAXN][WN], BR[MAXN][WN];
static int bestn = 0, bestm = 0;
static int bestU[MAXE], bestV[MAXE];
static uint64_t rs = 1;
static int mv_type, ma, mb, mc, me;
static int qbuf[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static unsigned rndu(void) { return (unsigned)(rnd64() >> 33); }
static double urand(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adjv[a][i] == b) return 1;
    return 0;
}
static void rm_from(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void add_edge(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}
static void del_edge(int a, int b) {
    rm_from(a, b);
    rm_from(b, a);
}

/* out[v] = bitset of vertices within distance R of v. */
static void balls(int R, uint64_t out[][WN]) {
    int nw = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(out[v], 0, sizeof(uint64_t) * WN);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(BB[v], out[v], sizeof(uint64_t) * nw);
            for (int i = 0; i < deg[v]; i++) {
                int u = adjv[v][i];
                for (int w = 0; w < nw; w++) BB[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < n; v++) memcpy(out[v], BB[v], sizeof(uint64_t) * nw);
    }
}

static long compute_bad(void) {
    int nw = (n + 63) / 64;
    balls(D, BA);
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(BA[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void save_best(void) {
    int m2 = 0;
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adjv[v][i];
            if (u > v && m2 < MAXE) {
                bestU[m2] = v;
                bestV[m2] = u;
                m2++;
            }
        }
    }
    bestn = n;
    bestm = m2;
}

static void restore_best(void) {
    n = bestn;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < bestm; i++) add_edge(bestU[i], bestV[i]);
}

/* Insert a vertex whose neighbourhood greedily covers the (D-1)-balls. */
static int insert_vertex(void) {
    if (n >= MAXN - 1) return 0;
    int s = (int)(rndu() & 1);
    int ncand = 0;
    for (int u = 0; u < n; u++) if (col[u] != s && deg[u] < d) ncand++;
    int tries = 0;
    while (ncand < d / 2 && tries < 20 * n) {
        tries++;
        int a = (int)(rndu() % (unsigned)n);
        if (col[a] == s || deg[a] < d) continue;
        int b = adjv[a][rndu() % (unsigned)deg[a]];
        del_edge(a, b);
        ncand++;
    }
    static int cand[MAXN];
    static int taken[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++) if (col[u] != s && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rndu() % (unsigned)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    balls(D - 1, BR);
    int nw = (n + 63) / 64;
    uint64_t U[WN];
    memset(U, 0, sizeof(U));
    for (int v = 0; v < n; v++) U[v >> 6] |= 1ULL << (v & 63);
    memset(taken, 0, sizeof(int) * nc);
    int chosen[MAXD];
    int k = 0;
    while (k < d) {
        int bi = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            if (taken[i]) continue;
            int u = cand[i];
            int g = 0;
            for (int w = 0; w < nw; w++) g += pc64(BR[u][w] & U[w]);
            if (g > bg) { bg = g; bi = i; }
        }
        if (bi < 0) break;
        taken[bi] = 1;
        int u = cand[bi];
        chosen[k++] = u;
        for (int w = 0; w < nw; w++) U[w] &= ~BR[u][w];
    }
    if (k == 0) return 0;
    int w = n++;
    deg[w] = 0;
    col[w] = s;
    for (int i = 0; i < k; i++) add_edge(chosen[i], w);
    return 1;
}

static int try_move(void) {
    int r = (int)(rndu() % 100);
    if (r < 60) {
        int a = (int)(rndu() % (unsigned)n);
        if (deg[a] == 0) return 0;
        int b = adjv[a][rndu() % (unsigned)deg[a]];
        int c = (int)(rndu() % (unsigned)n);
        if (c == a || col[c] != col[a] || deg[c] == 0) return 0;
        int e = adjv[c][rndu() % (unsigned)deg[c]];
        if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        mv_type = 1; ma = a; mb = b; mc = c; me = e;
        return 1;
    } else if (r < 85) {
        int a = (int)(rndu() % (unsigned)n);
        if (deg[a] == 0) return 0;
        int b = adjv[a][rndu() % (unsigned)deg[a]];
        int c = (int)(rndu() % (unsigned)n);
        if (c == b || col[c] != col[b] || deg[c] >= d || has_edge(a, c)) return 0;
        del_edge(a, b);
        add_edge(a, c);
        mv_type = 2; ma = a; mb = b; mc = c;
        return 1;
    } else {
        int a = (int)(rndu() % (unsigned)n);
        if (deg[a] >= d) return 0;
        int c = (int)(rndu() % (unsigned)n);
        if (c == a || col[c] == col[a] || deg[c] >= d || has_edge(a, c)) return 0;
        add_edge(a, c);
        mv_type = 3; ma = a; mb = c;
        return 1;
    }
}

static void undo(void) {
    if (mv_type == 1) {
        del_edge(ma, me);
        del_edge(mc, mb);
        add_edge(ma, mb);
        add_edge(mc, me);
    } else if (mv_type == 2) {
        del_edge(ma, mc);
        add_edge(ma, mb);
    } else if (mv_type == 3) {
        del_edge(ma, mb);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();
    if (d < 1 || d > MAXD - 1 || D < 2) { printf("0 0\n"); return 0; }

    int m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) { deg[v] = 0; col[v] = 0; }
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || has_edge(u, v) ||
            deg[u] >= d || deg[v] >= d) { ok = 0; break; }
        add_edge(u, v);
    }
    if (ok) {
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s0 = 0; s0 < n && ok; s0++) {
            if (col[s0] >= 0) continue;
            col[s0] = 0;
            int qh = 0, qt = 0;
            qbuf[qt++] = s0;
            while (qh < qt && ok) {
                int x = qbuf[qh++];
                for (int i = 0; i < deg[x]; i++) {
                    int y = adjv[x][i];
                    if (col[y] < 0) {
                        col[y] = 1 - col[x];
                        qbuf[qt++] = y;
                    } else if (col[y] == col[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    long cur = compute_bad();
    if (cur == 0) save_best();
    long iter = 0, since = 0;
    while (1) {
        if ((iter & 31) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC >= tl) break;
        iter++;
        if (cur == 0) {
            if (n > bestn) save_best();
            if (insert_vertex()) {
                cur = compute_bad();
                since = 0;
                continue;
            }
        }
        since++;
        if (bestn > 0 && since > STALL) {
            restore_best();
            cur = compute_bad();
            since = 0;
            continue;
        }
        double T = 0.25 + 0.75 * exp(-(double)since / 1500.0);
        if (!try_move()) continue;
        long nc = compute_bad();
        long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            if (nc < cur) since = 0;
            cur = nc;
        } else {
            undo();
        }
    }
    if (cur == 0 && n > bestn) save_best();
    if (bestn == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestn, bestm);
    for (int i = 0; i < bestm; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective plane graphs (D = 3),
# Araujo-Lopez graphs, and the generalized quadrangle W(q) (D = 4).
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build: best Python start graph, then the C annealing/insertion engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.90 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, t0 + 0.10 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(arcs, key=lambda t: -t[0])[:3]:
            consider(n_c, e_c)
        # Araujo-Lopez graphs of degree q+2 <= d (diameter 3).
        for q in range(3, d - 1):
            if time.monotonic() > t0 + 0.15 * time_limit:
                break
            if lib.is_prime_power(q):
                consider(*lib.araujo_lopez_graph(q))

    if D >= 4 and time.monotonic() < t0 + 0.15 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)

    # C engine: insertion + degree-preserving annealing, starting from the best graph.
    budget = deadline - time.monotonic() - 1.0
    if d <= 3:
        budget = min(budget, 5.0)
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5.0)
            consider(*lib.parse_graph_text(text))
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
