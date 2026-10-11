import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing at a fixed vertex count with degree-preserving
# bipartite edge switches. Cost = number of unordered pairs at distance > D.
# Each time cost reaches 0 the engine saves the graph and adds one isolated
# vertex. On stagnation it restarts from the best saved graph, perturbed by
# random switches. Output is always an edge list that Python re-validates.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define DCAP 32
#define MAXE 16384
#define STALL 30000
#define CYC 120000

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];
static int vis[MAXN];
static int queue_[MAXN];
static uint64_t rs = 1;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc64(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

static int bad_pairs(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(RA[v]));
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (v > u && m < MAXE) { bestU[m] = u; bestV[m] = v; m++; }
        }
    }
    bestN = n; bestM = m;
}

static int color_graph(void) {
    int iso = 0;
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        if (deg[s] == 0) { vis[s] = 1; side[s] = (iso++) & 1; continue; }
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; queue_[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

static int load_edges(int N, int M, const int *U, const int *V) {
    if (N < 1 || N > MAXN - 8) return 0;
    n = N;
    memset(adjm, 0, sizeof adjm);
    for (int u = 0; u < n; u++) deg[u] = 0;
    for (int i = 0; i < M; i++) {
        int u = U[i], v = V[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            adjm[u][v] || deg[u] >= d || deg[v] >= d) return 0;
        add_edge(u, v);
    }
    return color_graph();
}

static void add_isolated(void) {
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) { if (side[v] == 0) c0++; else c1++; }
    side[n] = (c0 <= c1) ? 0 : 1;
    deg[n] = 0;
    n++;
}

/* x -- y and z -- w (same side x,z; y,w opposite) become x -- w and z -- y. */
static int move_switch(int *o1, int *o2, int *o3, int *o4) {
    int x = -1, z = -1;
    for (int t = 0; t < 64 && x < 0; t++) { int c = rint_(n); if (deg[c] > 0) x = c; }
    if (x < 0) return 0;
    for (int t = 0; t < 64 && z < 0; t++) {
        int c = rint_(n);
        if (c != x && side[c] == side[x] && deg[c] > 0) z = c;
    }
    if (z < 0) return 0;
    int y = nb[x][rint_(deg[x])];
    int w = nb[z][rint_(deg[z])];
    if (y == w || adjm[x][w] || adjm[z][y]) return 0;
    del_edge(x, y); del_edge(z, w);
    add_edge(x, w); add_edge(z, y);
    *o1 = x; *o2 = y; *o3 = z; *o4 = w;
    return 1;
}

static int move_add(int *o1, int *o2) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) { int c = rint_(n); if (deg[c] < d) { x = c; break; } }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *o1 = x; *o2 = y;
    return 1;
}

static int move_remove(int *o1, int *o2) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) { int c = rint_(n); if (deg[c] > 0) a = c; }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    *o1 = a; *o2 = b;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) return 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { m0 = i; break; }
    }

    if (d < 1 || d > DCAP || D < 1 || !load_edges(n0, m0, iu, iv) || bad_pairs() != 0) {
        /* Start graph unusable: echo it back so Python keeps its own fallback. */
        printf("%d %d\n", n0, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }
    save_best();
    add_isolated();

    long it = 0, cyc_start = 0, last_imp = 0;
    int cur = bad_pairs();
    int cyc_min = cur;

    for (;;) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur == 0) {
            save_best();
            if (n >= MAXN - 4) break;
            add_isolated();
            cur = bad_pairs();
            cyc_min = cur;
            last_imp = it;
            cyc_start = it;
            continue;
        }

        if (it - last_imp > STALL) {
            if (!load_edges(bestN, bestM, bestU, bestV)) break;
            add_isolated();
            for (int t = 0; t < 40; t++) {
                int p1, p2, p3, p4;
                move_switch(&p1, &p2, &p3, &p4);
            }
            cur = bad_pairs();
            cyc_min = cur;
            last_imp = it;
            cyc_start = it;
            continue;
        }

        double phase = (double)((it - cyc_start) % CYC) / (double)CYC;
        double T = 0.1 + 0.9 * (1.0 - phase) * (1.0 - phase);

        int r = rint_(100);
        int kind = 0, applied = 0;
        int a = 0, b = 0, c = 0, e = 0;
        if (r < 60) { kind = 0; applied = move_switch(&a, &b, &c, &e); }
        else if (r < 85) { kind = 1; applied = move_add(&a, &b); }
        else { kind = 2; applied = move_remove(&a, &b); }
        if (!applied) continue;

        int nbad = bad_pairs();
        int delta = nbad - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nbad;
            if (cur < cyc_min) { cyc_min = cur; last_imp = it; }
        } else {
            if (kind == 0) {
                del_edge(a, e); del_edge(c, b);
                add_edge(a, b); add_edge(c, e);
            } else if (kind == 1) {
                del_edge(a, b);
            } else {
                add_edge(a, b);
            }
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (valid for D >= 3).
#
# Start from PG(2, q) incidence. Choose S (a set of points) so that every line
# holds <= s points of S and every point lies on <= s lines indexed by S, where
# s = d - q - 1 is the spare degree. Add an A-vertex on the point side joined to
# the lines through each P in S, and a B-vertex on the line side joined to the
# points of each line j in S.
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    if D >= 3:
        # Full projective plane PG(2, d-1) when d-1 is a prime power (meets the Moore bound).
        if d >= 3 and lib.is_prime_power(d - 1):
            consider(lib.projective_plane_incidence(d - 1))

        # Arc-extended projective plane graphs.
        if time.monotonic() < end:
            cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
            for g in sorted(cands, key=lambda t: -t[0]):
                consider(g)

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Bold step: grow the best valid graph by annealing with degree-preserving
    # bipartite switches, starting from one extra isolated vertex.
    cbudget = end - time.monotonic()
    if D >= 3 and d <= 32 and best[0] + 8 < 1000 and cbudget > 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget - 1.5, 2)],
                            stdin_graph=(best[0], list(best[1])),
                            timeout=cbudget + 5)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
