import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: greedy vertex insertion with ball-cover certificates (unchanged).
#
# Let R = D-1. A new vertex w joined to a set N of vertices on the opposite
# colour class is within distance D of every old vertex x whenever x lies in
# the R-ball of some u in N. Adding a vertex never increases distances between
# old vertices, so the graph stays valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
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

static int try_insert(int side) {
    int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    static int used[MAXN];
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    W = (n + 63) >> 6;
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
                }
            }
        }
    }

    clock_t t0 = clock();
    int fails = 0;
    const int maxfails = 200;
    while (fails < maxfails && n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = (int)(rnd() % (uint32_t)n);
            int v = (int)(rnd() % (uint32_t)n);
            if (u == v || col[u] == col[v]) continue;
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            break;
        }
    }

    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (new): cover-family search.
#
# Setting: elements E (|E| = M) and targets T (|T| = T); element e covers the
# targets etg[e]. A "cover family" is K subsets C_1..C_K of E such that
#   (a) every C_i covers all targets,
#   (b) |C_i| <= TMAX,
#   (c) any two C_i, C_j share an element,
#   (d) every element lies in at most S of the C_i.
# Used for diameter 3 with PG(2,q): a new vertex on the point side is joined to
# a cover C of lines (so every point is 2 away, every line 3 away); two new
# point-side vertices need a common line (condition c); the load limit (d) is
# the spare degree d - (q+1). Pencils through arc points are one solution; this
# engine searches for general covers (non-pencils) that allow more vertices.
# Simulated annealing over the bits x[i][e], with an incremental cost
#   U (uncovered target-cover pairs) + NI (non-intersecting pairs)
#   + OV (load excess) + SO (size excess).
#
# stdin: "n m" header (ignored), then a flat payload of ints:
#   M T, then M element lists (count, targets...), then K0, then K0 covers
#   (count, elements...).
# argv: S TMAX seed budget maxK.   stdout: K, then K lines "count elements...".
# ----------------------------------------------------------------------------

C_COVER = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXI 64
#define MAXK 48
#define MAXB 200000

static int M, T, S, TMAX, K;
static int ecnt[MAXM];
static int etg[MAXM][MAXI];
static unsigned char x[MAXK][MAXM];
static int sz[MAXK];
static int cov[MAXK][MAXM];
static int inter[MAXK][MAXK];
static int load[MAXM];
static long U, NI, OV, SO;
static uint64_t rs = 88172645463325252ULL;
static int bestK = 0;
static int bestcnt[MAXK];
static int bestel[MAXK][MAXM];
static int buf[MAXB];
static int nb = 0, bp = 0;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static double urand(void) { return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0); }
static int irand(int n) { return (int)(nextr() % (uint64_t)n); }
static int getv(void) { return bp < nb ? buf[bp++] : 0; }

static long delta_flip(int i, int e) {
    int on = !x[i][e];
    long dU = 0, dNI = 0, dOV = 0, dSO = 0;
    if (on) {
        for (int a = 0; a < ecnt[e]; a++) if (cov[i][etg[e][a]] == 0) dU--;
    } else {
        for (int a = 0; a < ecnt[e]; a++) if (cov[i][etg[e][a]] == 1) dU++;
    }
    for (int j = 0; j < K; j++) {
        if (j == i || !x[j][e]) continue;
        if (on) { if (inter[i][j] == 0) dNI--; }
        else { if (inter[i][j] == 1) dNI++; }
    }
    if (on) {
        if (load[e] >= S) dOV++;
        if (sz[i] >= TMAX) dSO++;
    } else {
        if (load[e] > S) dOV--;
        if (sz[i] > TMAX) dSO--;
    }
    return dU + dNI + dOV + dSO;
}

static void apply_flip(int i, int e) {
    int on = !x[i][e];
    for (int a = 0; a < ecnt[e]; a++) {
        int t = etg[e][a];
        if (on) {
            if (cov[i][t] == 0) U--;
            cov[i][t]++;
        } else {
            cov[i][t]--;
            if (cov[i][t] == 0) U++;
        }
    }
    for (int j = 0; j < K; j++) {
        if (j == i || !x[j][e]) continue;
        if (on) {
            if (inter[i][j] == 0) NI--;
            inter[i][j]++;
            inter[j][i]++;
        } else {
            inter[i][j]--;
            inter[j][i]--;
            if (inter[i][j] == 0) NI++;
        }
    }
    if (on) {
        if (load[e] >= S) OV++;
        load[e]++;
        sz[i]++;
        if (sz[i] > TMAX) SO++;
    } else {
        load[e]--;
        if (load[e] >= S) OV--;
        sz[i]--;
        if (sz[i] >= TMAX) SO--;
    }
    x[i][e] = (unsigned char)on;
}

static void add_cover(void) {
    int i = K;
    K++;
    sz[i] = 0;
    for (int t = 0; t < T; t++) cov[i][t] = 0;
    for (int e = 0; e < M; e++) x[i][e] = 0;
    for (int j = 0; j <= i; j++) { inter[i][j] = 0; inter[j][i] = 0; }
    U += T;
    NI += i;
}

static void random_fill(int i, int cnt) {
    for (int r = 0; r < cnt; r++) {
        int e = irand(M);
        if (!x[i][e]) apply_flip(i, e);
    }
}

static void save_best(void) {
    bestK = K;
    for (int i = 0; i < K; i++) {
        int c = 0;
        for (int e = 0; e < M; e++) if (x[i][e]) bestel[i][c++] = e;
        bestcnt[i] = c;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    S = atoi(argv[1]);
    TMAX = atoi(argv[2]);
    rs ^= (uint64_t)strtoul(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    int maxK = atoi(argv[5]);
    if (maxK > MAXK) maxK = MAXK;
    if (maxK < 1) maxK = 1;

    int hn, hm;
    if (scanf("%d %d", &hn, &hm) != 2) { printf("0\n"); return 0; }
    int v;
    while (nb < MAXB && scanf("%d", &v) == 1) buf[nb++] = v;

    M = getv();
    T = getv();
    if (M < 1 || M > MAXM || T < 1 || T > MAXM) { printf("0\n"); return 0; }
    for (int e = 0; e < M; e++) {
        int c = getv();
        if (c < 0) c = 0;
        if (c > MAXI) c = MAXI;
        ecnt[e] = c;
        for (int a = 0; a < c; a++) {
            int t = getv();
            if (t < 0 || t >= T) t = 0;
            etg[e][a] = t;
        }
    }

    int K0 = getv();
    if (K0 < 0) K0 = 0;
    for (int i = 0; i < K0 && K < maxK; i++) {
        int c = getv();
        if (c < 0) c = 0;
        add_cover();
        for (int a = 0; a < c; a++) {
            int e = getv();
            if (e < 0 || e >= M) continue;
            if (!x[K - 1][e]) apply_flip(K - 1, e);
        }
    }

    clock_t t0 = clock();
    double Tc = 0.6;
    unsigned long it = 0;
    for (;;) {
        long cost = U + NI + OV + SO;
        if (cost == 0) {
            save_best();
            if (K >= maxK) break;
            add_cover();
            random_fill(K - 1, 12);
            Tc = 0.6;
            continue;
        }
        if ((it & 16383UL) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        int i = irand(K);
        int e = irand(M);
        long dl = delta_flip(i, e);
        if (dl <= 0 || urand() < exp(-(double)dl / Tc)) apply_flip(i, e);
        Tc *= 0.99998;
        if (Tc < 0.06) Tc = 0.6;
    }

    printf("%d\n", bestK);
    for (int i = 0; i < bestK; i++) {
        printf("%d", bestcnt[i]);
        for (int a = 0; a < bestcnt[i]; a++) printf(" %d", bestel[i][a]);
        printf("\n");
    }
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
    """Run the C insertion engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


def _pack(tokens):
    """Pack a flat int list into the edge-list stdin format (header "1 m", then pairs)."""
    if len(tokens) % 2:
        tokens = tokens + [0]
    return (1, [(tokens[i], tokens[i + 1]) for i in range(0, len(tokens), 2)])


def _cover_search(m, elem_targets, init, s, tmax, maxk, seed, budget):
    """Search cover families (see C_COVER). Returns list of covers (lists of element ids), or []."""
    tok = [m, m]
    for tg in elem_targets:
        tok.append(len(tg))
        tok.extend(int(t) for t in tg)
    tok.append(len(init))
    for cov in init:
        tok.append(len(cov))
        tok.extend(int(t) for t in cov)
    try:
        out = lib.run_c(C_COVER, [s, tmax, int(seed) % 1000003, round(budget, 2), maxk],
                        stdin_graph=_pack(tok), timeout=budget + 8.0)
        t = out.split()
        k = int(t[0])
        p = 1
        fam = []
        for _ in range(k):
            c = int(t[p])
            p += 1
            fam.append([int(v) for v in t[p:p + c]])
            p += c
        return fam
    except Exception:
        return []


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. New point-side vertex for a set of
# lines (cover) and new line-side vertex for a set of points (cover).
# The pencil-based version (arc sets) is the parent's baseline; the cover
# family search generalises it.
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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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


def _family_graph(m, edges, fam_a, fam_b):
    """PG(2,q) plus A-vertices (covers of lines) and B-vertices (covers of points)."""
    n = 2 * m + len(fam_a) + len(fam_b)
    E = list(edges)
    for t, cov in enumerate(fam_a):
        x = 2 * m + t
        for L in cov:
            E.append((x, m + L))
    base = 2 * m + len(fam_a)
    for t, cov in enumerate(fam_b):
        y = base + t
        for P in cov:
            E.append((P, y))
    return n, E


def _arc_sets(d, q, rng, deadline):
    """Return (m, edges, point_lines, line_points, SA, SB) for PG(2,q) with spare s = d-q-1, or None."""
    s = d - q - 1
    if s < 0:
        return None
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    SA = _greedy_side(m, s, point_lines, rng, 40, deadline) if s >= 1 else []
    SB = _greedy_side(m, s, line_points, rng, 40, deadline) if s >= 1 else []
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
            SA = cs
        if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
            SB = cs
    if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
        return None
    return m, edges, point_lines, line_points, SA, SB


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
# Simulated annealing over bi-Cayley voltage lifts (used for D != 3).
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nx = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nx.append(v)
            count += len(nx)
            frontier = nx
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
#
# D = 3: (1) pencil/arc baselines for every prime power q with q+1 <= d;
#        (2) cover-family search on the two best q, side A and side B
#            independently (each side's covers are a pairwise-intersecting
#            family with load <= spare), starting from the arc baseline;
#        (3) leftover time: greedy C insertion on the best graph.
# D != 3: parent's GQ baseline and voltage-lift annealing.
# Every candidate passes lib.is_valid before it can replace the best graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    searched = False
    if D == 3:
        arc_deadline = start + 0.10 * time_limit
        sets = []
        for q in range(2, min(d - 1, 23) + 1):
            if not lib.is_prime_power(q):
                continue
            if time.monotonic() > arc_deadline:
                break
            r = _arc_sets(d, q, random.Random(seed * 7919 + q), arc_deadline)
            if r is None:
                continue
            m, edges, pl, lp, SA, SB = r
            consider(_arc_graph(m, edges, pl, lp, SA, SB))
            sets.append((q, r))

        # Cover-family search on the two richest q with spare degree >= 1.
        ranked = sorted([x for x in sets if d - x[0] - 1 >= 1],
                        key=lambda x: -(2 * x[1][0] + len(x[1][4]) + len(x[1][5])))[:2]
        total = 0.72 * time_limit - elapsed()
        shares = [0.7, 0.3]
        for idx, (q, r) in enumerate(ranked):
            m, edges, pl, lp, SA, SB = r
            s = d - q - 1
            bud = total * shares[idx] / 2.0
            if bud < 1.0:
                break
            init_a = [pl[P] for P in SA]
            fam_a = _cover_search(m, lp, init_a, s, d, 40, seed + 11 * idx, bud)
            if len(fam_a) < len(init_a):
                fam_a = init_a
            init_b = [lp[j] for j in SB]
            fam_b = _cover_search(m, pl, init_b, s, d, 40, seed + 17 * idx + 1, bud)
            if len(fam_b) < len(init_b):
                fam_b = init_b
            consider(_family_graph(m, edges, fam_a, fam_b))
            searched = True

        if searched:
            rem = 0.88 * time_limit - elapsed()
            if rem > 1.0:
                consider(_c_augment(best, d, D, seed + 1, min(rem, 0.08 * time_limit)))
    else:
        if D >= 4 and elapsed() < 0.40 * time_limit:
            consider(_best_gq(d))
        anneal_end = start + 0.70 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
