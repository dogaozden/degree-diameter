import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates (parent engine).
#
# Let R = D-1. A new vertex w joined to a set N of vertices on the opposite
# colour class is within distance D of every old vertex x whenever x lies in
# the R-ball of some u in N. Adding a vertex never increases distances between
# old vertices, and cross edges between colour classes only shrink distances,
# so the graph stays valid. The engine repeats:
#   1. compute R-balls as bitsets,
#   2. for each colour class, greedily cover all vertices with spare-degree
#      neighbours (randomized tie-breaks), and insert a vertex on success,
#   3. on failure add a random spare cross edge to change the spare pattern.
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
# NEW C engine: pairwise-intersecting cover families by simulated annealing.
#
# Problem: blocks b = 0..NB-1, each a subset of elements 0..NE-1. Choose K
# families (sets) of SZ distinct blocks each such that
#   (a) every family covers all elements,
#   (b) every two families share a block,
#   (c) every block belongs to at most CAP families.
# Cost = uncovered element count + PAIRW per non-intersecting pair
#        + CAPW per unit of capacity overflow. Cost 0 means feasible.
# Moves replace one member of one family; half of the moves target an
# uncovered element of that family.
# Input (stdin): a graph-format header "n m" followed by 2m integers forming
# the stream: NB NE, then for each block "len e1 .. elen", then I, then I
# initial families of SZ blocks each (I may be 0).
# Output: "OK" then K*SZ block indices, or "FAIL".
# ----------------------------------------------------------------------------

C_COVER_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXB 640
#define MAXW 10
#define MAXK 40
#define MAXSZ 40
#define MAXDEG 64
#define MAXIN 200000
#define PAIRW 3
#define CAPW 2

static int NB, NE, K, SZ, CAP, W;
static uint64_t elt[MAXB][MAXW];
static int einc[MAXB][MAXDEG];
static int ninc[MAXB];
static int mem[MAXK][MAXSZ];
static int bestmem[MAXK][MAXSZ];
static uint64_t smask[MAXK][MAXW];
static int use[MAXB];
static uint64_t rs = 88172645463325252ULL;
static int X[MAXIN];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int rndint(int n) { return (int)(rnd() % (uint32_t)n); }

static double urand(void) { return ((double)rnd() + 0.5) / 4294967296.0; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int in_set(int i, int b) {
    return (int)((smask[i][b >> 6] >> (b & 63)) & 1ULL);
}

static void rebuild(void) {
    memset(use, 0, sizeof(use));
    for (int i = 0; i < K; i++) {
        memset(smask[i], 0, sizeof(smask[i]));
        for (int p = 0; p < SZ; p++) {
            int b = mem[i][p];
            smask[i][b >> 6] |= 1ULL << (b & 63);
            use[b]++;
        }
    }
}

static void cover_of(int i, uint64_t *cov) {
    for (int w = 0; w < W; w++) cov[w] = 0;
    for (int p = 0; p < SZ; p++) {
        const uint64_t *e = elt[mem[i][p]];
        for (int w = 0; w < W; w++) cov[w] |= e[w];
    }
}

static long cost_full(void) {
    long c = 0;
    uint64_t cov[MAXW];
    for (int i = 0; i < K; i++) {
        cover_of(i, cov);
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc(cov[w]);
        c += NE - cnt;
    }
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            int any = 0;
            for (int w = 0; w < W; w++)
                if (smask[i][w] & smask[j][w]) { any = 1; break; }
            if (!any) c += PAIRW;
        }
    for (int b = 0; b < NB; b++)
        if (use[b] > CAP) c += (long)(use[b] - CAP) * CAPW;
    return c;
}

static void fix_set(int i) {
    for (int p = 0; p < SZ; p++) {
        int bad;
        do {
            bad = 0;
            if (mem[i][p] < 0 || mem[i][p] >= NB) {
                bad = 1;
            } else {
                for (int q = 0; q < p; q++)
                    if (mem[i][q] == mem[i][p]) { bad = 1; break; }
            }
            if (bad) mem[i][p] = rndint(NB);
        } while (bad);
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("FAIL\n"); return 0; }
    K = atoi(argv[1]);
    SZ = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int hn, hm;
    if (scanf("%d %d", &hn, &hm) != 2) { printf("FAIL\n"); return 0; }
    int nx = 0;
    for (int i = 0; i < 2 * hm && nx < MAXIN; i++) {
        if (scanf("%d", &X[nx]) != 1) break;
        nx++;
    }
    if (nx < 2 || K < 1 || K > MAXK || SZ < 1 || SZ > MAXSZ || CAP < 0) {
        printf("FAIL\n");
        return 0;
    }
    NB = X[0];
    NE = X[1];
    if (NB < 1 || NB > MAXB || NE < 1 || NE > MAXB || SZ > NB) {
        printf("FAIL\n");
        return 0;
    }
    W = (NB > NE ? NB : NE);
    W = (W + 63) >> 6;
    int idx = 2;
    for (int b = 0; b < NB; b++) {
        if (idx >= nx) { printf("FAIL\n"); return 0; }
        int c = X[idx++];
        for (int t = 0; t < c; t++) {
            if (idx >= nx) { printf("FAIL\n"); return 0; }
            int e = X[idx++];
            if (e < 0 || e >= NE) continue;
            elt[b][e >> 6] |= 1ULL << (e & 63);
            if (ninc[e] < MAXDEG) einc[e][ninc[e]++] = b;
        }
    }

    int I = 0;
    if (idx < nx) I = X[idx++];
    for (int i = 0; i < K; i++)
        for (int p = 0; p < SZ; p++) {
            if (i < I && idx < nx) mem[i][p] = X[idx++];
            else mem[i][p] = -1;
        }
    for (int i = 0; i < K; i++) fix_set(i);
    rebuild();

    long cost = cost_full();
    long best = cost;
    memcpy(bestmem, mem, sizeof(mem));

    clock_t t0 = clock();
    const double T0 = 2.5, T1 = 0.08;
    const long CYC = 300000;
    long it = 0;
    uint64_t cov[MAXW];
    static int cand[MAXB];

    while (best > 0) {
        if ((it & 255) == 0 &&
            (double)(clock() - t0) / CLOCKS_PER_SEC > budget)
            break;
        long ci = it % CYC;
        double T = T0 * pow(T1 / T0, (double)ci / (double)CYC);
        it++;
        int i = rndint(K);
        int p = rndint(SZ);
        int b = -1;
        if (rnd() & 1u) {
            cover_of(i, cov);
            int nc = 0;
            for (int e = 0; e < NE; e++)
                if (!((cov[e >> 6] >> (e & 63)) & 1ULL)) cand[nc++] = e;
            if (nc > 0) {
                int e = cand[rndint(nc)];
                if (ninc[e] > 0) b = einc[e][rndint(ninc[e])];
            }
        }
        if (b < 0) b = rndint(NB);
        if (in_set(i, b)) continue;
        int old = mem[i][p];
        mem[i][p] = b;
        rebuild();
        long c2 = cost_full();
        long dl = c2 - cost;
        if (dl <= 0 || urand() < exp(-(double)dl / T)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                memcpy(bestmem, mem, sizeof(mem));
            }
        } else {
            mem[i][p] = old;
            rebuild();
        }
    }

    if (best == 0) {
        printf("OK");
        for (int i = 0; i < K; i++)
            for (int p = 0; p < SZ; p++) printf(" %d", bestmem[i][p]);
        printf("\n");
    } else {
        printf("FAIL\n");
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


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3, parent idea).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1.
#
# A-side: a set SA of points; each P in SA gets a new vertex joined to the q+1
# lines through P. Every line may hold at most s points of SA.
# B-side: a set SB of lines; each j in SB gets a new vertex joined to the q+1
# points on j. Every point may lie on at most s lines of SB.
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


# ----------------------------------------------------------------------------
# NEW construction: pairwise-intersecting cover families on PG(2, q).
#
# Add an A-vertex x for every family N_x of lines such that
#   * N_x covers all points (every point lies on a line of N_x),
#   * any two families N_x, N_x' share a line (so x, x' are at distance 2),
#   * each line lies in at most s families (its spare degree).
# Dually, add B-vertices y for families N_y of points that cover all lines,
# pairwise share a point, and use each point at most s times.
#
# Why diameter 3 holds (old vertices keep distances <= 3 among themselves):
#   x to old point P:   x - L - P with L in N_x through P (N_x covers points).
#   x to old line M:    x - L - Q - M with L in N_x, Q = L meet M.
#   x to y:             x - L - Q - y, where L in N_x contains a point Q of N_y
#                       (N_y covers lines, so L does).
#   x to x':            common line (pairwise intersecting).
# The oval pencils of the parent are the special case N_x = star(P), P on a conic.
# Here families are found by annealing, so families need not be pencils.
# Counting shows a side can reach about q+4 families for d = q+3 (not only q+1),
# which gives 2(q^2+q+1) + KA + KB vertices and beats the oval whenever KA+KB > 2(q+1).
# ----------------------------------------------------------------------------

def _cover_family(blocks, NE, K, sz, cap, seed, budget):
    """Ask the C annealer for K families of sz blocks, each covering all NE elements.

    blocks[b] lists the elements of block b. Returns a list of K lists of block
    indices, or None if the search failed within budget.
    """
    ints = [len(blocks), NE]
    for b in blocks:
        ints.append(len(b))
        ints.extend(b)
    ints.append(0)  # no initial family: random start
    if len(ints) % 2:
        ints.append(0)
    pairs = [(ints[i], ints[i + 1]) for i in range(0, len(ints), 2)]
    try:
        out = lib.run_c(C_COVER_SOURCE, [K, sz, cap, seed, round(budget, 2)],
                        stdin_graph=(1, pairs), timeout=budget + 5.0)
    except Exception:
        return None
    tok = out.split()
    if len(tok) != 1 + K * sz or tok[0] != "OK":
        return None
    try:
        vals = [int(t) for t in tok[1:]]
    except ValueError:
        return None
    return [vals[i * sz:(i + 1) * sz] for i in range(K)]


def _grow_side(blocks, NE, base, sz, cap, deadline, seed):
    """Grow one side's family by one set at a time while the annealer succeeds."""
    cur = [list(s) for s in base]
    while True:
        remaining = deadline - time.monotonic()
        K = len(cur) + 1
        if remaining < 2.0 or K * sz > cap * NE or K > 40:
            break
        fam = _cover_family(blocks, NE, K, sz, cap, seed + 101 * K, 0.45 * remaining)
        if fam is None:
            break
        cur = fam
    return cur


def _cover_graph(m, edges, FA, FB):
    """Attach an A-vertex per family of lines and a B-vertex per family of points."""
    n = 2 * m
    E = list(edges)
    for t, S in enumerate(FA):
        x = n + t
        for L in S:
            E.append((x, m + L))
    n += len(FA)
    for t, S in enumerate(FB):
        y = n + t
        for P in S:
            E.append((P, y))
    n += len(FB)
    return n, E


def _cover_extension(d, best_n, deadline, seed):
    """Return candidate graphs from cover-family growth on PG(2, q) for each useful q."""
    out = []
    qs = sorted((q for q in range(3, min(d - 1, 23) + 1) if lib.is_prime_power(q)),
                reverse=True)
    for q in qs:
        s = d - q - 1
        if s < 1:
            continue
        if time.monotonic() > deadline - 3.0:
            break
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        sz = d
        bound = (s * m) // sz  # each family uses sz units of spare capacity
        if 2 * m + 2 * bound <= best_n:
            continue
        cs = _conic_set(q, index, lib.GF(q))
        base_A = [list(point_lines[P]) for P in cs]    # pencils (blocks = lines)
        base_B = [list(line_points[j]) for j in cs]    # points on lines (blocks = points)
        blocks_A = [list(line_points[L]) for L in range(m)]   # block L -> points on L
        blocks_B = [list(point_lines[P]) for P in range(m)]   # block P -> lines through P
        FA = _grow_side(blocks_A, m, base_A, sz, s, deadline, seed * 31 + 1)
        FB = _grow_side(blocks_B, m, base_B, sz, s, deadline, seed * 31 + 2)
        out.append(_cover_graph(m, edges, FA, FB))
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
# Simulated annealing over bi-Cayley voltage lifts (parent, used for D != 3).
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
# Driver. Time plan (fractions of time_limit):
#   D == 3:
#     0.00-0.05  parent arc-extended PG graphs (oval families)
#     0.05-0.85  cover-family growth on PG(2, q) (new), starting from the oval
#     0.85-0.93  C greedy insertion on the best graph so far
#   D != 3 (parent behaviour):
#     0.00-0.40  generalized quadrangle baseline (D >= 4)
#     0.00-0.70  annealed group voltage lifts
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

    if D == 3:
        arcs = _arc_extensions(d, start + 0.05 * time_limit,
                               random.Random(seed * 7919 + d))
        for g in sorted(arcs, key=lambda t: -t[0]):
            consider(g)
        for g in _cover_extension(d, best_n, start + 0.85 * time_limit, seed):
            consider(g)
        rem = 0.93 * time_limit - elapsed()
        if rem > 1.0:
            consider(_c_augment(best, d, D, seed + 1, rem))
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
