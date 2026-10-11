import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair search for bipartite graphs with max degree d and
# diameter <= D.
#
# State: a valid-or-nearly-valid bipartite graph with per-vertex sides fixed.
# Moves:
#   * degree-preserving edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), annealed
#     on cost = number of ordered pairs at distance > D (bitset BFS);
#   * vertex-pair insertion (NEW): choose d disjoint edges (a_i,b_i), delete
#     them, add x (side A) joined to all b_i and y (side B) joined to all a_i.
#     Degrees are unchanged except x,y which get degree d, and x,y are at
#     distance 3 through (b_i, a_i). Best of several random matchings is kept.
#   * deficit filling: add any missing edge between an A and a B vertex that
#     both have spare degree (never increases distances).
# When cost reaches 0 the graph is saved and a pair is inserted; if the search
# stalls it restores the best saved graph and retries.
# ----------------------------------------------------------------------------
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1400
#define MAXW 22
#define MAXD 40
#define MAXE (MAXN * MAXD / 2 + 8)
#define GROW_TRIES 12
#define STAGE 12000

static int NV = 0, WD = 1, DEG = 0, DIAM = 1, CAP = MAXN;
static int side[MAXN], deg[MAXN], nb[MAXN][MAXD];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int stA[MAXN], stB[MAXN], stamp = 0;
static int bestN = 0, bestM = 0;
static int bu[MAXE], bv[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void set_NV(int n) { NV = n; WD = (n + 63) / 64; }

static void add_e(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = adjm[v][u] = 1;
}
static void rem_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; return; }
}
static void del_e(int u, int v) {
    rem_nb(u, v); rem_nb(v, u);
    adjm[u][v] = adjm[v][u] = 0;
}

static long compute_cost(void) {
    uint64_t (*cur)[MAXW] = RA, (*nxt)[MAXW] = RB;
    for (int v = 0; v < NV; v++) {
        for (int w = 0; w < WD; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DIAM; it++) {
        for (int v = 0; v < NV; v++) {
            for (int w = 0; w < WD; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < WD; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long cost = 0;
    for (int v = 0; v < NV; v++) {
        int c = 0;
        for (int w = 0; w < WD; w++) c += popc(cur[v][w]);
        cost += NV - c;
    }
    return cost;
}

static void fill_deficits(void) {
    for (int pass = 0; pass < 2; pass++) {
        for (int a = 0; a < NV; a++) {
            if (side[a] != 0 || deg[a] >= DEG) continue;
            int off = rndint(NV);
            for (int k = 0; k < NV && deg[a] < DEG; k++) {
                int b = (off + k) % NV;
                if (side[b] == 1 && deg[b] < DEG && !adjm[a][b]) add_e(a, b);
            }
        }
    }
}

static int rand_side(int s) {
    for (int t = 0; t < 400; t++) {
        int v = rndint(NV);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

static int pick_matching(int *ua, int *ub) {
    stamp++;
    int k = 0;
    for (int t = 0; t < 4000 && k < DEG; t++) {
        int a = rand_side(0);
        if (a < 0) break;
        int b = nb[a][rndint(deg[a])];
        if (stA[a] == stamp || stB[b] == stamp) continue;
        stA[a] = stamp;
        stB[b] = stamp;
        ua[k] = a;
        ub[k] = b;
        k++;
    }
    return k == DEG;
}

static void apply_pair(const int *ua, const int *ub) {
    int x = NV, y = NV + 1;
    side[x] = 0;
    side[y] = 1;
    set_NV(NV + 2);
    for (int i = 0; i < DEG; i++) {
        del_e(ua[i], ub[i]);
        add_e(x, ub[i]);
        add_e(y, ua[i]);
    }
}

static void undo_pair(const int *ua, const int *ub) {
    int x = NV - 2, y = NV - 1;
    for (int i = 0; i < DEG; i++) {
        del_e(x, ub[i]);
        del_e(y, ua[i]);
        add_e(ua[i], ub[i]);
    }
    set_NV(NV - 2);
}

static void save_best(void) {
    bestN = NV;
    bestM = 0;
    for (int v = 0; v < NV; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (v < u) { bu[bestM] = v; bv[bestM] = u; bestM++; }
        }
}

static void load_graph(int n, int m, const int *eu, const int *ev) {
    memset(adjm, 0, sizeof adjm);
    for (int v = 0; v < MAXN; v++) deg[v] = 0;
    set_NV(n);
    for (int i = 0; i < m; i++) add_e(eu[i], ev[i]);
}

static int grow(void) {
    if (NV + 2 > CAP) return 0;
    int ua[MAXD], ub[MAXD], ba[MAXD], bb[MAXD];
    int have = 0;
    long bestc = 0;
    for (int t = 0; t < GROW_TRIES; t++) {
        if (!pick_matching(ua, ub)) continue;
        apply_pair(ua, ub);
        long c = compute_cost();
        undo_pair(ua, ub);
        if (!have || c < bestc) {
            have = 1;
            bestc = c;
            memcpy(ba, ua, sizeof(int) * DEG);
            memcpy(bb, ub, sizeof(int) * DEG);
        }
    }
    if (!have) return 0;
    apply_pair(ba, bb);
    fill_deficits();
    return 1;
}

static long step(long cur, double T) {
    int a1 = rand_side(0), a2 = rand_side(0);
    if (a1 < 0 || a2 < 0) return cur;
    int b1 = nb[a1][rndint(deg[a1])];
    int b2 = nb[a2][rndint(deg[a2])];
    if (a1 == a2 || b1 == b2 || adjm[a1][b2] || adjm[a2][b1]) return cur;
    del_e(a1, b1);
    del_e(a2, b2);
    add_e(a1, b2);
    add_e(a2, b1);
    long c = compute_cost();
    int acc = (c <= cur) || (rnd01() < exp(-(double)(c - cur) / T));
    if (acc) return c;
    del_e(a1, b2);
    del_e(a2, b1);
    add_e(a1, b1);
    add_e(a2, b2);
    return cur;
}

static long moore_bound(int d, int D) {
    if (d <= 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    clock_t t0 = clock();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 2 || m < 0 ||
        d < 1 || d >= MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    DEG = d;
    set_NV(n);
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
            deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_e(u, v);
    }
    /* bipartition by BFS; reject non-bipartite input */
    for (int v = 0; v < n; v++) side[v] = -1;
    static int qu[MAXN];
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int x = qu[h++];
            for (int k = 0; k < deg[x]; k++) {
                int y = nb[x][k];
                if (side[y] < 0) { side[y] = 1 - side[x]; qu[t++] = y; }
                else if (side[y] == side[x]) { printf("0 0\n"); return 0; }
            }
        }
    }

    long moore = moore_bound(d, DIAM);
    CAP = (moore < MAXN) ? (int)moore : MAXN;

    fill_deficits();
    long cost = compute_cost();
    if (cost == 0) save_best();

    int stage = 0;
    long it = 0;
    while (1) {
        if ((it & 15) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        if (cost == 0) {
            if (NV > bestN) save_best();
            if (NV + 2 > CAP) break;
            if (!grow()) break;
            cost = compute_cost();
            stage = 0;
            continue;
        }
        stage++;
        if (stage > STAGE) {
            if (bestM > 0) load_graph(bestN, bestM, bu, bv);
            cost = compute_cost();
            stage = 0;
            continue;
        }
        double T = 2.0 * (1.0 - (double)stage / STAGE) + 0.02;
        cost = step(cost, T);
    }
    if (cost == 0 && NV > bestN) save_best();

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""

MAX_C_N = 1300


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials):
    """Randomized greedy set S with all loads <= s; the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per point of S (joined to its lines) and a new B-vertex per point of S (joined to its line points)."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, y))
    return 2 * m + 2 * k, E


def _arc_candidates(d, rng):
    """Arc-extended graphs for each prime power q <= d - 1 (valid for D >= 3)."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        m, edges, pl, lp, index = _pg(q)
        if s == 0:
            S = []
        else:
            cands = [_greedy_arc(m, s, pl, lp, rng, 40)]
            if s >= 2:
                cs = _conic_set(q, index, lib.GF(q))
                if _loads_ok(cs, s, m, pl, lp):
                    cands.append(cs)
            S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for cand in _arc_candidates(d, random.Random(seed * 7919 + d)):
            consider(cand)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # C grow-and-repair search from the best construction.
    elapsed = time.monotonic() - t0
    budget = 0.72 * time_limit - elapsed - 1.0
    if (budget >= 2.0 and d < 40 and best[0] <= MAX_C_N
            and best[0] + 2 <= lib.moore_bound(d, D)):
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 0.2 * time_limit)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
