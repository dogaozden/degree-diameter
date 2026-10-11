import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define MAXD 64
#define MAXE (MAXN * MAXD)
#define STALL 60000L

static int d, D, n, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
#ifdef __GNUC__
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW], resBuf[MAXN * MAXW];
static int EU[MAXE], EV[MAXE], SU[MAXE], SV[MAXE];
static int snapN = 0, snapM = 0;

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_nbr(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) { adj[u][k] = adj[u][--deg[u]]; return; }
    }
}

static void remove_edge(int u, int v) {
    del_nbr(u, v);
    del_nbr(v, u);
}

/* Bitset of vertices within distance R of each vertex; stride W. */
static uint64_t *compute_ball(int R) {
    uint64_t *cur = bufA, *nxt = bufB;
    W = (n + 63) / 64;
    size_t tot = (size_t)n * W;
    memset(cur, 0, sizeof(uint64_t) * tot);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < R; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s2 = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    memcpy(resBuf, cur, sizeof(uint64_t) * tot);
    return resBuf;
}

/* Number of unordered pairs at distance > D. Zero means valid. */
static long eval_cost(void) {
    uint64_t *b = compute_ball(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = b + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pc64(row[w]);
        bad += n - c;
    }
    return bad / 2;
}

static int accept(long c, long c2, double T) {
    if (c2 <= c) return 1;
    return rndu() < exp(-(double)(c2 - c) / T);
}

/* Insert a new vertex on a random side, joined greedily to a cover of the old vertices. */
static void grow(void) {
    int w = n, s = rndi(2);
    n = n + 1;
    deg[w] = 0;
    col[w] = s;
    uint64_t *B = compute_ball(D - 1);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    static int used[MAXN];
    memset(used, 0, sizeof(int) * (size_t)n);
    int chosen[MAXD];
    int nc = 0;
    while (nc < d) {
        int bu = -1;
        long bk = -1;
        for (int u = 0; u < w; u++) {
            if (col[u] == s || used[u]) continue;
            const uint64_t *bb = B + (size_t)u * W;
            long g = 0;
            for (int x = 0; x < W; x++) g += pc64(bb[x] & ~cov[x]);
            long key = g * 4096 + rndi(4096);
            if (key > bk) { bk = key; bu = u; }
        }
        if (bu < 0) break;
        used[bu] = 1;
        chosen[nc++] = bu;
        const uint64_t *bb = B + (size_t)bu * W;
        for (int x = 0; x < W; x++) cov[x] |= bb[x];
        int c = 0;
        for (int x = 0; x < W; x++) c += pc64(cov[x]);
        if (c >= w) break;
    }
    for (int i = 0; i < nc; i++) {
        int u = chosen[i];
        if (deg[u] >= d) {
            int x = adj[u][rndi(deg[u])];
            remove_edge(u, x);
        }
        add_edge(u, w);
    }
}

static void save_snapshot(void) {
    snapN = n;
    snapM = 0;
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] > u) {
                SU[snapM] = u;
                SV[snapM] = adj[u][k];
                snapM++;
            }
}

static void restore_snapshot(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    n = snapN;
    for (int i = 0; i < snapM; i++) add_edge(SU[i], SV[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    clock_t t0 = clock();

    int nin = 0, min = 0;
    if (scanf("%d %d", &nin, &min) != 2 || d < 1 || d > MAXD || D < 2 ||
        nin < 1 || nin > MAXN - 2 || min < 0 || min > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < min; i++) {
        if (scanf("%d %d", &EU[i], &EV[i]) != 2) { printf("0 0\n"); return 0; }
    }
    n = nin;
    int ok = 1;
    for (int i = 0; i < min && ok; i++) {
        int u = EU[i], v = EV[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) ok = 0;
        else if (has_edge(u, v) || deg[u] >= d || deg[v] >= d) ok = 0;
        else add_edge(u, v);
    }
    for (int i = 0; i < n; i++) col[i] = -1;
    static int stk[MAXN];
    for (int s = 0; s < n && ok; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] == -1) { col[v] = 1 - col[u]; stk[sp++] = v; }
            }
        }
    }
    for (int u = 0; u < n && ok; u++)
        for (int k = 0; k < deg[u]; k++)
            if (col[adj[u][k]] == col[u]) ok = 0;
    if (!ok) { printf("0 0\n"); return 0; }

    long cost = eval_cost();
    if (cost == 0) save_snapshot();
    double T = 0.25 + 0.5 * rndu();
    long stall = 0, iters = 0;

    while (1) {
        if ((iters & 127) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        iters++;

        if (cost == 0) {
            save_snapshot();
            if (n >= MAXN - 1) break;
            grow();
            stall = 0;
            cost = eval_cost();
            continue;
        }

        if (++stall > STALL) {
            stall = 0;
            T = 0.25 + 0.5 * rndu();
            if (snapN > 0) {
                restore_snapshot();
                cost = eval_cost();
            }
            continue;
        }

        int mv = rndi(100);
        if (mv < 40) {
            /* add an edge between opposite sides with spare capacity */
            int u = rndi(n), v = rndi(n);
            if (u == v || col[u] == col[v] || deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            long c2 = eval_cost();
            if (accept(cost, c2, T)) cost = c2;
            else remove_edge(u, v);
        } else if (mv < 60) {
            /* remove a random edge */
            int u = rndi(n);
            if (deg[u] == 0) continue;
            int v = adj[u][rndi(deg[u])];
            remove_edge(u, v);
            long c2 = eval_cost();
            if (accept(cost, c2, T)) cost = c2;
            else add_edge(u, v);
        } else {
            /* degree-preserving double swap: (u,v),(x,y) -> (u,y),(x,v), u and x on side 0 */
            int u = rndi(n);
            if (deg[u] == 0) continue;
            int v = adj[u][rndi(deg[u])];
            int x = rndi(n);
            if (deg[x] == 0) continue;
            int y = adj[x][rndi(deg[x])];
            if (col[u] != 0) { int t = u; u = v; v = t; }
            if (col[x] != 0) { int t = x; x = y; y = t; }
            if (col[u] != 0 || col[x] != 0) continue;
            if (u == x || v == y || has_edge(u, y) || has_edge(x, v)) continue;
            remove_edge(u, v);
            remove_edge(x, y);
            add_edge(u, y);
            add_edge(x, v);
            long c2 = eval_cost();
            if (accept(cost, c2, T)) {
                cost = c2;
            } else {
                remove_edge(u, y);
                remove_edge(x, v);
                add_edge(u, v);
                add_edge(x, y);
            }
        }
    }

    if (snapN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", SU[i], SV[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q); each old vertex has spare capacity s = d - q - 1.
# Add an A-vertex per point of an arc S (joined to the q+1 lines through it)
# and a B-vertex per line index in S (joined to the q+1 points on it).
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


# ----------------------------------------------------------------------------
# Build: start from the best algebraic graph, then let the C engine grow it.
# The C engine is a general bipartite local search (no voltage restriction):
# it inserts a vertex whose neighbourhood covers all old vertices within D-1,
# then repairs the graph with simulated annealing over edge additions,
# removals and degree-preserving double swaps, minimizing the number of pairs
# at distance > D. It keeps the largest valid graph it has seen.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bound = lib.moore_bound(d, D)
    if best[0] >= bound:
        return best

    # Arc-extended projective plane graphs (diameter 3).
    if D == 3:
        arcs = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(arcs, key=lambda t: -t[0])[:3]:
            consider(n_c, e_c)

    if best[0] >= bound:
        return best

    # General bipartite local search in C, started from the best graph so far.
    elapsed = time.monotonic() - start
    budget = 0.80 * time_limit - elapsed - 1.0
    if budget >= 1.0 and d <= 64:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=best,
                            timeout=time_limit * 0.92 - elapsed)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
