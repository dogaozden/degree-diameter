import time

import lib


# ----------------------------------------------------------------------------
# C engine: repair-annealing vertex insertion.
#
# The graph is kept bipartite (side 0 / side 1). Each new vertex is joined to
# spare-degree vertices of the opposite side, then simulated annealing rewires
# the graph to remove every pair at distance > D. Moves are degree-preserving
# double swaps and additions of cross edges between spare vertices. Whenever
# the cost (number of ordered bad pairs) reaches zero, the graph is saved and
# one more vertex is added. Stagnation restores the best saved graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 40
#define MAXE 40000

static int N, DMAX, DIAM;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int side[MAXN];
static int qbuf[MAXN];
static int dist_[MAXN];
static int seenst[MAXN];
static int stampv = 0;
static int bestN = 0, bestM = 0;
static int bestA[MAXE], bestB[MAXE];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void add_e(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static void del_one(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; break; }
    for (int i = 0; i < deg[b]; i++) if (adj[b][i] == a) { adj[b][i] = adj[b][--deg[b]]; break; }
}

/* Number of ordered pairs (s,t) with distance > DIAM. Zero means valid. */
static long bad_pairs(void) {
    long bad = 0;
    for (int s = 0; s < N; s++) {
        stampv++;
        int h = 0, t = 0;
        qbuf[t++] = s;
        seenst[s] = stampv;
        dist_[s] = 0;
        while (h < t) {
            int u = qbuf[h++];
            if (dist_[u] >= DIAM) continue;
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (seenst[v] != stampv) {
                    seenst[v] = stampv;
                    dist_[v] = dist_[u] + 1;
                    qbuf[t++] = v;
                }
            }
        }
        bad += (long)(N - t);
    }
    return bad;
}

static void save_best(void) {
    if (N <= bestN) return;
    int m = 0;
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (v > u) {
                if (m >= MAXE) return;
                bestA[m] = u;
                bestB[m] = v;
                m++;
            }
        }
    }
    bestN = N;
    bestM = m;
}

static void load_best(void) {
    for (int u = 0; u < N; u++) deg[u] = 0;
    N = bestN;
    for (int i = 0; i < bestM; i++) add_e(bestA[i], bestB[i]);
}

static void add_vertex(void) {
    if (N >= MAXN) return;
    int s = rndi(2);
    int v = N++;
    side[v] = s;
    deg[v] = 0;
    int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < v; u++) if (side[u] != s && deg[u] < DMAX) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int tmp = cand[i]; cand[i] = cand[j]; cand[j] = tmp;
    }
    for (int i = 0; i < nc && deg[v] < DMAX; i++) add_e(v, cand[i]);
}

static int pick_side_edge(int s) {
    for (int t = 0; t < 30; t++) {
        int u = rndi(N);
        if (side[u] == s && deg[u] > 0) return u;
    }
    return -1;
}

static int pick_side_spare(int s) {
    for (int t = 0; t < 30; t++) {
        int u = rndi(N);
        if (side[u] == s && deg[u] < DMAX) return u;
    }
    return -1;
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    DMAX = d;
    if (d < 1 || d >= MAXD || DIAM < 1) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double deadline = now_s() + budget;

    static int ea[MAXE], eb[MAXE];
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n == 0) {
        n = 2; m = 1; ea[0] = 0; eb[0] = 1;
    } else {
        if (n < 2 || n > MAXN || m < 0 || m > MAXE) { printf("0 0\n"); return 0; }
        for (int i = 0; i < m; i++)
            if (scanf("%d %d", &ea[i], &eb[i]) != 2) { printf("0 0\n"); return 0; }
    }

    N = n;
    for (int u = 0; u < N; u++) deg[u] = 0;
    for (int i = 0; i < m; i++) {
        int a = ea[i], b = eb[i];
        if (a < 0 || a >= N || b < 0 || b >= N || a == b || deg[a] >= DMAX || deg[b] >= DMAX || has_edge(a, b)) {
            printf("0 0\n");
            return 0;
        }
        add_e(a, b);
    }

    for (int u = 0; u < N; u++) side[u] = -1;
    for (int s0 = 0; s0 < N; s0++) {
        if (side[s0] >= 0) continue;
        side[s0] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s0;
        while (h < t) {
            int u = qbuf[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (side[v] < 0) { side[v] = 1 - side[u]; qbuf[t++] = v; }
            }
        }
    }
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (side[adj[u][i]] == side[u]) { printf("0 0\n"); return 0; }

    long cur = bad_pairs();
    if (cur == 0) save_best();
    long minc = cur;
    long stagn = 0;
    double T = 1.0;
    const long STAG = 4000;

    while (now_s() < deadline) {
        if (cur == 0) {
            save_best();
            if (N >= MAXN) break;
            add_vertex();
            cur = bad_pairs();
            minc = cur;
            stagn = 0;
            T = 1.0;
            continue;
        }
        if (bestN > 0 && stagn > STAG) {
            load_best();
            cur = bad_pairs();
            minc = cur;
            stagn = 0;
            T = 1.0;
            continue;
        }

        int mv = rndi(10);
        if (mv < 8) {
            int a = pick_side_edge(0);
            int c = pick_side_edge(0);
            if (a < 0 || c < 0) continue;
            int b = adj[a][rndi(deg[a])];
            int e = adj[c][rndi(deg[c])];
            if (a == c || b == e || has_edge(a, e) || has_edge(c, b)) continue;
            del_one(a, b);
            del_one(c, e);
            add_e(a, e);
            add_e(c, b);
            long nc = bad_pairs();
            if (accept(nc - cur, T)) {
                cur = nc;
            } else {
                del_one(a, e);
                del_one(c, b);
                add_e(a, b);
                add_e(c, e);
            }
        } else {
            int a = pick_side_spare(0);
            int b = pick_side_spare(1);
            if (a < 0 || b < 0 || has_edge(a, b)) continue;
            add_e(a, b);
            long nc = bad_pairs();
            if (accept(nc - cur, T)) {
                cur = nc;
            } else {
                del_one(a, b);
            }
        }

        if (cur < minc) { minc = cur; stagn = 0; }
        else stagn++;
        T *= 0.9995;
        if (T < 0.1) T = 0.1;
    }

    if (cur == 0) save_best();
    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestA[i], bestB[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python construction: arc-extended projective plane graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each vertex has degree q+1, so
# with d >= q+1 it has spare s = d-q-1. Choose a point set S (conic, plus the
# nucleus for even q) whose line and point loads are at most s. Add an A-vertex
# on each point of S joined to the q+1 lines through it, and a B-vertex on each
# line of S joined to its q+1 points. The diameter stays 3.
# ----------------------------------------------------------------------------

def _arc_ext(q, d):
    """Arc-extended PG(2, q) for degree d, or None if the loads do not fit."""
    s = d - q - 1
    if s < 1 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    if max(cl) > s or max(cp) > s:
        return None
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Diameter-3 starts: PG(2,q) incidence and arc-extended versions.
    if D >= 3:
        for q in range(min(d - 1, 16), 1, -1):
            if not lib.is_prime_power(q):
                continue
            try:
                n2, e2 = lib.projective_plane_incidence(q)
                if q + 1 <= d:
                    consider(n2, e2)
                ext = _arc_ext(q, d)
                if ext is not None:
                    consider(*ext)
            except Exception:
                pass

    # Already at the Moore bound: nothing to gain.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Search: grow the best start with the C repair-annealer.
    remaining = time_limit - (time.monotonic() - start)
    if remaining > 6:
        budget = max(0.2, 0.7 * remaining - 2.0)
    else:
        budget = 0.4 * remaining
    if budget >= 0.2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=best,
                            timeout=max(1.0, remaining * 0.92))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
