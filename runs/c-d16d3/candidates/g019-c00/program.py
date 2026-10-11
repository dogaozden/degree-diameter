import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), as in the parent.
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
    """Old PG incidence plus a new A-vertex per point of S (joined to its lines) and a new B-vertex per S-line (joined to its points)."""
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
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, _pts = _pg_data(q)
        cands = [[]]  # the plain incidence graph is always allowed
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            S = []
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# New search engine (C): incremental vertex-insertion annealing.
#
# Starting from a valid bipartite graph, the engine adds one vertex at a time
# (kept on the smaller side). It then anneals over edge moves that keep the
# bipartition and max degree, minimizing the number of vertex pairs at distance
# greater than D. Distances come from bitset balls of radius D. When the cost
# reaches zero, the current graph is saved and one more vertex is inserted.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXDEG 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE 40000

static int N, DIAM, DMAX;
static int colr[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char M[MAXN][MAXN];
static int listA[MAXN], nA, listB[MAXN], nB;
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static uint64_t (*Rc)[MAXW] = bufA;
static uint64_t (*Rn)[MAXW] = bufB;
static uint64_t rng_s = 1;
static int BN, BM;
static int BU[MAXE], BV[MAXE];

static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}

static int rndint(int k) {
    return (int)(rnd64() % (uint64_t)k);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
    M[a][b] = 1;
    M[b][a] = 1;
}

static void del_from(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][--deg[a]];
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
    M[a][b] = 0;
    M[b][a] = 0;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long bad_pairs(void) {
    int W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) Rc[v][w] = 0;
        Rc[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) Rn[v][w] = Rc[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) Rn[v][w] |= Rc[u][w];
            }
        }
        uint64_t (*t)[MAXW] = Rc;
        Rc = Rn;
        Rn = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(Rc[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void snapshot(void) {
    BN = N;
    BM = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (u > v && BM < MAXE) {
                BU[BM] = v;
                BV[BM] = u;
                BM++;
            }
        }
    }
}

static void emit(void) {
    printf("%d %d\n", BN, BM);
    for (int i = 0; i < BM; i++) printf("%d %d\n", BU[i], BV[i]);
}

static void add_vertex(void) {
    int v = N++;
    deg[v] = 0;
    if (nA <= nB) {
        colr[v] = 0;
        listA[nA++] = v;
    } else {
        colr[v] = 1;
        listB[nB++] = v;
    }
}

/* Prefer a vertex of the list with spare degree (a few random tries). */
static int pick(int *list, int n) {
    for (int t = 0; t < 8; t++) {
        int v = list[rndint(n)];
        if (deg[v] < DMAX) return v;
    }
    return list[rndint(n)];
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    if (DMAX > MAXDEG) DMAX = MAXDEG;
    rng_s = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rng_s == 0) rng_s = 1;
    clock_t t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 1 || n0 > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (M[u][v] || deg[u] >= DMAX || deg[v] >= DMAX) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < N; v++) colr[v] = -1;
    int bip = 1;
    static int queue[MAXN];
    for (int s = 0; s < N; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int h = 0, t = 0;
        queue[t++] = s;
        while (h < t) {
            int u = queue[h++];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (colr[w] < 0) {
                    colr[w] = 1 - colr[u];
                    queue[t++] = w;
                } else if (colr[w] == colr[u]) {
                    bip = 0;
                }
            }
        }
    }
    nA = nB = 0;
    for (int v = 0; v < N; v++) {
        if (colr[v] == 0) listA[nA++] = v;
        else listB[nB++] = v;
    }
    snapshot();
    if (!bip || nA == 0 || nB == 0) {
        emit();
        return 0;
    }

    long long cur = bad_pairs();
    long long it = 0, since = 0;
    const double T0 = 1.2;
    while (1) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > limit) break;
        }
        it++;
        if (cur == 0) {
            snapshot();
            if (N + 1 >= MAXN) break;
            add_vertex();
            cur = bad_pairs();
            since = 0;
            continue;
        }
        since++;
        double T = T0 * exp(-(double)(since % 30000) / 6000.0);
        if (T < 0.15) T = 0.15;

        int x = (rnd01() < 0.5) ? pick(listA, nA) : listA[rndint(nA)];
        int y = (rnd01() < 0.5) ? pick(listB, nB) : listB[rndint(nB)];
        if (M[x][y]) continue;

        int xr = -1, yr = -1;
        if (deg[x] >= DMAX) {
            xr = nb[x][rndint(deg[x])];
            remove_edge(x, xr);
        }
        if (deg[y] >= DMAX) {
            yr = nb[y][rndint(deg[y])];
            remove_edge(y, yr);
        }
        add_edge(x, y);

        long long nc = bad_pairs();
        double delta = (double)(nc - cur);
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            cur = nc;
        } else {
            remove_edge(x, y);
            if (yr >= 0) add_edge(y, yr);
            if (xr >= 0) add_edge(x, xr);
        }
    }
    emit();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    # Arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    arc_deadline = t0 + 0.25 * time_limit
    cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
    cands.sort(key=lambda t: -t[0])
    for n_c, e_c in cands:
        if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            best_n = n_c
            break

    # New: C vertex-insertion annealing grows the best start one vertex at a time.
    elapsed = time.monotonic() - t0
    remaining = 0.8 * time_limit - elapsed - 1.0
    if d <= 60 and remaining >= 1.0:
        timeout = max(1.0, 0.92 * time_limit - elapsed)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=timeout)
            n_c, e_c = lib.parse_graph_text(text)
            if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                best_n = n_c
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
