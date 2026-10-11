import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy for d = 16, D = 3 (and any D >= 3):
#   1. Build arc-extended projective plane graphs (verified diameter 3).
#   2. Hand the largest one to a C engine that does a different kind of search
#      than the parent: bitset-based bad-pair annealing with 2-switch, edge
#      add/remove moves on a fixed bipartition, interleaved with vertex growth
#      (a new vertex takes d neighbours on the opposite side, freeing their slots
#      by deleting edges). The cost is the number of vertex pairs farther than D.
#   3. Every output is re-checked with lib.is_valid. K_{d,d} (or the best arc
#      graph) is the fallback, so every case returns a valid graph.
# ----------------------------------------------------------------------------

_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1000
#define MAXW 16
#define MAXD 40
#define MAXE 20000

static int d, Dd, n;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static int color[MAXN];
static uint64_t P1[MAXN][MAXW], P2[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int bestN = 0, bestM = 0;
static int bu[MAXE], bv[MAXE];

typedef struct { int nr, na; int ra[2], rb[2], aa[2], ab[2]; } Move;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    A[a][b] = A[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_one(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; break; }
    }
}

static void del_edge(int a, int b) {
    A[a][b] = A[b][a] = 0;
    del_one(a, b);
    del_one(b, a);
}

/* Number of ordered-pair-halved unordered pairs at distance > Dd (unreachable included). */
static long long bad_pairs(void) {
    int W = (n + 63) / 64;
    uint64_t (*cur)[MAXW] = P1;
    uint64_t (*nxt)[MAXW] = P2;
    int v, w, i, r;
    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
        for (i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            cur[v][u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (r = 2; r <= Dd; r++) {
        for (v = 0; v < n; v++) {
            for (w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += pc64(cur[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void compute_colors(void) {
    int i, s;
    static int q[MAXN];
    for (i = 0; i < n; i++) color[i] = -1;
    for (s = 0; s < n; s++) {
        if (color[s] != -1) continue;
        int h = 0, t = 0;
        color[s] = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (color[v] == -1) {
                    color[v] = 1 - color[u];
                    q[t++] = v;
                }
            }
        }
    }
}

/* Move generator: add an edge between deficient opposite vertices, remove an edge,
   or do a degree-preserving 2-switch that keeps the bipartition. */
static int gen_move(Move *m) {
    int t = rndi(10), v, tries;
    m->nr = 0;
    m->na = 0;
    if (t < 3) {
        static int c0[MAXN], c1[MAXN];
        int k0 = 0, k1 = 0;
        for (v = 0; v < n; v++) {
            if (deg[v] < d) {
                if (color[v] == 0) c0[k0++] = v;
                else c1[k1++] = v;
            }
        }
        if (!k0 || !k1) return 0;
        for (tries = 0; tries < 30; tries++) {
            int a = c0[rndi(k0)], b = c1[rndi(k1)];
            if (!A[a][b]) {
                m->na = 1;
                m->aa[0] = a;
                m->ab[0] = b;
                return 1;
            }
        }
        return 0;
    }
    if (t < 5) {
        int a = -1;
        for (tries = 0; tries < 100 && a < 0; tries++) {
            int x = rndi(n);
            if (deg[x] > 0) a = x;
        }
        if (a < 0) return 0;
        int b = nb[a][rndi(deg[a])];
        m->nr = 1;
        m->ra[0] = a;
        m->rb[0] = b;
        return 1;
    }
    int a = -1, c = -1, b, e;
    for (tries = 0; tries < 100 && a < 0; tries++) {
        int x = rndi(n);
        if (deg[x] > 0) a = x;
    }
    if (a < 0) return 0;
    b = nb[a][rndi(deg[a])];
    for (tries = 0; tries < 100 && c < 0; tries++) {
        int x = rndi(n);
        if (deg[x] > 0 && color[x] == color[a]) c = x;
    }
    if (c < 0) return 0;
    e = nb[c][rndi(deg[c])];
    if (a == c || b == e || A[a][e] || A[c][b]) return 0;
    m->nr = 2;
    m->ra[0] = a; m->rb[0] = b;
    m->ra[1] = c; m->rb[1] = e;
    m->na = 2;
    m->aa[0] = a; m->ab[0] = e;
    m->aa[1] = c; m->ab[1] = b;
    return 1;
}

static void apply_move(const Move *m) {
    int i;
    for (i = 0; i < m->nr; i++) del_edge(m->ra[i], m->rb[i]);
    for (i = 0; i < m->na; i++) add_edge(m->aa[i], m->ab[i]);
}

static void undo_move(const Move *m) {
    int i;
    for (i = 0; i < m->na; i++) del_edge(m->aa[i], m->ab[i]);
    for (i = 0; i < m->nr; i++) add_edge(m->ra[i], m->rb[i]);
}

/* Add a vertex on the smaller colour class, joined to d vertices of the other class.
   Saturated neighbours first lose a random edge so degrees stay <= d. */
static int grow(void) {
    int c0 = 0, c1 = 0, v, c, k = 0, i, j;
    static int opp[MAXN];
    if (n + 1 >= MAXN) return 0;
    for (v = 0; v < n; v++) {
        if (color[v] == 0) c0++;
        else c1++;
    }
    c = (c0 <= c1) ? 0 : 1;
    for (v = 0; v < n; v++) {
        if (color[v] == 1 - c) opp[k++] = v;
    }
    if (k < d) return 0;
    for (i = 0; i < d; i++) {
        j = i + rndi(k - i);
        int tmp = opp[i];
        opp[i] = opp[j];
        opp[j] = tmp;
    }
    int w = n++;
    color[w] = c;
    deg[w] = 0;
    for (i = 0; i < d; i++) {
        int u = opp[i];
        if (deg[u] >= d) {
            int y = nb[u][rndi(deg[u])];
            del_edge(u, y);
        }
        add_edge(u, w);
    }
    return 1;
}

static void snapshot(void) {
    int v, i, cnt = 0;
    if (n < bestN) return;
    for (v = 0; v < n; v++) {
        for (i = 0; i < deg[v]; i++) {
            if (nb[v][i] > v) cnt++;
        }
    }
    if (cnt > MAXE) return;
    int m = 0;
    for (v = 0; v < n; v++) {
        for (i = 0; i < deg[v]; i++) {
            if (nb[v][i] > v) {
                bu[m] = v;
                bv[m] = nb[v][i];
                m++;
            }
        }
    }
    bestN = n;
    bestM = m;
}

int main(int argc, char **argv) {
    int i, m0 = 0, u, v, n0 = 0;
    double tl;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    Dd = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 1;
    tl = atof(argv[4]);
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d < 1 || d > MAXD - 1 || Dd < 1 || n0 > MAXN - 64) {
        printf("0 0\n");
        return 0;
    }
    n = n0 < 2 ? 2 : n0;
    for (i = 0; i < m0; i++) {
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (A[u][v] || deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }
    compute_colors();

    clock_t t0 = clock();
    long long cost = bad_pairs();
    double T0 = 0.8, T = T0;
    long long iter = 0, since = 0;
    if (cost == 0) snapshot();
    Move mv;
    for (;;) {
        if ((iter & 15) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
        }
        iter++;
        if (cost == 0) {
            snapshot();
            if (!grow()) break;
            cost = bad_pairs();
            T = T0;
            since = 0;
            continue;
        }
        if (!gen_move(&mv)) continue;
        apply_move(&mv);
        long long c2 = bad_pairs();
        long long delta = c2 - cost;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            undo_move(&mv);
        }
        T *= 0.9995;
        if (T < 0.1) T = 0.1;
        if (++since > 50000) {
            T = T0;
            since = 0;
        }
    }
    if (cost == 0) snapshot();

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
# Build: algebraic start, then the C bad-pair annealer with vertex growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, list(fb_e))

    def consider(g):
        nonlocal best
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        arcs = _arc_extensions(d, t_start + 0.10 * time_limit,
                               random.Random(seed * 7919 + d))
        for g in arcs:
            consider(g)

    # Different search: C bad-pair annealing with growth, from the best graph so far.
    spent = time.monotonic() - t_start
    avail = time_limit - spent - 6.0
    if avail > 3.0:
        budget = avail - 2.0
        try:
            out = lib.run_c(_C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=avail)
            n2, e2 = lib.parse_graph_text(out)
            consider((n2, e2))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, list(fb_e))
    return best
