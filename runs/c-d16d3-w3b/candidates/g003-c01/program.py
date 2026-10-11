import random
import time

import lib


# ----------------------------------------------------------------------------
# Python side: arc-extended projective plane graphs (diameter 3, valid by design).
#
# PG(2, q) incidence graph: points 0..m-1, lines m..2m-1, each vertex degree q+1.
# A-vertex per point P in SA, joined to the q+1 lines through P.
# B-vertex per line j in SB, joined to the q+1 points on j.
# Each line carries <= s = d-q-1 A-vertices, each point <= s B-vertices, so
# degrees stay <= d. Sides: points and B-vertices vs lines and A-vertices.
# Diameter 3 holds for any SA, SB obeying the caps (lines meet, so every pair of
# vertices is within distance 3). Conic arcs give |SA| = |SB| = q+1 for s >= 2.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1200
#define MAXDEG 40
#define MAXW 19

static int D_ = 3, DEG_ = 3;
static int hw = 0, nalive = 0;
static int alive[MAXN], side[MAXN], deg[MAXN], adj[MAXN][MAXDEG];
static int badv[MAXN], totbad = 0;
static uint64_t bsA[MAXN][MAXW], bsB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int eu[MAXN * MAXDEG], ev[MAXN * MAXDEG];

typedef struct {
    int hw, nalive;
    int alive[MAXN], side[MAXN], deg[MAXN];
    int adj[MAXN][MAXDEG];
} Snap;
static Snap S_cur, S_best;

static double now_sec(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

static uint64_t xr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) {
    if (k <= 1) return 0;
    return (int)(xr() % (uint64_t)k);
}

static int pc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static void save(Snap *s) {
    s->hw = hw;
    s->nalive = nalive;
    memcpy(s->alive, alive, sizeof(int) * hw);
    memcpy(s->side, side, sizeof(int) * hw);
    memcpy(s->deg, deg, sizeof(int) * hw);
    memcpy(s->adj, adj, sizeof(int) * hw * MAXDEG);
}

static void load(const Snap *s) {
    hw = s->hw;
    nalive = s->nalive;
    memcpy(alive, s->alive, sizeof(int) * hw);
    memcpy(side, s->side, sizeof(int) * hw);
    memcpy(deg, s->deg, sizeof(int) * hw);
    memcpy(adj, s->adj, sizeof(int) * hw * MAXDEG);
}

/* Bad pairs = unordered alive pairs at distance > D_. Sets badv[] and totbad. */
static int compute_bad(void) {
    int W = (hw + 63) >> 6;
    for (int v = 0; v < hw; v++) {
        if (!alive[v]) continue;
        memset(bsA[v], 0, sizeof(uint64_t) * W);
        bsA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < hw; v++) {
            if (!alive[v]) continue;
            memcpy(bsB[v], bsA[v], sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                uint64_t *src = bsA[adj[v][k]];
                for (int w = 0; w < W; w++) bsB[v][w] |= src[w];
            }
        }
        for (int v = 0; v < hw; v++)
            if (alive[v]) memcpy(bsA[v], bsB[v], sizeof(uint64_t) * W);
    }
    int tot = 0;
    for (int v = 0; v < hw; v++) {
        if (!alive[v]) { badv[v] = 0; continue; }
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(bsA[v][w]);
        badv[v] = nalive - c;
        tot += badv[v];
    }
    totbad = tot / 2;
    return totbad;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
}

static void kill(int v) {
    for (int k = 0; k < deg[v]; k++) del_arc(adj[v][k], v);
    deg[v] = 0;
    alive[v] = 0;
    nalive--;
}

/* Add a new vertex on side s joined to up to DEG_ random free vertices of the other side. */
static int add_vertex(int s) {
    int cand[MAXN], nc = 0;
    for (int i = 0; i < hw; i++)
        if (alive[i] && side[i] != s && deg[i] < DEG_) cand[nc++] = i;
    if (nc == 0) return -1;
    int v = -1;
    int off = rnd(hw);
    for (int t = 0; t < hw; t++) {
        int i = (off + t) % hw;
        if (!alive[i]) { v = i; break; }
    }
    if (v < 0) {
        if (hw >= MAXN) return -1;
        v = hw++;
    }
    for (int i = nc - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
    alive[v] = 1;
    side[v] = s;
    deg[v] = 0;
    nalive++;
    int k = nc < DEG_ ? nc : DEG_;
    for (int j = 0; j < k; j++) add_edge(v, cand[j]);
    return v;
}

/* Repair: repeatedly delete the alive vertex involved in the most bad pairs. */
static int repair(int maxrem) {
    int rem = 0;
    while (compute_bad() > 0) {
        if (rem >= maxrem) return 0;
        int best = -1, bv = 0, ties = 0;
        for (int v = 0; v < hw; v++) {
            if (!alive[v] || badv[v] <= 0) continue;
            if (badv[v] > bv) {
                bv = badv[v];
                best = v;
                ties = 1;
            } else if (badv[v] == bv) {
                ties++;
                if (rnd(ties) == 0) best = v;
            }
        }
        if (best < 0) return 0;
        kill(best);
        rem++;
    }
    return 1;
}

/* Adding edges between opposite sides never increases distances, so validity is kept. */
static void fill_edges(void) {
    int order[MAXN], no = 0;
    for (int i = 0; i < hw; i++)
        if (alive[i]) order[no++] = i;
    for (int i = no - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int tmp = order[i];
        order[i] = order[j];
        order[j] = tmp;
    }
    for (int x = 0; x < no; x++) {
        int a = order[x];
        for (int y = 0; y < no; y++) {
            int b = order[y];
            if (deg[a] >= DEG_) break;
            if (side[a] == side[b] || deg[b] >= DEG_) continue;
            if (has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 2654435761ULL + 1;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    DEG_ = d;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) {
        printf("0 0\n");
        return 0;
    }
    if (m < 0) m = 0;
    if (m > MAXN * MAXDEG) m = MAXN * MAXDEG;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m = i; break; }
    }

    hw = n;
    nalive = n;
    for (int i = 0; i < n; i++) {
        alive[i] = 1;
        deg[i] = 0;
        side[i] = -1;
    }
    for (int i = 0; i < m; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) continue;
        if (deg[a] < DEG_ && deg[b] < DEG_ && !has_edge(a, b)) add_edge(a, b);
    }

    /* 2-colour by BFS. */
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    queue[qt++] = w;
                }
            }
        }
    }

    if (repair(1000000) == 0) {
        printf("0 0\n");
        return 0;
    }
    save(&S_cur);
    save(&S_best);
    int cur_n = nalive, best_n = nalive;

    double t0 = now_sec();
    while (now_sec() - t0 < tl) {
        int nadd = 1 + rnd(3);
        for (int a = 0; a < nadd; a++) add_vertex(rnd(2));
        if (rnd(3) == 0) {
            int r = 1 + rnd(2);
            for (int a = 0; a < r; a++) {
                int v = rnd(hw);
                if (alive[v]) kill(v);
            }
        }
        int ok = repair(40 + 20 * nadd);
        if (ok) {
            int nn = nalive;
            if (nn >= cur_n || (nn == cur_n - 1 && rnd(4) == 0)) {
                save(&S_cur);
                cur_n = nn;
                if (nn > best_n) {
                    best_n = nn;
                    save(&S_best);
                }
            } else {
                load(&S_cur);
            }
        } else {
            load(&S_cur);
        }
    }

    load(&S_best);
    fill_edges();
    if (compute_bad() != 0) {
        printf("0 0\n");
        return 0;
    }
    static int idx[MAXN];
    int k = 0;
    for (int i = 0; i < hw; i++) idx[i] = alive[i] ? k++ : -1;
    int m2 = 0;
    for (int i = 0; i < hw; i++) {
        if (!alive[i]) continue;
        for (int t = 0; t < deg[i]; t++) if (adj[i][t] > i) m2++;
    }
    printf("%d %d\n", k, m2);
    for (int i = 0; i < hw; i++) {
        if (!alive[i]) continue;
        for (int t = 0; t < deg[i]; t++)
            if (adj[i][t] > i) printf("%d %d\n", idx[i], idx[adj[i][t]]);
    }
    return 0;
}
"""


def _pg(q):
    """Return (m, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, point_lines, line_points, index, pts


def _conic(q, index, F):
    """Conic (plus nucleus for even q): an arc with at most 2 points per line."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _extend(m, caps, nbr, seed, rng, tries):
    """Randomized greedy extension of a valid seed set under per-target caps."""
    best = list(seed)
    order = list(range(m))
    for _ in range(tries):
        rng.shuffle(order)
        load = [0] * m
        inS = [False] * m
        S = []
        for x in seed:
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
        for x in order:
            if not inS[x] and all(load[t] < caps[t] for t in nbr[x]):
                inS[x] = True
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _arc_graph(m, point_lines, line_points, SA, SB):
    """Incidence graph plus one A-vertex per SA point and one B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = []
    for P in range(m):
        for L in point_lines[P]:
            E.append((P, m + L))
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    q = max((x for x in range(2, d) if lib.is_prime_power(x)), default=None)
    if q is None:
        return best
    s = d - q - 1
    # d - 1 a prime power: the projective plane incidence graph is already optimal.
    if s == 0 and lib.is_prime_power(d - 1):
        n0, E0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, E0, d, D):
            return n0, E0

    m, point_lines, line_points, index, pts = _pg(q)
    F = lib.GF(q)
    SA, SB = [], []
    if s >= 1:
        conic = _conic(q, index, F) if s >= 2 else []
        SA = _extend(m, [s] * m, point_lines, conic, rng, 6)
        SB = _extend(m, [s] * m, line_points, conic, rng, 6)

    n, E = _arc_graph(m, point_lines, line_points, SA, SB)
    if lib.is_valid(n, E, d, D) and n > best[0]:
        best = (n, E)

    # C engine: vertex insertion + bad-pair repair, starting from the arc graph.
    elapsed = time.monotonic() - t0
    budget = max(1.0, 0.6 * time_limit - elapsed)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=best, timeout=0.85 * time_limit)
        n2, e2 = lib.parse_graph_text(out)
        if n2 >= best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
