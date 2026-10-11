import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy for D >= 3:
#   1. Start from the best algebraic candidate: PG(2,q) incidence, or arc-extended
#      PG(2,q) graphs (conic A/B sets, valid for diameter 3), or K_{d,d}.
#   2. If the Moore bound is not reached, hand the graph to a C engine. It grows the
#      bipartite graph one vertex at a time. New vertices get edges by stealing
#      slots from full vertices. Simulated annealing over degree-preserving moves
#      (edge swaps and endpoint relocations) then repairs the bad pairs. Every
#      accepted state is checked (zero bad pairs) and snapshotted, so the output is
#      always a valid graph no smaller than the start.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 640
#define MAXD 32
#define WMAX 10

static int N, DEG, DIAM;
static int side[MAXN], deg[MAXN], nb[MAXN][MAXD];
static unsigned char am[MAXN][MAXN];
static uint64_t RA[MAXN][WMAX], RB[MAXN][WMAX];
static int snapN, snapE;
static int snap_u[MAXN * MAXD], snap_v[MAXN * MAXD];
static int mr_n, ma_n;
static int mru[4], mrv[4], mau[4], mav[4];
static uint64_t rs = 88172645463325252ULL;
static struct timespec TSTART;
static double LIMIT = 10.0;

static uint64_t rnext(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd(int k) { return (int)(rnext() % (uint64_t)k); }
static double urand(void) { return (rnext() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double wall(void) {
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return (double)(t.tv_sec - TSTART.tv_sec) + 1e-9 * (double)(t.tv_nsec - TSTART.tv_nsec);
}

static void rm_nb(int u, int v) {
    int k;
    for (k = 0; k < deg[u]; k++)
        if (nb[u][k] == v) { nb[u][k] = nb[u][--deg[u]]; return; }
}
static void add_edge(int u, int v) {
    am[u][v] = am[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}
static void del_edge(int u, int v) {
    am[u][v] = am[v][u] = 0;
    rm_nb(u, v);
    rm_nb(v, u);
}

/* Number of unordered vertex pairs at distance > DIAM (0 means valid). */
static long eval_cost(void) {
    int W = (N + 63) / 64, r, v, w, k;
    uint64_t (*cur)[WMAX] = RA, (*nxt)[WMAX] = RB, (*tmp)[WMAX];
    for (v = 0; v < N; v++) {
        for (w = 0; w < WMAX; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            for (w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    long tot = 0;
    for (v = 0; v < N; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc(cur[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

/* Random vertex on side s; spare=1 needs deg < DEG, spare=0 needs deg > 0. */
static int pick_side_vertex(int s, int spare) {
    int t;
    for (t = 0; t < 200; t++) {
        int v = rnd(N);
        if (side[v] != s) continue;
        if (spare) { if (deg[v] < DEG) return v; }
        else if (deg[v] > 0) return v;
    }
    return -1;
}

/* Propose a degree-preserving or relocation move; records it without applying. */
static int make_move(void) {
    int type = rnd(4), a1, a2, b1, b2;
    mr_n = 0; ma_n = 0;
    if (type < 2) {
        a1 = pick_side_vertex(0, 0);
        a2 = pick_side_vertex(0, 0);
        if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
        b1 = nb[a1][rnd(deg[a1])];
        b2 = nb[a2][rnd(deg[a2])];
        if (b1 == b2 || am[a1][b2] || am[a2][b1]) return 0;
        mru[0] = a1; mrv[0] = b1; mru[1] = a2; mrv[1] = b2; mr_n = 2;
        mau[0] = a1; mav[0] = b2; mau[1] = a2; mav[1] = b1; ma_n = 2;
        return 1;
    }
    a1 = pick_side_vertex(0, 0);
    if (a1 < 0) return 0;
    b1 = nb[a1][rnd(deg[a1])];
    if (type == 2) {
        a2 = pick_side_vertex(0, 1);
        if (a2 < 0 || a2 == a1 || am[a2][b1]) return 0;
        mru[0] = a1; mrv[0] = b1; mr_n = 1;
        mau[0] = a2; mav[0] = b1; ma_n = 1;
    } else {
        b2 = pick_side_vertex(1, 1);
        if (b2 < 0 || b2 == b1 || am[a1][b2]) return 0;
        mru[0] = a1; mrv[0] = b1; mr_n = 1;
        mau[0] = a1; mav[0] = b2; ma_n = 1;
    }
    return 1;
}

static void apply_move(void) {
    int i;
    for (i = 0; i < mr_n; i++) del_edge(mru[i], mrv[i]);
    for (i = 0; i < ma_n; i++) add_edge(mau[i], mav[i]);
}

static void undo_move(void) {
    int i;
    for (i = 0; i < ma_n; i++) del_edge(mau[i], mav[i]);
    for (i = 0; i < mr_n; i++) add_edge(mru[i], mrv[i]);
}

/* Adding edges never increases distances, so add every missing spare-spare edge. */
static void greedy_fill(void) {
    static int spA[MAXN], spB[MAXN];
    int na = 0, nbb = 0, i, j, v;
    for (v = 0; v < N; v++) {
        if (deg[v] < DEG) {
            if (side[v] == 0) spA[na++] = v;
            else spB[nbb++] = v;
        }
    }
    for (i = 0; i < na; i++) {
        int a = spA[i];
        for (j = 0; j < nbb; j++) {
            int b = spB[j];
            if (deg[a] >= DEG) break;
            if (deg[b] < DEG && !am[a][b]) add_edge(a, b);
        }
    }
}

static long sa_run(long iters, double Tstart, double Tend) {
    long cost = eval_cost();
    long it;
    for (it = 0; it < iters && cost > 0; it++) {
        double T;
        if ((it & 127) == 0 && wall() > LIMIT) break;
        T = Tstart * pow(Tend / Tstart, (double)it / (double)iters);
        if (!make_move()) continue;
        apply_move();
        {
            long c2 = eval_cost();
            long delta = c2 - cost;
            if (delta <= 0 || urand() < exp(-(double)delta / T)) {
                greedy_fill();
                cost = eval_cost();
            } else {
                undo_move();
            }
        }
    }
    return cost;
}

static void save_snapshot(void) {
    int u, k;
    snapN = N; snapE = 0;
    for (u = 0; u < N; u++)
        for (k = 0; k < deg[u]; k++) {
            int v = nb[u][k];
            if (u < v) { snap_u[snapE] = u; snap_v[snapE] = v; snapE++; }
        }
}

static void load_snapshot(void) {
    int u, e;
    for (u = 0; u < N; u++) {
        deg[u] = 0;
        memset(am[u], 0, (size_t)N);
    }
    N = snapN;
    for (e = 0; e < snapE; e++) add_edge(snap_u[e], snap_v[e]);
}

static int new_vertex(int s) {
    int x = N, u;
    for (u = 0; u < N; u++) { am[u][x] = 0; am[x][u] = 0; }
    am[x][x] = 0;
    side[x] = s;
    deg[x] = 0;
    N++;
    return x;
}

/* Give vertex x DEG neighbours on the other side; steal slots from full vertices if needed. */
static void fill_vertex(int x) {
    int s = side[x];
    while (deg[x] < DEG) {
        int cand[MAXN], nc = 0, y;
        for (y = 0; y < N; y++)
            if (side[y] != s && deg[y] < DEG && !am[x][y]) cand[nc++] = y;
        if (nc > 0) {
            add_edge(x, cand[rnd(nc)]);
            continue;
        }
        nc = 0;
        for (y = 0; y < N; y++)
            if (side[y] != s && deg[y] == DEG && !am[x][y]) cand[nc++] = y;
        if (nc == 0) return;
        y = cand[rnd(nc)];
        {
            int z = nb[y][rnd(deg[y])];
            del_edge(y, z);
            add_edge(x, y);
        }
    }
}

static int bipartite_color(void) {
    static int st[MAXN];
    int v, sp, u, k;
    for (v = 0; v < N; v++) side[v] = -1;
    for (v = 0; v < N; v++) {
        if (side[v] >= 0) continue;
        side[v] = 0;
        sp = 0;
        st[sp++] = v;
        while (sp > 0) {
            u = st[--sp];
            for (k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (side[w] < 0) { side[w] = 1 - side[u]; st[sp++] = w; }
                else if (side[w] == side[u]) return 0;
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    int n0, m0, i, j;
    int *eu, *ev;
    if (argc < 5) return 1;
    timespec_get(&TSTART, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    LIMIT = atof(argv[4]);
    if (DEG < 2 || DEG > MAXD || DIAM < 2 || DIAM > 30) { printf("0 0\n"); return 0; }

    n0 = 0; m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0 || n0 > MAXN - 200 || m0 > MAXN * MAXD / 2) { printf("0 0\n"); return 0; }
    eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!eu || !ev) { printf("0 0\n"); return 0; }
    for (i = 0; i < m0; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }

    if (n0 == 0) {
        N = 2 * DEG;
        for (i = 0; i < N; i++) side[i] = (i >= DEG);
        for (i = 0; i < DEG; i++)
            for (j = DEG; j < N; j++) add_edge(i, j);
    } else {
        N = n0;
        for (i = 0; i < m0; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || v < 0 || u >= N || v >= N || u == v || am[u][v] ||
                deg[u] >= DEG || deg[v] >= DEG) {
                printf("0 0\n");
                return 0;
            }
            add_edge(u, v);
        }
        if (!bipartite_color()) { printf("0 0\n"); return 0; }
    }

    {
        long c = eval_cost();
        if (c > 0) c = sa_run(300000, 1.0, 0.05);
        if (c > 0) { printf("0 0\n"); return 0; }
    }
    save_snapshot();

    {
        int fails = 0;
        while (wall() < LIMIT && N < MAXN - 1) {
            int c0 = 0, c1 = 0, v, s, x;
            long cost;
            for (v = 0; v < N; v++) { if (side[v]) c1++; else c0++; }
            s = (c0 < c1) ? 0 : (c1 < c0 ? 1 : rnd(2));
            x = new_vertex(s);
            fill_vertex(x);
            greedy_fill();
            cost = eval_cost();
            if (cost > 0) {
                long iters = 4000L * (1 + (fails < 10 ? fails : 10));
                cost = sa_run(iters, 2.0, 0.05);
            }
            if (cost == 0) { save_snapshot(); fails = 0; }
            else { load_snapshot(); fails++; }
        }
    }

    printf("%d %d\n", snapN, snapE);
    for (i = 0; i < snapE; i++) printf("%d %d\n", snap_u[i], snap_v[i]);
    free(eu);
    free(ev);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Algebraic candidates.
# ----------------------------------------------------------------------------

def _pg(q):
    """Points, m, incidence edges, point->lines and line->points lists for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return pts, m, edges, point_lines, line_points


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: pick elements so every target is hit at most s times."""
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
    """Conic plus nucleus (q even): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """PG incidence plus one vertex per SA point (joined to its lines) and per SB line (joined to its points)."""
    na, nb = len(SA), len(SB)
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + na + nb, E


def _arc_candidates(d, rng, deadline):
    """Diameter-3 candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        if time.monotonic() > deadline:
            break
        pts, m, edges, point_lines, line_points = _pg(q)
        index = {p: i for i, p in enumerate(pts)}
        SA = _greedy_side(m, s, point_lines, rng, 30, deadline)
        SB = _greedy_side(m, s, line_points, rng, 30, deadline)
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle of length 2D: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        cands = []
        if lib.is_prime_power(d - 1):
            cands.append(lib.projective_plane_incidence(d - 1))
        cands += _arc_candidates(d, rng, t0 + 0.1 * time_limit)
        for n, e in cands:
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e

    # Grow and repair with the C engine unless the Moore bound is already reached.
    if D >= 3 and best_n < lib.moore_bound(d, D):
        elapsed = time.monotonic() - t0
        budget = max(0.5, 0.85 * time_limit - elapsed - 1.5)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=(best_n, best_e), timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
