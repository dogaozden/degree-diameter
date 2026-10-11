import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: ruin-and-recreate with ball set-cover insertion.
#
# State: a valid bipartite graph with max degree d and diameter <= D. Slots
# can be dead (removed) and are reused. Inserting a new vertex x on side X
# with neighbour set S (all on the other side, each with spare degree) keeps
# the diameter <= D iff the radius-(D-1) balls of the vertices of S cover all
# alive vertices. Adding a vertex never lengthens an existing distance, so
# only x needs checking. Insertion is a randomized greedy set cover.
#
# Removal can break distances, so after each ruin-and-recreate step the whole
# graph is re-checked, and the step is reverted if it is invalid or smaller.
# Equal-size moves are accepted (plateau walk), and rarely a smaller state.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1700
#define DMAX 64
#define WMAX 27

typedef uint64_t u64;

typedef struct {
    int nslots;
    int alive_cnt;
    int side[NMAX];
    int alive[NMAX];
    int deg[NMAX];
    int adj[NMAX][DMAX];
} State;

static int dd, DD;
static int nslots, alive_cnt, W;
static int side_[NMAX], alive_[NMAX], deg_[NMAX];
static int adj_[NMAX][DMAX];
static u64 aliveb[WMAX];
static u64 ball_[NMAX][WMAX];
static u64 chk_[NMAX][WMAX];
static u64 tmpA[NMAX][WMAX], tmpB[NMAX][WMAX];
static char chosen_[NMAX];
static u64 rs = 88172645463325252ULL;
static State snap_, best_;

static u64 rnd64(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndi(int k) { return (int)(rnd64() % (u64)k); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void recompute_aliveb(void) {
    W = (nslots + 63) >> 6;
    memset(aliveb, 0, sizeof aliveb);
    for (int v = 0; v < nslots; v++)
        if (alive_[v]) aliveb[v >> 6] |= 1ULL << (v & 63);
}

/* out[v] = bitset of alive vertices within distance R of v. */
static void compute_balls(int R, u64 out[][WMAX]) {
    u64 (*cu)[WMAX] = tmpA;
    u64 (*nx)[WMAX] = tmpB;
    W = (nslots + 63) >> 6;
    for (int v = 0; v < nslots; v++) {
        for (int w = 0; w < W; w++) cu[v][w] = 0;
        if (alive_[v]) cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < R; k++) {
        for (int v = 0; v < nslots; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cu[v][w];
            if (!alive_[v]) continue;
            for (int i = 0; i < deg_[v]; i++) {
                const u64 *src = cu[adj_[v][i]];
                for (int w = 0; w < W; w++) nx[v][w] |= src[w];
            }
        }
        u64 (*t)[WMAX] = cu; cu = nx; nx = t;
    }
    for (int v = 0; v < nslots; v++)
        for (int w = 0; w < W; w++) out[v][w] = cu[v][w];
}

static int check_valid(void) {
    compute_balls(DD, chk_);
    for (int v = 0; v < nslots; v++) {
        if (!alive_[v]) continue;
        for (int w = 0; w < W; w++)
            if ((chk_[v][w] & aliveb[w]) != aliveb[w]) return 0;
    }
    return 1;
}

/* Try to insert one new vertex with a greedy randomized ball cover. */
static int try_insert(void) {
    int X = rndi(2);
    int S[DMAX];
    int ns = 0;
    u64 U[WMAX];
    int ok = 0;
    for (int w = 0; w < W; w++) U[w] = 0;
    while (ns < dd) {
        int best = -1;
        long bsc = -1;
        for (int u = 0; u < nslots; u++) {
            if (!alive_[u] || side_[u] == X || deg_[u] >= dd || chosen_[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(ball_[u][w] & ~U[w] & aliveb[w]);
            if (g == 0) continue;
            long sc = (long)g * 64 + rndi(64);
            if (sc > bsc) { bsc = sc; best = u; }
        }
        if (best < 0) break;
        S[ns++] = best;
        chosen_[best] = 1;
        for (int w = 0; w < W; w++) U[w] |= ball_[best][w];
        ok = 1;
        for (int w = 0; w < W; w++)
            if ((U[w] & aliveb[w]) != aliveb[w]) { ok = 0; break; }
        if (ok) break;
    }
    int x = -1;
    if (ok) {
        for (int v = 0; v < nslots; v++) if (!alive_[v]) { x = v; break; }
        if (x < 0) {
            if (nslots < NMAX) x = nslots++;
            else ok = 0;
        }
    }
    if (ok) {
        alive_[x] = 1;
        side_[x] = X;
        deg_[x] = 0;
        for (int i = 0; i < ns; i++) {
            int u = S[i];
            adj_[x][deg_[x]++] = u;
            adj_[u][deg_[u]++] = x;
        }
        alive_cnt++;
        recompute_aliveb();
        compute_balls(DD - 1, ball_);
    }
    for (int i = 0; i < ns; i++) chosen_[S[i]] = 0;
    return ok;
}

static void remove_vertex(int x) {
    for (int i = 0; i < deg_[x]; i++) {
        int u = adj_[x][i];
        for (int j = 0; j < deg_[u]; j++)
            if (adj_[u][j] == x) { adj_[u][j] = adj_[u][deg_[u] - 1]; break; }
        deg_[u]--;
    }
    deg_[x] = 0;
    alive_[x] = 0;
    alive_cnt--;
    recompute_aliveb();
    compute_balls(DD - 1, ball_);
}

static void save_state(State *s) {
    s->nslots = nslots;
    s->alive_cnt = alive_cnt;
    memcpy(s->side, side_, sizeof(int) * nslots);
    memcpy(s->alive, alive_, sizeof(int) * nslots);
    memcpy(s->deg, deg_, sizeof(int) * nslots);
    memcpy(s->adj, adj_, sizeof(int) * nslots * DMAX);
}

static void load_state(const State *s) {
    nslots = s->nslots;
    alive_cnt = s->alive_cnt;
    memcpy(side_, s->side, sizeof(int) * nslots);
    memcpy(alive_, s->alive, sizeof(int) * nslots);
    memcpy(deg_, s->deg, sizeof(int) * nslots);
    memcpy(adj_, s->adj, sizeof(int) * nslots * DMAX);
    recompute_aliveb();
    compute_balls(DD - 1, ball_);
}

static void output_state(const State *s) {
    static int map[NMAX];
    int k = 0, m = 0;
    for (int v = 0; v < s->nslots; v++) map[v] = s->alive[v] ? k++ : -1;
    for (int v = 0; v < s->nslots; v++)
        if (s->alive[v])
            for (int i = 0; i < s->deg[v]; i++)
                if (s->adj[v][i] > v) m++;
    printf("%d %d\n", k, m);
    for (int v = 0; v < s->nslots; v++) {
        if (!s->alive[v]) continue;
        for (int i = 0; i < s->deg[v]; i++) {
            int u = s->adj[v][i];
            if (u > v) printf("%d %d\n", map[v], map[u]);
        }
    }
}

static void echo_input(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

static int eu[NMAX * DMAX], ev[NMAX * DMAX];
static int qu[NMAX];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double t0 = elapsed();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n == 0) {
        n = 2 * dd;
        m = 0;
        for (int i = 0; i < dd; i++)
            for (int j = 0; j < dd; j++) { eu[m] = i; ev[m] = dd + j; m++; }
    } else {
        if (n > NMAX - 300 || m > NMAX * DMAX) { printf("0 0\n"); return 0; }
        for (int i = 0; i < m; i++)
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m = i; break; }
    }

    nslots = n;
    alive_cnt = n;
    int ok = 1;
    for (int v = 0; v < n; v++) { alive_[v] = 1; deg_[v] = 0; side_[v] = -1; }
    for (int i = 0; i < m && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg_[u] >= DMAX || deg_[v] >= DMAX) {
            ok = 0;
            break;
        }
        adj_[u][deg_[u]++] = v;
        adj_[v][deg_[v]++] = u;
    }
    for (int v = 0; v < n && ok; v++) if (deg_[v] > dd) ok = 0;
    for (int s = 0; s < n && ok; s++) {
        if (side_[s] >= 0) continue;
        side_[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt && ok) {
            int u = qu[qh++];
            for (int i = 0; i < deg_[u]; i++) {
                int v = adj_[u][i];
                if (side_[v] < 0) { side_[v] = 1 - side_[u]; qu[qt++] = v; }
                else if (side_[v] == side_[u]) { ok = 0; break; }
            }
        }
    }
    if (!ok || DD < 2) { echo_input(n, m, eu, ev); return 0; }

    recompute_aliveb();
    compute_balls(DD - 1, ball_);
    if (!check_valid()) { echo_input(n, m, eu, ev); return 0; }
    save_state(&best_);

    double t_end = t0 + budget;
    int fails = 0;
    while (fails < 60 && elapsed() < t_end) {
        if (try_insert()) fails = 0;
        else fails++;
    }
    if (check_valid() && alive_cnt > best_.alive_cnt) save_state(&best_);

    while (elapsed() < t_end) {
        save_state(&snap_);
        int k = 1 + rndi(3);
        for (int i = 0; i < k && alive_cnt > 3; i++) {
            int x = -1;
            for (int tries = 0; tries < 100000 && x < 0; tries++) {
                int c = rndi(nslots);
                if (alive_[c]) x = c;
            }
            if (x >= 0) remove_vertex(x);
        }
        fails = 0;
        while (fails < 40) {
            if (try_insert()) fails = 0;
            else fails++;
        }
        int valid = check_valid();
        if (valid && alive_cnt > best_.alive_cnt) save_state(&best_);
        int accept = valid && (alive_cnt >= snap_.alive_cnt || rndi(100) < 2);
        if (!accept) load_state(&snap_);
    }

    output_state(&best_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), from the parent.
#
# Start from PG(2, q). Each old vertex has degree q+1, so spare s = d - q - 1.
# Add an A-vertex per point of SA (joined to the q+1 lines through it), with
# every line holding <= s points of SA, and a B-vertex per line of SB (joined
# to its q+1 points), with every point on <= s lines of SB.
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so every target is hit by <= s chosen elements."""
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
# Generalized quadrangle W(q) baseline (D = 4), from the parent.
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
# Glue: run the C ruin-and-recreate engine from the best starts.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    starts = [fallback]
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in cands:
            consider(n_c, e_c)
            starts.append((n_c, e_c))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            starts.append(gq)

    # C search, started from the two largest valid starts, with the time split between them.
    if D >= 2 and d <= 60:
        starts = sorted(starts, key=lambda t: -t[0])[:2]
        for idx, st in enumerate(starts):
            remaining = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
            budget = remaining / (len(starts) - idx)
            if budget < 0.5:
                break
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed * 31 + idx, round(budget, 2)],
                                stdin_graph=st, timeout=budget + 6.0)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
