"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C annealer.

NEW IDEA (bad-pair annealing with growth): the parent only augmented by adding vertices whose
neighbourhoods had to cover everything at once, which fails once the base is dense. This program
instead keeps the vertex count fixed and anneals the EDGES against an objective equal to the number
of vertex pairs at distance more than D. Reachability is computed with bitsets (D rounds of OR over
neighbour bitsets), so one evaluation is cheap. Moves are degree-preserving double edge swaps
(x1,y1),(x2,y2) -> (x1,y2),(x2,y1), endpoint moves onto vertices with spare degree, and fills of
spare capacity. Bipartiteness is kept by only joining the two sides. Whenever the objective hits
zero the graph is valid and is saved; a new vertex is then added on the smaller side and greedily
joined to spare vertices that cover the most unreached pairs, and annealing repairs the rest. A
stall counter restores the last valid graph and regrows it with different random tie-breaks.
Python re-checks everything with lib.is_valid and keeps the arc start as a fallback.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define WORDS 32
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)
#define STALL 80000L
#define CYC 40000L
#define T0 2.0
#define T1 0.05

static int N, Dd, Dist;
static int deg[MAXN], side[MAXN], bq[MAXN];
static int nbr[MAXN][MAXDEG];
static unsigned char Adj[MAXN][MAXN];
static uint64_t RA[MAXN][WORDS], RB[MAXN][WORDS], EVR[MAXN][WORDS], BALL[MAXN][WORDS];
static int bestN, bestM;
static int bestE[MAXE][2];
static long cur_bad;
static double Tcur;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* out[v] = bitset of vertices within distance `rounds` of v. */
static void compute_reach(int rounds, uint64_t out[][WORDS]) {
    int w = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < w; i++) RA[v][i] = 0;
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    int ca = 1;
    for (int r = 0; r < rounds; r++) {
        uint64_t (*cur)[WORDS] = ca ? RA : RB;
        uint64_t (*nxt)[WORDS] = ca ? RB : RA;
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < w; i++) nxt[v][i] = cur[v][i];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *cu = cur[nbr[v][k]];
                for (int i = 0; i < w; i++) nxt[v][i] |= cu[i];
            }
        }
        ca = !ca;
    }
    uint64_t (*fin)[WORDS] = ca ? RA : RB;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < w; i++) out[v][i] = fin[v][i];
}

/* Number of unordered vertex pairs at distance > Dist (0 means valid). */
static long eval_bad(void) {
    int w = (N + 63) / 64;
    compute_reach(Dist, EVR);
    long reached = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < w; i++) reached += popc(EVR[v][i]);
    return (((long)N * N) - reached) / 2;
}

static void add_edge(int x, int y) {
    nbr[x][deg[x]++] = y;
    nbr[y][deg[y]++] = x;
    Adj[x][y] = Adj[y][x] = 1;
}

static void del_one(int x, int y) {
    for (int k = 0; k < deg[x]; k++)
        if (nbr[x][k] == y) {
            nbr[x][k] = nbr[x][--deg[x]];
            return;
        }
}

static void remove_edge(int x, int y) {
    del_one(x, y);
    del_one(y, x);
    Adj[x][y] = Adj[y][x] = 0;
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) Adj[v][nbr[v][k]] = 0;
        deg[v] = 0;
    }
    N = 0;
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (nbr[v][k] > v && bestM < MAXE) {
                bestE[bestM][0] = v;
                bestE[bestM][1] = nbr[v][k];
                bestM++;
            }
}

static void load_best(void) {
    clear_graph();
    N = bestN;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < bestM; i++) add_edge(bestE[i][0], bestE[i][1]);
}

/* Add one isolated vertex on the smaller side, then greedily join spare
   vertices of the other side that cover the most still-unreached vertices. */
static void grow_one(void) {
    int c0 = 0, c1 = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] == 0) c0++;
        else c1++;
    }
    int X = (c0 <= c1) ? 0 : 1;
    int x = N;
    side[x] = X;
    deg[x] = 0;
    N++;
    int w = (N + 63) / 64;
    compute_reach(Dist - 1, BALL);
    uint64_t U[WORDS];
    for (int i = 0; i < w; i++) U[i] = ~0ULL;
    if (N & 63) U[w - 1] = (1ULL << (N & 63)) - 1ULL;
    U[x >> 6] &= ~(1ULL << (x & 63));
    for (int k = 0; k < Dd; k++) {
        int best = -1;
        long bs = -1;
        for (int y = 0; y < N; y++) {
            if (y == x || side[y] == X || deg[y] >= Dd) continue;
            long g = 0;
            for (int i = 0; i < w; i++) g += popc(BALL[y][i] & U[i]);
            if (g <= 0) continue;
            long sc = g * 1000 + rndint(1000);
            if (sc > bs) {
                bs = sc;
                best = y;
            }
        }
        if (best < 0) break;
        add_edge(x, best);
        for (int i = 0; i < w; i++) U[i] &= ~BALL[best][i];
    }
}

static int pick_edge(int *ex, int *ey) {
    for (int t = 0; t < 50; t++) {
        int v = rndint(N);
        if (deg[v] == 0) continue;
        int u = nbr[v][rndint(deg[v])];
        if (side[v] == 0) {
            *ex = v;
            *ey = u;
        } else {
            *ex = u;
            *ey = v;
        }
        return 1;
    }
    return 0;
}

static int pick_side(int s) {
    for (int t = 0; t < 60; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] < Dd) return v;
    }
    return -1;
}

static int accept(long delta) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / Tcur);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 7777ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 64 || Dist < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (Adj[u][v] || deg[u] >= Dd || deg[v] >= Dd) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        bq[t++] = s;
        while (h < t) {
            int u = bq[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nbr[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    save_best();
    cur_bad = eval_bad();
    Tcur = T0;

    long iter = 0, lastImp = 0;
    long minBad = cur_bad;
    double t_end = cpu_now() + budget;
    while (cpu_now() < t_end) {
        iter++;
        if (cur_bad == 0) {
            if (N > bestN) save_best();
            if (N + 1 >= MAXN) break;
            grow_one();
            cur_bad = eval_bad();
            minBad = cur_bad;
            lastImp = iter;
            continue;
        }
        if (iter - lastImp > STALL) {
            load_best();
            cur_bad = eval_bad();
            minBad = cur_bad;
            lastImp = iter;
            continue;
        }
        Tcur = T0 * pow(T1 / T0, (double)(iter % CYC) / (double)CYC);
        int mv = rndint(100);
        if (mv < 10) {
            int x = pick_side(0), y = pick_side(1);
            if (x < 0 || y < 0 || Adj[x][y]) continue;
            add_edge(x, y);
            long nb = eval_bad();
            if (nb <= cur_bad) cur_bad = nb;
            else remove_edge(x, y);
        } else if (mv < 55) {
            int x1, y1, x2, y2;
            if (!pick_edge(&x1, &y1) || !pick_edge(&x2, &y2)) continue;
            if (x1 == x2 || y1 == y2 || Adj[x1][y2] || Adj[x2][y1]) continue;
            remove_edge(x1, y1);
            remove_edge(x2, y2);
            add_edge(x1, y2);
            add_edge(x2, y1);
            long nb = eval_bad();
            if (accept(nb - cur_bad)) cur_bad = nb;
            else {
                remove_edge(x1, y2);
                remove_edge(x2, y1);
                add_edge(x1, y1);
                add_edge(x2, y2);
            }
        } else {
            int x, y;
            if (!pick_edge(&x, &y)) continue;
            if (rndint(2)) {
                int y2 = pick_side(1);
                if (y2 < 0 || y2 == y || Adj[x][y2]) continue;
                remove_edge(x, y);
                add_edge(x, y2);
                long nb = eval_bad();
                if (accept(nb - cur_bad)) cur_bad = nb;
                else {
                    remove_edge(x, y2);
                    add_edge(x, y);
                }
            } else {
                int x2 = pick_side(0);
                if (x2 < 0 || x2 == x || Adj[x2][y]) continue;
                remove_edge(x, y);
                add_edge(x2, y);
                long nb = eval_bad();
                if (accept(nb - cur_bad)) cur_bad = nb;
                else {
                    remove_edge(x2, y);
                    add_edge(x, y);
                }
            }
        }
        if (cur_bad < minBad) {
            minBad = cur_bad;
            lastImp = iter;
        }
    }
    if (cur_bad == 0 && N > bestN) save_best();

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[i][0], bestE[i][1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence. Each vertex has spare capacity s = d - q - 1.
# Choose a point set S so that each line holds at most s points of S, then add
# an A-vertex per point of S (joined to lines through it) and a B-vertex per
# element of S (joined to points on that line).
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
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
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# Driver.
# ----------------------------------------------------------------------------

def _anneal(n0, e0, d, D, seed, budget, timeout):
    """Run the C bad-pair annealer from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = starts[0]

    # Anneal the largest valid start; the C engine only returns valid graphs.
    remaining = hard_end - time.monotonic()
    budget = remaining - 4.0
    if budget > 1.0:
        try:
            n1, e1 = _anneal(best[0], best[1], d, D, seed * 31 + 7,
                             budget, budget + 6.0)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
