import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Old vertices have degree q+1, so
# spare degree s = d - q - 1 is available. An A-vertex for point P joins the q+1
# lines through P; a B-vertex for line j joins the q+1 points on j. Loads per
# line (A) and per point (B) must stay <= s. Diameter stays 3 for any SA, SB.
# ----------------------------------------------------------------------------

_LS_ITERS = 8000


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
    """Randomized greedy load-constrained set."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, _pts = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# NEW in this version: C "growth annealing" repair engine.
#
# Starting from a valid bipartite graph, the engine alternates:
#   * growth: when the graph is valid (cost 0), add one vertex on a random side,
#     joined to up to d spare vertices of the opposite side;
#   * annealing: moves that rewire one edge endpoint (keeping bipartiteness and
#     degrees) or add an edge between spare vertices. The cost is the number of
#     vertex pairs at distance > D (unreachable pairs included).
#   * stall recovery: after a long stretch without reaching cost 0, the best
#     valid graph is restored and growth restarts from it.
# Only valid (cost 0) graphs are ever recorded as best, so output is valid.
# ----------------------------------------------------------------------------

_C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXD 40

static int d, D, N;
static int deg[MAXN], adj[MAXN][MAXD], side[MAXN];
static int bN = 0, bdeg[MAXN], badj[MAXN][MAXD];
static int dist_[MAXN], qu[MAXN];
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int ri(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rf(void) { return (double)(rnd() >> 11) / 9007199254740992.0; }

static int has_edge(int u, int w) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == w) return 1;
    return 0;
}
static void del_from(int u, int w) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == w) { adj[u][i] = adj[u][--deg[u]]; return; }
}
static void add_to(int u, int w) { adj[u][deg[u]++] = w; }
static void add_edge(int u, int w) { add_to(u, w); add_to(w, u); }
static void del_edge(int u, int w) { del_from(u, w); del_from(w, u); }

/* neighbour a of u becomes b (b on the same side as a, with spare degree) */
static void rewire(int u, int a, int b) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == a) { adj[u][i] = b; break; }
    del_from(a, u);
    add_to(b, u);
}

static long long cost(void) {
    long long bad = 0;
    for (int s = 0; s < N; s++) {
        for (int i = 0; i < N; i++) dist_[i] = -1;
        int h = 0, t = 0, cnt = 1;
        qu[t++] = s; dist_[s] = 0;
        while (h < t) {
            int u = qu[h++];
            if (dist_[u] >= D) continue;
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (dist_[v] < 0) { dist_[v] = dist_[u] + 1; qu[t++] = v; cnt++; }
            }
        }
        bad += N - cnt;
    }
    return bad / 2;
}

static void save_best(void) {
    bN = N;
    for (int i = 0; i < N; i++) {
        bdeg[i] = deg[i];
        memcpy(badj[i], adj[i], sizeof(int) * deg[i]);
    }
}

static void restore_best(void) {
    N = bN;
    for (int i = 0; i < N; i++) {
        deg[i] = bdeg[i];
        memcpy(adj[i], badj[i], sizeof(int) * deg[i]);
    }
}

static int read_and_color(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN / 2) return 0;
    N = n;
    for (int i = 0; i < N; i++) deg[i] = 0;
    for (int e = 0; e < m; e++) {
        int u, w;
        if (scanf("%d %d", &u, &w) != 2) return 0;
        if (u < 0 || w < 0 || u >= N || w >= N || u == w) return 0;
        if (has_edge(u, w)) return 0;
        if (deg[u] >= MAXD || deg[w] >= MAXD) return 0;
        add_edge(u, w);
    }
    for (int i = 0; i < N; i++) if (deg[i] > d) return 0;
    for (int i = 0; i < N; i++) side[i] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (side[v] < 0) { side[v] = 1 - side[u]; qu[t++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 1ULL;
    double limit = atof(argv[4]);
    clock_t c0 = clock();

    if (d < 1 || d > MAXD || D < 1 || !read_and_color()) {
        printf("0 0\n");
        return 0;
    }
    long long cur = cost();
    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    const long long STALL = 4000;
    long long stall = 0;
    long long it = 0;
    while (1) {
        if ((it & 127) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > limit) break;
        it++;

        if (cur == 0) {
            if (N > bN) save_best();
            if (N < MAXN - 1) {
                int x = N++;
                deg[x] = 0;
                side[x] = ri(2);
                for (int k = 0; k < 4 * d && deg[x] < d; k++) {
                    int w = ri(N - 1);
                    if (side[w] == side[x] || deg[w] >= d || has_edge(x, w)) continue;
                    add_edge(x, w);
                }
                cur = cost();
                stall = 0;
            }
            continue;
        }

        if (++stall > STALL) {
            restore_best();
            cur = cost();
            stall = 0;
            continue;
        }

        if (ri(10) < 2) {
            int u = ri(N), w = ri(N);
            if (u == w || side[u] == side[w] || deg[u] >= d || deg[w] >= d || has_edge(u, w)) continue;
            add_edge(u, w);
            long long nc = cost();
            double T = 0.3;
            if (nc <= cur || rf() < exp((double)(cur - nc) / T)) cur = nc;
            else del_edge(u, w);
        } else {
            int u = ri(N);
            if (deg[u] == 0) continue;
            int v = adj[u][ri(deg[u])];
            int w = ri(N);
            if (w == v || side[w] != side[v] || deg[w] >= d || has_edge(u, w)) continue;
            rewire(u, v, w);
            long long nc = cost();
            double T = 0.3;
            if (nc <= cur || rf() < exp((double)(cur - nc) / T)) cur = nc;
            else rewire(u, w, v);
        }
    }

    long long m = 0;
    for (int u = 0; u < bN; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) m++;
    printf("%d %lld\n", bN, m);
    for (int u = 0; u < bN; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) printf("%d %d\n", u, badj[u][i]);
    return 0;
}
'''


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        # Arc-extended projective plane graphs (diameter 3).
        cands = _arc_extensions(d, start + 0.3 * time_limit, rng)
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)

        # Growth annealing in C, starting from the best valid graph.
        remaining = time_limit - (time.monotonic() - start)
        c_budget = remaining * 0.8 - 1.0
        if c_budget > 0.5 and best[0] > 1:
            try:
                out = lib.run_c(_C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=best, timeout=remaining * 0.92)
                n_r, e_r = lib.parse_graph_text(out)
                if n_r > best[0] and lib.is_valid(n_r, e_r, d, D):
                    best = (n_r, e_r)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
