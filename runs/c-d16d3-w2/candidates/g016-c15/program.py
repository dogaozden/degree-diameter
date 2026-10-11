import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair annealing for bipartite graphs with diameter <= D.
#
# State: a valid bipartite graph with max degree d. Each iteration either
#   * grows: adds a vertex on a random side and joins it greedily to spare
#     vertices of the opposite side (the choice minimises the number of pairs
#     at distance > D among a random sample of candidates), or
#   * repairs: applies a random move (degree-preserving double edge swap,
#     edge insertion between spare vertices, or edge deletion) and accepts it by
#     the Metropolis rule on cost = number of ordered-unordered vertex pairs at
#     distance > D.
# A repair that stalls is rolled back to the last valid snapshot. The best valid
# graph (largest order) is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXW 25
#define MAXDEG 40
#define STALL 3000
#define NEDGE (MAXN * MAXDEG / 2)

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
} State;

typedef struct {
    int typ, p, q, r, s;
} Move;

static State S, SNAP, BEST;
static uint64_t R[2][MAXN][MAXW];
static int d, D, NCAP;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double runif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered-unordered pairs (u,v), u != v, at distance > D (counted twice). */
static long long evalbad(void) {
    int n = S.n, Wn = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < Wn; w++) R[0][v][w] = 0;
        R[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        int src = r & 1, dst = src ^ 1;
        for (int v = 0; v < n; v++) {
            uint64_t *o = R[dst][v];
            const uint64_t *sv = R[src][v];
            for (int w = 0; w < Wn; w++) o[w] = sv[w];
            for (int k = 0; k < S.deg[v]; k++) {
                const uint64_t *t = R[src][S.adj[v][k]];
                for (int w = 0; w < Wn; w++) o[w] |= t[w];
            }
        }
    }
    int fin = D & 1;
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < Wn; w++) c += popc(R[fin][v][w]);
        bad += n - c;
    }
    return bad;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < S.deg[a]; k++)
        if (S.adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    S.adj[a][S.deg[a]++] = b;
    S.adj[b][S.deg[b]++] = a;
}

static void del_half(int a, int b) {
    for (int k = 0; k < S.deg[a]; k++) {
        if (S.adj[a][k] == b) {
            S.adj[a][k] = S.adj[a][S.deg[a] - 1];
            S.deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static int pick_side(int s) {
    for (int t = 0; t < 64; t++) {
        int v = rint_(S.n);
        if (S.side[v] == s) return v;
    }
    return -1;
}

static void apply_move(const Move *m) {
    if (m->typ == 1) {          /* double swap: (p,q),(r,s) -> (p,s),(r,q) */
        del_edge(m->p, m->q);
        del_edge(m->r, m->s);
        add_edge(m->p, m->s);
        add_edge(m->r, m->q);
    } else if (m->typ == 2) {   /* insert (p,q) */
        add_edge(m->p, m->q);
    } else {                    /* delete (p,q) */
        del_edge(m->p, m->q);
    }
}

static void undo_move(const Move *m) {
    if (m->typ == 1) {
        del_edge(m->p, m->s);
        del_edge(m->r, m->q);
        add_edge(m->p, m->q);
        add_edge(m->r, m->s);
    } else if (m->typ == 2) {
        del_edge(m->p, m->q);
    } else {
        add_edge(m->p, m->q);
    }
}

/* Add one vertex on a random side, joined greedily to spare opposite vertices. */
static int grow(void) {
    if (S.n >= NCAP) return 0;
    int s = rint_(2);
    int x = S.n;
    S.n++;
    S.side[x] = s;
    S.deg[x] = 0;
    static int cand[MAXN];
    int added = 0;
    for (int k = 0; k < d; k++) {
        int nc = 0;
        for (int v = 0; v < x; v++)
            if (S.side[v] != s && S.deg[v] < d) cand[nc++] = v;
        if (nc == 0) break;
        int trials = nc < 10 ? nc : 10;
        int bestc = -1;
        long long bestb = 0;
        for (int t = 0; t < trials; t++) {
            int c = cand[rint_(nc)];
            if (has_edge(x, c)) continue;
            add_edge(x, c);
            long long b = evalbad();
            del_edge(x, c);
            if (bestc < 0 || b < bestb) {
                bestc = c;
                bestb = b;
            }
        }
        if (bestc < 0) break;
        add_edge(x, bestc);
        added++;
    }
    if (added == 0) {
        S.n--;
        return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > MAXDEG || D < 1) return 1;
    rs ^= 0x9E3779B97F4A7C15ULL * (seed + 1);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2) return 1;
    if (n0 < 1 || n0 > MAXN - 1 || m0 < 0 || m0 > NEDGE) return 1;
    static int eu[NEDGE], ev[NEDGE];
    for (int i = 0; i < m0; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 1;

    memset(&S, 0, sizeof(S));
    S.n = n0;
    for (int i = 0; i < m0; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n0 || b >= n0 || a == b) return 1;
        if (S.deg[a] >= d || S.deg[b] >= d || has_edge(a, b)) return 1;
        add_edge(a, b);
    }

    /* Bipartition by BFS. */
    static int queue[MAXN];
    for (int v = 0; v < n0; v++) S.side[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (S.side[s] >= 0) continue;
        S.side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int v = queue[qh++];
            for (int k = 0; k < S.deg[v]; k++) {
                int u = S.adj[v][k];
                if (S.side[u] < 0) {
                    S.side[u] = 1 - S.side[v];
                    queue[qt++] = u;
                } else if (S.side[u] == S.side[v]) {
                    return 1;
                }
            }
        }
    }

    NCAP = n0 + 400;
    if (NCAP > MAXN) NCAP = MAXN;
    if (evalbad() != 0) return 1;

    BEST = S;
    SNAP = S;
    int bestN = n0;
    double tend = now_s() + budget;
    long long cur = 0, stall = 0, it = 0;
    const double T = 0.5;

    while (1) {
        if ((it & 63) == 0 && now_s() > tend) break;
        it++;

        if (cur == 0) {
            if (S.n > bestN) {
                bestN = S.n;
                BEST = S;
            }
            SNAP = S;
            if (grow()) {
                cur = evalbad();
            } else {
                /* No spare capacity: free some by deleting a random edge. */
                int a = pick_side(0);
                if (a >= 0 && S.deg[a] > 0) {
                    int b = S.adj[a][rint_(S.deg[a])];
                    del_edge(a, b);
                }
                cur = evalbad();
            }
            stall = 0;
            continue;
        }

        stall++;
        if (stall > STALL) {
            S = SNAP;
            cur = evalbad();
            stall = 0;
            continue;
        }

        Move mv;
        mv.typ = 0;
        double r = runif();
        if (r < 0.6) {
            int a = pick_side(0), a2 = pick_side(0);
            if (a < 0 || a2 < 0 || a == a2 || S.deg[a] == 0 || S.deg[a2] == 0) continue;
            int b = S.adj[a][rint_(S.deg[a])];
            int b2 = S.adj[a2][rint_(S.deg[a2])];
            if (b == b2 || has_edge(a, b2) || has_edge(a2, b)) continue;
            mv.typ = 1;
            mv.p = a;
            mv.q = b;
            mv.r = a2;
            mv.s = b2;
        } else if (r < 0.85) {
            int a = pick_side(0), b = pick_side(1);
            if (a < 0 || b < 0 || S.deg[a] >= d || S.deg[b] >= d || has_edge(a, b)) continue;
            mv.typ = 2;
            mv.p = a;
            mv.q = b;
        } else {
            int a = pick_side(0);
            if (a < 0 || S.deg[a] == 0) continue;
            int b = S.adj[a][rint_(S.deg[a])];
            mv.typ = 3;
            mv.p = a;
            mv.q = b;
        }

        apply_move(&mv);
        long long c2 = evalbad();
        long long delta = c2 - cur;
        if (delta <= 0 || runif() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            undo_move(&mv);
        }
    }

    if (cur == 0 && S.n > bestN) {
        bestN = S.n;
        BEST = S;
    }

    int bn = BEST.n, me = 0;
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < BEST.deg[v]; k++)
            if (v < BEST.adj[v][k]) me++;
    printf("%d %d\n", bn, me);
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < BEST.deg[v]; k++)
            if (v < BEST.adj[v][k]) printf("%d %d\n", v, BEST.adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. New A-vertices are attached to
# lines through chosen points (each line holds <= s of them), and new B-vertices
# to points on chosen lines (each point lies on <= s of them). Diameter stays 3.
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
    """True if every target t is hit by <= s elements of S."""
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
    """Plateau/improvement local search for the same load-constrained set problem."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

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
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is a valid fallback for D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = [fallback]
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        starts.extend(cands)
    starts = [g for g in starts if g[0] > 0 and lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    best = starts[0]

    # Grow-and-repair search in C, from the two largest valid starts.
    top = starts[:2]
    deadline = t0 + 0.85 * time_limit
    for i, g in enumerate(top):
        left = deadline - time.monotonic()
        if left < 1.0:
            break
        budget = left / (len(top) - i)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed + 1000 * i, round(budget, 2)],
                            stdin_graph=g, timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            continue

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
