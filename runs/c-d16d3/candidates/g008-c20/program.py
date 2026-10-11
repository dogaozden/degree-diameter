import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grows a valid bipartite graph (max degree d, diameter <= D) by
# attaching one new vertex at a time. Each new vertex's neighbour set is found
# by simulated annealing that minimises the number of vertex pairs at distance
# greater than D, computed with 64-bit bitset ball expansion. Only new-vertex
# edges change, so every accepted state is valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1400
#define WMAX 22
#define MAXDEG 64

static int n, d, D;
static int dg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t R1[MAXN][WMAX], R2[MAXN][WMAX];
static int W;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int irand(int k) { return (int)(rnd() % (uint64_t)k); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int u, int v) {
    for (int i = 0; i < dg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}
static void half_del(int u, int v) {
    for (int i = 0; i < dg[u]; i++) {
        if (adj[u][i] == v) { adj[u][i] = adj[u][--dg[u]]; return; }
    }
}
static void add_edge(int u, int v) { adj[u][dg[u]++] = v; adj[v][dg[v]++] = u; }
static void del_edge(int u, int v) { half_del(u, v); half_del(v, u); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,u) with dist(v,u) > D. Zero means valid. */
static long long cost(void) {
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(R1[v], 0, sizeof(uint64_t) * W);
        R1[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(R2[v], R1[v], sizeof(uint64_t) * W);
            for (int i = 0; i < dg[v]; i++) {
                uint64_t *src = R1[adj[v][i]];
                for (int w = 0; w < W; w++) R2[v][w] |= src[w];
            }
        }
        for (int v = 0; v < n; v++) memcpy(R1[v], R2[v], sizeof(uint64_t) * W);
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R1[v][w]);
        bad += n - c;
    }
    return bad;
}

/* Random vertex on the opposite side of x with spare capacity, not yet adjacent to x. */
static int pick_partner(int x) {
    if (x <= 0 || dg[x] >= d) return -1;
    for (int tr = 0; tr < 400; tr++) {
        int y = irand(x);
        if (side[y] != side[x] && dg[y] < d && !has_edge(x, y)) return y;
    }
    return -1;
}

static void emit(void) {
    long long m = 0;
    for (int v = 0; v < n; v++) m += dg[v];
    m /= 2;
    printf("%d %lld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < dg[u]; i++) {
            int v = adj[u][i];
            if (u < v) printf("%d %d\n", u, v);
        }
}

int main(int argc, char **argv) {
    int m;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 8 || m < 0 ||
        d < 1 || d > MAXDEG || D < 1) {
        printf("1 0\n");
        return 0;
    }
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            dg[u] >= d || dg[v] >= d || has_edge(u, v)) { ok = 0; break; }
        add_edge(u, v);
    }
    static int qu[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s0 = 0; s0 < n && ok; s0++) {
        if (side[s0] != -1) continue;
        side[s0] = 0;
        int h = 0, t = 0;
        qu[t++] = s0;
        while (h < t && ok) {
            int u = qu[h++];
            for (int i = 0; i < dg[u]; i++) {
                int v = adj[u][i];
                if (side[v] == -1) { side[v] = 1 - side[u]; qu[t++] = v; }
                else if (side[v] == side[u]) { ok = 0; break; }
            }
        }
    }
    if (!ok || cost() != 0) {
        printf("1 0\n");
        return 0;
    }

    clock_t t0 = clock();
    const int iters = 6000;
    while (n + 1 < MAXN - 1) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        int x = n++;
        side[x] = (int)(rnd() & 1);
        dg[x] = 0;
        for (int k = 0; k < d; k++) {
            int y = pick_partner(x);
            if (y < 0) break;
            add_edge(x, y);
        }
        if (dg[x] == 0) { n--; break; }   /* no spare capacity on that side */

        long long c = cost();
        int success = (c == 0);
        for (int it = 0; it < iters && !success; it++) {
            double T = 3.0 * (1.0 - (double)it / iters) + 0.05;
            int mv = irand(3);
            if (mv == 0 || dg[x] == 0) {
                int y = pick_partner(x);
                if (y < 0) continue;
                add_edge(x, y);
                long long c2 = cost();
                if (c2 <= c || urand() < exp(-(double)(c2 - c) / T)) c = c2;
                else del_edge(x, y);
            } else if (mv == 1) {
                int y = adj[x][irand(dg[x])];
                del_edge(x, y);
                long long c2 = cost();
                if (c2 <= c || urand() < exp(-(double)(c2 - c) / T)) c = c2;
                else add_edge(x, y);
            } else {
                int y1 = adj[x][irand(dg[x])];
                del_edge(x, y1);
                int y2 = pick_partner(x);
                if (y2 < 0) { add_edge(x, y1); continue; }
                add_edge(x, y2);
                long long c2 = cost();
                if (c2 <= c || urand() < exp(-(double)(c2 - c) / T)) c = c2;
                else { del_edge(x, y2); add_edge(x, y1); }
            }
            if (c == 0) success = 1;
        }
        if (!success) {
            for (int i = 0; i < dg[x]; i++) half_del(adj[x][i], x);
            dg[x] = 0;
            n--;
        }
    }
    emit();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Construction: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q). Old vertices have degree q+1, so with spare s = d-q-1
# each can take up to s new edges. New A-vertices (one per point P in S_A)
# join the q+1 lines through P; new B-vertices (one per line j in S_B) join
# the q+1 points on j.
#
# NEW IDEA versus the parent: S_A and S_B are chosen INDEPENDENTLY. Lines
# only receive load from A-vertices, so S_A only needs every line to contain
# at most s points of S_A. Points only receive load from B-vertices, so S_B
# only needs every point to lie on at most s lines of S_B. Each side is found
# by randomized greedy, and the conic/oval is tried as a candidate.
# Diameter stays 3: A_P reaches every point via the line PQ, and A_P to B_j
# is joined by the path A_P - PQ - Q - B_j with Q on j.
# Order is 2m + |S_A| + |S_B|.
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


def _loads_ok(S, slots_of, num_slots, s):
    """True if every slot is used by at most s items of S."""
    load = [0] * num_slots
    for it in S:
        for x in slots_of[it]:
            load[x] += 1
    return max(load, default=0) <= s


def _greedy_sets(slots_of, num_items, num_slots, s, rng, trials, deadline):
    """Randomized greedy: pick items so that no slot is used more than s times."""
    best = []
    order = list(range(num_items))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * num_slots
        S = []
        for it in order:
            sl = slots_of[it]
            if all(load[x] < s for x in sl):
                S.append(it)
                for x in sl:
                    load[x] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): a 2-arc in PG(2,q), used as a point and as a line index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_candidate(d, q, rng, deadline):
    """Return (n, edges) for PG(2,q) extended with independent S_A and S_B, or None."""
    s = d - q - 1
    if s < 0:
        return None
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    SA, SB = [], []
    if s >= 1:
        SA = _greedy_sets(point_lines, m, m, s, rng, 30, deadline)   # points, load on lines
        SB = _greedy_sets(line_points, m, m, s, rng, 30, deadline)   # lines, load on points
    if s >= 2:
        F = lib.GF(q)
        cs = _conic_set(q, index, F)
        if len(cs) > len(SA) and _loads_ok(cs, point_lines, m, s):
            SA = cs
        if len(cs) > len(SB) and _loads_ok(cs, line_points, m, s):
            SB = cs
    n = 2 * m
    E = list(edges)
    for P in SA:
        x = n
        n += 1
        for L in point_lines[P]:
            E.append((x, m + L))
    for j in SB:
        y = n
        n += 1
        for Q in line_points[j]:
            E.append((Q, y))
    return n, E


def _has_spare(n, edges, d):
    """True if some vertex has degree below d (so augmentation can add edges)."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return any(x < d for x in deg)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D < 3:
        return best

    # Arc-extended projective plane graphs with independent S_A, S_B.
    rng = random.Random(seed * 7919 + d)
    deadline = t0 + 0.3 * time_limit
    cands = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        c = _arc_candidate(d, q, rng, deadline)
        if c is not None:
            cands.append(c)
    cands.sort(key=lambda t: -t[0])
    for n_c, e_c in cands:
        if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            best_n = n_c
            break

    # Augmentation: C search adds vertices one at a time into spare capacity.
    if _has_spare(best_n, best[1], d):
        rem = time_limit - (time.monotonic() - t0)
        budget = max(0.5, 0.75 * rem - 3.0)
        timeout = max(budget + 1.0, 0.9 * rem)
        try:
            txt = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=timeout)
            n2, e2 = lib.parse_graph_text(txt)
            if n2 > best_n and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
                best_n = n2
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
