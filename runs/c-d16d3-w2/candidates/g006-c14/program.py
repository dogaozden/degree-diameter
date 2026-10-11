import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over bipartite graphs with fixed vertex count.
#
# Input: a bipartite graph with max degree d (the start graph may contain
# vertices of degree 1 or d-1). Moves keep the bipartition: degree-preserving
# double swaps, endpoint reattachment, and greedy insertion of edges between
# deficient vertices on opposite sides. Cost = number of ordered vertex pairs
# at distance > D (bitset BFS). Prints the best state found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 64
#define WMAX 16

static int N, DEG, DIAM;
static int Wn;
static unsigned char adj[MAXN][MAXN];
static int nb[MAXN][MAXDEG];
static int dg[MAXN];
static int col[MAXN];
static int LS[2][MAXN];
static int nLS[2];
static uint64_t RR[2][MAXN][WMAX];
static int SE[MAXN * MAXDEG / 2 + 8][2];
static int SM;
static uint64_t rs;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double wall_now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_e(int a, int b) {
    adj[a][b] = 1;
    adj[b][a] = 1;
    nb[a][dg[a]++] = b;
    nb[b][dg[b]++] = a;
}

static void del_from(int a, int b) {
    for (int i = 0; i < dg[a]; i++) {
        if (nb[a][i] == b) {
            nb[a][i] = nb[a][--dg[a]];
            return;
        }
    }
}

static void del_e(int a, int b) {
    adj[a][b] = 0;
    adj[b][a] = 0;
    del_from(a, b);
    del_from(b, a);
}

static long long eval_cost(void) {
    int cur = 0;
    Wn = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < Wn; w++) RR[0][v][w] = 0;
        RR[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        int nx = cur ^ 1;
        for (int v = 0; v < N; v++) {
            uint64_t *dst = RR[nx][v];
            const uint64_t *src0 = RR[cur][v];
            for (int w = 0; w < Wn; w++) dst[w] = src0[w];
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *src = RR[cur][nb[v][i]];
                for (int w = 0; w < Wn; w++) dst[w] |= src[w];
            }
        }
        cur = nx;
    }
    long long c = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        for (int w = 0; w < Wn; w++) pc += popc64(RR[cur][v][w]);
        c += N - pc;
    }
    return c;
}

static void snapshot(void) {
    SM = 0;
    for (int a = 0; a < N; a++) {
        for (int i = 0; i < dg[a]; i++) {
            int b = nb[a][i];
            if (a < b) {
                SE[SM][0] = a;
                SE[SM][1] = b;
                SM++;
            }
        }
    }
}

static int try_add(void) {
    static int d0[MAXN], d1[MAXN];
    int n0 = 0, n1 = 0;
    for (int i = 0; i < nLS[0]; i++) if (dg[LS[0][i]] < DEG) d0[n0++] = LS[0][i];
    for (int i = 0; i < nLS[1]; i++) if (dg[LS[1][i]] < DEG) d1[n1++] = LS[1][i];
    for (int i = 0; i < n0; i++) {
        for (int j = 0; j < n1; j++) {
            if (!adj[d0[i]][d1[j]]) {
                add_e(d0[i], d1[j]);
                return 1;
            }
        }
    }
    return 0;
}

static int ua1, ub1, ua2, ub2;
static int mx, my, mz;

static int move_swap(void) {
    int a1 = LS[0][rndi(nLS[0])];
    int a2 = LS[0][rndi(nLS[0])];
    if (a1 == a2 || !dg[a1] || !dg[a2]) return 0;
    int b1 = nb[a1][rndi(dg[a1])];
    int b2 = nb[a2][rndi(dg[a2])];
    if (b1 == b2 || adj[a1][b2] || adj[a2][b1]) return 0;
    del_e(a1, b1);
    del_e(a2, b2);
    add_e(a1, b2);
    add_e(a2, b1);
    ua1 = a1; ub1 = b1; ua2 = a2; ub2 = b2;
    return 1;
}

static void undo_swap(void) {
    del_e(ua1, ub2);
    del_e(ua2, ub1);
    add_e(ua1, ub1);
    add_e(ua2, ub2);
}

static int move_reattach(void) {
    int s = rndi(2);
    int x = LS[s][rndi(nLS[s])];
    if (!dg[x]) return 0;
    int y = nb[x][rndi(dg[x])];
    int z = LS[1 - s][rndi(nLS[1 - s])];
    if (z == y || dg[z] >= DEG || adj[x][z]) return 0;
    del_e(x, y);
    add_e(x, z);
    mx = x; my = y; mz = z;
    return 1;
}

static void undo_reattach(void) {
    del_e(mx, mz);
    add_e(mx, my);
}

static void print_out(void) {
    printf("%d %d\n", N, SM);
    for (int i = 0; i < SM; i++) printf("%d %d\n", SE[i][0], SE[i][1]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)strtoull(argv[3], NULL, 10) * 0xD1B54A32D192ED03ULL);
    if (rs == 0) rs = 1;
    double budget = strtod(argv[4], NULL);
    if (budget <= 0) budget = 1.0;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) { bad = 1; break; }
        if (a < 0 || a >= N || b < 0 || b >= N || a == b || adj[a][b] || dg[a] >= DEG || dg[b] >= DEG) {
            bad = 1;
            continue;
        }
        add_e(a, b);
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    for (int v = 0; v < N; v++) col[v] = -1;
    static int qu[MAXN];
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int i = 0; i < dg[u]; i++) {
                int v = nb[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qu[t++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    nLS[0] = nLS[1] = 0;
    for (int v = 0; v < N; v++) LS[col[v]][nLS[col[v]]++] = v;

    if (nLS[0] == 0 || nLS[1] == 0) {
        snapshot();
        print_out();
        return 0;
    }

    while (try_add()) {}

    long long cur = eval_cost();
    long long bestc = cur;
    snapshot();

    double t0 = wall_now();
    const double T0 = 1.0, T1 = 0.05;
    double T = T0;
    long it = 0;
    while (cur > 0) {
        if ((it & 31) == 0) {
            double el = wall_now() - t0;
            if (el >= budget) break;
            double f = el / budget;
            T = T0 * pow(T1 / T0, f);
        }
        it++;
        if (try_add()) {
            cur = eval_cost();
        } else if (rndi(10) < 5) {
            if (!move_swap()) continue;
            long long nc = eval_cost();
            long long dl = nc - cur;
            if (dl <= 0 || rnd01() < exp(-(double)dl / T)) cur = nc;
            else undo_swap();
        } else {
            if (!move_reattach()) continue;
            long long nc = eval_cost();
            long long dl = nc - cur;
            if (dl <= 0 || rnd01() < exp(-(double)dl / T)) cur = nc;
            else undo_reattach();
        }
        if (cur < bestc) {
            bestc = cur;
            snapshot();
        }
    }
    print_out();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add a new vertex per chosen point
# (joined to its q+1 lines) subject to every line being hit by <= s chosen
# points, and symmetrically for lines. Diameter stays 3.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    na, nb_ = len(SA), len(SB)
    n = 2 * m + na + nb_
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Refinement: add a few vertices to a valid graph (attached to deficient
# vertices of the opposite side), then let the C engine repair it.
# ----------------------------------------------------------------------------

def _extend(n, edges, d, k, rnd):
    """Append up to k new vertices, each joined to one deficient vertex on the other side."""
    adj = lib.adjacency(n, edges)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    deg = [len(a) for a in adj]
    E = list(edges)
    cn = n
    added = 0
    for _ in range(k):
        opts = []
        for side in (0, 1):
            cands = [v for v in range(cn) if col[v] == 1 - side and deg[v] < d]
            if cands:
                opts.append((side, cands))
        if not opts:
            break
        side, cands = rnd.choice(opts)
        y = rnd.choice(cands)
        E.append((cn, y))
        col.append(side)
        deg.append(1)
        deg[y] += 1
        cn += 1
        added += 1
    return (cn, E) if added else None


def _refine(d, D, n0, e0, deadline, seed):
    best = (n0, e0)
    rnd = random.Random(seed * 1000003 + 17)
    k = 2
    rounds = 0
    while rounds < 40:
        left = deadline - time.monotonic()
        if left < 6.0:
            break
        budget = min(left - 4.0, 14.0)
        ext = _extend(best[0], best[1], d, k, rnd)
        if ext is None:
            break
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + rounds, round(budget, 3)],
                             stdin_graph=ext, timeout=budget + 5.0)
            gn, ge = lib.parse_graph_text(text)
        except Exception:
            break
        rounds += 1
        if gn > best[0] and lib.is_valid(gn, ge, d, D):
            best = (gn, ge)
        elif k > 1:
            k = 1
        else:
            break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        arc_deadline = start + 0.3 * time_limit
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands[:3]:
            consider(n_c, e_c)

        refine_deadline = start + 0.8 * time_limit
        try:
            rn, re_ = _refine(d, D, best_n, best_e, refine_deadline, seed)
            consider(rn, re_)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
