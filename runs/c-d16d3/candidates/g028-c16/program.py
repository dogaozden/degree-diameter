import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: defect-driven simulated annealing that grows a bipartite graph.
#
# Sides are fixed (edges only join side 0 to side 1), so bipartiteness is kept
# by construction. The cost is the number of unordered vertex pairs at distance
# greater than D, computed with bitset reachability. Moves are degree-preserving
# double swaps, endpoint rewires into spare capacity, and free edge additions
# (which never raise the cost). Vertices are added one at a time and annealed
# to cost zero; a failed step is rolled back to the last valid snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int DMAX = 0, DIAM = 0, CAP = 0, N = 0;
static int *side = NULL, *deg = NULL, *adj = NULL;
static int *s_side = NULL, *s_deg = NULL, *s_adj = NULL, s_N = 0;
static u64 *RA = NULL, *RB = NULL;
static u64 rs = 88172645463325252ULL;

enum { ANY = 0, HASDEG = 1, HASROOM = 2 };

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u * DMAX + i] == v) return 1;
    return 0;
}

static void rem_half(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u * DMAX + i] == v) {
            adj[u * DMAX + i] = adj[u * DMAX + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adj[u * DMAX + deg[u]++] = v;
    adj[v * DMAX + deg[v]++] = u;
}

static void del_edge(int u, int v) {
    rem_half(u, v);
    rem_half(v, u);
}

/* Number of unordered pairs at distance > DIAM. Zero means valid. */
static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    u64 *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(u64) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const u64 *src = cur + (size_t)adj[v * DMAX + i] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        const u64 *row = cur + (size_t)v * W;
        long long cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(row[w]);
        miss += (long long)N - cnt;
    }
    return miss / 2;
}

/* Random vertex on side s satisfying the mode, or -1. */
static int pick(int s, int mode) {
    for (int t = 0; t < 2000; t++) {
        int v = rndi(N);
        if (side[v] != s) continue;
        if (mode == HASDEG && deg[v] == 0) continue;
        if (mode == HASROOM && deg[v] >= DMAX) continue;
        return v;
    }
    return -1;
}

static void save_snap(void) {
    s_N = N;
    memcpy(s_side, side, sizeof(int) * (size_t)CAP);
    memcpy(s_deg, deg, sizeof(int) * (size_t)CAP);
    memcpy(s_adj, adj, sizeof(int) * (size_t)CAP * (size_t)DMAX);
}

static void load_snap(void) {
    N = s_N;
    memcpy(side, s_side, sizeof(int) * (size_t)CAP);
    memcpy(deg, s_deg, sizeof(int) * (size_t)CAP);
    memcpy(adj, s_adj, sizeof(int) * (size_t)CAP * (size_t)DMAX);
}

static double now_s(clock_t t0) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static long long anneal(double secs, double T0, double T1) {
    clock_t t0 = clock();
    long long cur = eval_cost();
    double T = T0;
    long long it = 0;
    while (cur > 0) {
        if ((it & 63) == 0) {
            double el = now_s(t0);
            if (el >= secs) break;
            T = T0 * pow(T1 / T0, el / secs);
        }
        it++;
        int r = rndi(100);
        if (r < 40) {
            /* degree-preserving double swap on side 0 pivots */
            int x = pick(0, HASDEG);
            int x2 = pick(0, HASDEG);
            if (x < 0 || x2 < 0 || x == x2) continue;
            int y = adj[x * DMAX + rndi(deg[x])];
            int y2 = adj[x2 * DMAX + rndi(deg[x2])];
            if (y == y2 || has_edge(x, y2) || has_edge(x2, y)) continue;
            del_edge(x, y);
            del_edge(x2, y2);
            add_edge(x, y2);
            add_edge(x2, y);
            long long nc = eval_cost();
            if (nc <= cur || rndf() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                del_edge(x, y2);
                del_edge(x2, y);
                add_edge(x, y);
                add_edge(x2, y2);
            }
        } else if (r < 85) {
            /* move one endpoint of an edge into spare capacity */
            int s = rndi(2);
            int x = pick(s, HASDEG);
            if (x < 0) continue;
            int y = adj[x * DMAX + rndi(deg[x])];
            int z;
            if (rndi(4) == 0 && N - 1 != y && side[N - 1] == 1 - s && deg[N - 1] < DMAX) z = N - 1;
            else z = pick(1 - s, HASROOM);
            if (z < 0 || z == y || has_edge(x, z)) continue;
            del_edge(x, y);
            add_edge(x, z);
            long long nc = eval_cost();
            if (nc <= cur || rndf() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                del_edge(x, z);
                add_edge(x, y);
            }
        } else {
            /* free edge addition: never increases the cost */
            int x = pick(0, HASROOM);
            int y = pick(1, HASROOM);
            if (x < 0 || y < 0 || has_edge(x, y)) continue;
            add_edge(x, y);
            cur = eval_cost();
        }
    }
    return cur;
}

static void fill_new(int z) {
    int s = side[z];
    for (int t = 0; t < 40 * DMAX && deg[z] < DMAX; t++) {
        int y = pick(1 - s, HASROOM);
        if (y < 0) break;
        if (has_edge(z, y)) continue;
        add_edge(z, y);
    }
}

static void print_graph(void) {
    long long m = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) if (adj[v * DMAX + i] > v) m++;
    printf("%d %lld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * DMAX + i];
            if (u > v) printf("%d %d\n", v, u);
        }
}

static void print_original(int n0, int m0, const int *eu, const int *ev) {
    printf("%d %d\n", n0, m0);
    for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed secs\n"); return 1; }
    DMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double total = atof(argv[4]);
    if (DMAX < 1 || DIAM < 1) return 1;
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    clock_t t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0) return 1;
    int ecap = m0 > DMAX * DMAX ? m0 : DMAX * DMAX;
    int *eu = malloc(sizeof(int) * (size_t)(ecap + 1));
    int *ev = malloc(sizeof(int) * (size_t)(ecap + 1));
    if (!eu || !ev) return 1;
    if (n0 == 0) {
        n0 = 2 * DMAX;
        m0 = 0;
        for (int i = 0; i < DMAX; i++)
            for (int j = 0; j < DMAX; j++) { eu[m0] = i; ev[m0] = DMAX + j; m0++; }
    } else {
        for (int i = 0; i < m0; i++)
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 1;
    }

    CAP = n0 + 600;
    int Wcap = (CAP + 63) >> 6;
    side = calloc((size_t)CAP, sizeof(int));
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DMAX, sizeof(int));
    s_side = calloc((size_t)CAP, sizeof(int));
    s_deg = calloc((size_t)CAP, sizeof(int));
    s_adj = calloc((size_t)CAP * DMAX, sizeof(int));
    RA = calloc((size_t)CAP * Wcap, sizeof(u64));
    RB = calloc((size_t)CAP * Wcap, sizeof(u64));
    if (!side || !deg || !adj || !s_side || !s_deg || !s_adj || !RA || !RB) return 1;

    int ok = 1;
    N = n0;
    for (int i = 0; i < m0 && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
        if (has_edge(u, v)) continue;
        if (deg[u] >= DMAX || deg[v] >= DMAX) { ok = 0; break; }
        add_edge(u, v);
    }
    if (ok) {
        int *col = malloc(sizeof(int) * (size_t)CAP);
        int *stk = malloc(sizeof(int) * (size_t)CAP);
        for (int v = 0; v < CAP; v++) col[v] = -1;
        for (int s = 0; s < N && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0 && ok) {
                int x = stk[--sp];
                for (int i = 0; i < deg[x]; i++) {
                    int y = adj[x * DMAX + i];
                    if (col[y] < 0) { col[y] = 1 - col[x]; stk[sp++] = y; }
                    else if (col[y] == col[x]) { ok = 0; break; }
                }
            }
        }
        if (ok) for (int v = 0; v < N; v++) side[v] = col[v];
        free(col);
        free(stk);
    }
    if (!ok) { print_original(n0, m0, eu, ev); return 0; }

    long long c = eval_cost();
    if (c != 0) c = anneal(total * 0.2, 1.0, 0.05);
    if (c != 0) { print_original(n0, m0, eu, ev); return 0; }

    save_snap();
    int fails = 0;
    while (fails < 3 && N + 1 < CAP) {
        double remain = total - now_s(t0);
        if (remain < 1.0) break;
        int c0 = 0, c1 = 0;
        for (int v = 0; v < N; v++) { if (side[v]) c1++; else c0++; }
        int s = (c0 <= c1) ? 0 : 1;
        side[N] = s;
        deg[N] = 0;
        N++;
        fill_new(N - 1);
        double slice = remain * 0.5;
        long long r = anneal(slice, 2.0, 0.05);
        if (r == 0) { save_snap(); fails = 0; }
        else { load_snap(); fails++; }
    }
    load_snap();
    print_graph();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q). Each SA point gets a new A-vertex joined to its q+1 lines,
# each SB line gets a new B-vertex joined to its q+1 points. Load limits keep all
# degrees <= d. Order is 2(q^2+q+1) + |SA| + |SB|.
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


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

C_FRACTION = 0.8      # share of time_limit allowed for the whole C run
C_MARGIN = 4.0        # seconds reserved for compilation and Python overhead


def _c_grow(d, D, seed, graph, budget):
    """Run the C annealer from `graph`; return a validated (n, edges) or None."""
    n, edges = graph
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=(n, edges), timeout=budget + 10.0)
    n2, e2 = lib.parse_graph_text(out)
    if lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D == 3:
        # Bold path: anneal-grow from the best arc graph in C.
        if best_n < lib.moore_bound(d, D):
            elapsed = time.monotonic() - start
            budget = C_FRACTION * time_limit - elapsed - C_MARGIN
            if budget >= 1.0:
                try:
                    res = _c_grow(d, D, seed, best, budget)
                    if res is not None:
                        consider(res[0], res[1])
                except Exception:
                    pass
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # D >= 4: GQ baseline and voltage-lift annealing (parent behaviour).
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
