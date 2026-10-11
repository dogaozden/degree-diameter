import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing local search that grows a bipartite graph with max degree
# d and diameter D. It starts from the input graph, keeps the diameter cost at
# zero, and adds one vertex each time the cost reaches zero. Cost = number of
# unordered vertex pairs at distance > D, computed with bitset BFS. Moves are
# edge rewires (keep bipartiteness and degrees) and edge additions. The program
# prints the largest zero-cost graph it found, or the input if none is larger.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3000
#define WMAX ((MAXN + 63) / 64)

static int N, Dg, DIAM, W, CAP;
static int *deg, *adj, *side, *cand;
static uint64_t *RA, *RB;
static int *best_E, best_N = -1, best_m = 0;
static long long cur_cost;
static clock_t DL;
static unsigned char PC[65536];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    return PC[x & 0xffff] + PC[(x >> 16) & 0xffff] + PC[(x >> 32) & 0xffff] + PC[(x >> 48) & 0xffff];
}

static int is_adj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[(size_t)a * Dg + i] == b) return 1;
    return 0;
}

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[(size_t)a * Dg + i] == b) {
            adj[(size_t)a * Dg + i] = adj[(size_t)a * Dg + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    adj[(size_t)a * Dg + deg[a]++] = b;
    adj[(size_t)b * Dg + deg[b]++] = a;
}

static void del_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static long long cost_eval(void) {
    uint64_t *cur = RA, *nxt = RB;
    size_t tot_words = (size_t)N * W;
    memset(cur, 0, tot_words * sizeof(uint64_t));
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, (size_t)W * sizeof(uint64_t));
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s2 = cur + (size_t)adj[(size_t)v * Dg + i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(r[w]);
        tot += N - c;
    }
    return tot / 2;
}

static void snapshot(void) {
    best_N = N;
    best_m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[(size_t)v * Dg + i];
            if (v < u) {
                best_E[2 * best_m] = v;
                best_E[2 * best_m + 1] = u;
                best_m++;
            }
        }
    }
}

static int grow(void) {
    if (N >= CAP) return 0;
    int first = rndint(2);
    for (int tr = 0; tr < 2; tr++) {
        int sd = (tr == 0) ? first : 1 - first;
        int k = 0;
        for (int x = 0; x < N; x++) if (side[x] == 1 - sd && deg[x] < Dg) cand[k++] = x;
        if (k == 0) continue;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
        }
        int take = k < Dg ? k : Dg;
        int v = N;
        N++;
        side[v] = sd;
        deg[v] = 0;
        W = (N + 63) / 64;
        for (int i = 0; i < take; i++) add_edge(v, cand[i]);
        cur_cost = cost_eval();
        return 1;
    }
    return 0;
}

static void anneal(long long iters, double T0, double T1) {
    double lr = log(T1 / T0);
    for (long long it = 0; it < iters; it++) {
        if (cur_cost == 0) return;
        if ((it & 31) == 0 && clock() > DL) return;
        double T = T0 * exp(lr * (double)it / (double)iters);
        if (rndint(100) < 10) {
            int a = -1, b = -1;
            for (int t = 0; t < 60; t++) {
                int x = rndint(N), y = rndint(N);
                if (side[x] == side[y] || deg[x] >= Dg || deg[y] >= Dg || is_adj(x, y)) continue;
                a = x; b = y;
                break;
            }
            if (a < 0) continue;
            add_edge(a, b);
            cur_cost = cost_eval();
            continue;
        }
        int b = rndint(N);
        if (deg[b] == 0) continue;
        int a = adj[(size_t)b * Dg + rndint(deg[b])];
        int c = -1;
        for (int t = 0; t < 60; t++) {
            int x = rndint(N);
            if (x != b && side[x] == side[b] && deg[x] < Dg && !is_adj(a, x)) { c = x; break; }
        }
        if (c < 0) continue;
        del_edge(a, b);
        add_edge(a, c);
        long long nc = cost_eval();
        long long delta = nc - cur_cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur_cost = nc;
        } else {
            del_edge(a, c);
            add_edge(a, b);
        }
    }
}

static void print_input(int n0, int m0, int *ie) {
    if (n0 == 0) { printf("0 0\n"); return; }
    printf("%d %d\n", n0, m0);
    for (int i = 0; i < m0; i++) printf("%d %d\n", ie[2 * i], ie[2 * i + 1]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dg = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = (uint64_t)strtoull(argv[3], NULL, 10);
    rs ^= sd * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    for (int i = 1; i < 65536; i++) PC[i] = (unsigned char)(PC[i >> 1] + (i & 1));

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || n0 > MAXN || m0 < 0 || Dg < 1 || Dg > 256 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    int *ie = malloc(sizeof(int) * 2 * (size_t)(m0 + 1));
    int mm = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        ie[2 * mm] = u;
        ie[2 * mm + 1] = v;
        mm++;
    }
    m0 = mm;

    deg = calloc(MAXN, sizeof(int));
    side = calloc(MAXN, sizeof(int));
    adj = calloc((size_t)MAXN * Dg, sizeof(int));
    cand = calloc(MAXN, sizeof(int));
    RA = calloc((size_t)MAXN * WMAX, sizeof(uint64_t));
    RB = calloc((size_t)MAXN * WMAX, sizeof(uint64_t));
    best_E = calloc((size_t)MAXN * Dg * 2 + 4, sizeof(int));

    int ok = 1;
    if (n0 == 0) {
        N = 2;
        add_edge(0, 1);
        m0 = 0;
    } else {
        N = n0;
        for (int i = 0; i < m0 && ok; i++) {
            int u = ie[2 * i], v = ie[2 * i + 1];
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
            if (deg[u] >= Dg || deg[v] >= Dg || is_adj(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
    }
    if (!ok) { print_input(n0, m0, ie); return 0; }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N && ok; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        cand[t++] = s;
        while (h < t) {
            int u = cand[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[(size_t)u * Dg + i];
                if (side[w] < 0) { side[w] = 1 - side[u]; cand[t++] = w; }
                else if (side[w] == side[u]) { ok = 0; }
            }
        }
    }
    if (!ok) { print_input(n0, m0, ie); return 0; }

    double cb;
    if (Dg == 1) cb = 2;
    else if (Dg == 2) cb = 2.0 * DIAM;
    else {
        cb = 0;
        double p = 1;
        for (int i = 0; i < DIAM; i++) {
            cb += p;
            p *= (Dg - 1);
            if (p > 1e9) break;
        }
        cb *= 2;
    }
    CAP = (cb >= MAXN) ? MAXN : (int)cb;
    if (CAP < N) CAP = N;

    W = (N + 63) / 64;
    cur_cost = cost_eval();
    if (cur_cost == 0) snapshot();
    DL = clock() + (clock_t)(tl * CLOCKS_PER_SEC);

    double T0 = 5.0, T1 = 0.2;
    long long stage = 5000;
    while (clock() < DL) {
        if (cur_cost == 0) {
            snapshot();
            if (N >= CAP) break;
            if (!grow()) break;
            continue;
        }
        anneal(stage, T0, T1);
    }

    if (best_N < 0) {
        print_input(n0, m0, ie);
        return 0;
    }
    printf("%d %d\n", best_N, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_E[2 * i], best_E[2 * i + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Extra A-vertices attach to lines
# and extra B-vertices attach to points, with bounded loads per target.
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
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4 only).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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
    """Simulated annealing over voltages and per-layer B-assignments."""
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
# Build: best algebraic start, optional lift search for D >= 4, then C growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

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

    # Arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

        # Short lift search for larger diameters.
        rng = random.Random(seed)
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        lift_deadline = t0 + 0.3 * time_limit
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Main search: C annealing that grows the best valid graph found so far.
    remaining = t0 + 0.75 * time_limit - time.monotonic()
    budget = max(0.5, remaining)
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=time_limit * 0.9)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
