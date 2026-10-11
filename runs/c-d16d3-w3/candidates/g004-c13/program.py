import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
#
# Order is 2(q^2+q+1) + |SA| + |SB|. Diameter stays 3 for any SA, SB.
#
# New in this version: a C repair engine. It takes the best graph found so far,
# adds ONE vertex (on a random side, with no edges), and runs simulated
# annealing over edge moves (add, delete, or re-target an edge endpoint) with
# cost = number of ordered vertex pairs at distance > D. Bipartiteness and the
# degree cap are kept as invariants, so any zero-cost state is a valid graph.
# Each time the cost reaches zero, the engine keeps that graph and tries to add
# another vertex. The output is re-checked with lib.is_valid, and the Python
# best graph is the fallback.
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
#define WORDS 16
#define MAXE 32768
#define ITERS 60000

typedef uint64_t u64;

static int DEG = 3, DIAM = 3;
static int N = 0;
static int col[MAXN];
static int dg[MAXN];
static int nb[MAXN][MAXDEG];
static u64 bufA[MAXN][WORDS];
static u64 bufB[MAXN][WORDS];

static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pop64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v, x) with dist(v, x) > DIAM. Zero means valid. */
static long cost_eval(void) {
    int W = (N + 63) >> 6;
    u64 (*cur)[WORDS] = bufA;
    u64 (*nxt)[WORDS] = bufB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DIAM; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < dg[v]; k++) {
                const u64 *src = cur[nb[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        u64 (*t)[WORDS] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pop64(cur[v][w]);
        bad += N - c;
    }
    return bad;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < dg[u]; k++)
        if (nb[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    nb[u][dg[u]++] = v;
    nb[v][dg[v]++] = u;
}

static void del_half(int u, int v) {
    for (int k = 0; k < dg[u]; k++) {
        if (nb[u][k] == v) {
            nb[u][k] = nb[u][--dg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_half(u, v);
    del_half(v, u);
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int u = 0; u < N; u++) {
        for (int k = 0; k < dg[u]; k++) {
            int v = nb[u][k];
            if (u < v && bestM < MAXE) {
                bestU[bestM] = u;
                bestV[bestM] = v;
                bestM++;
            }
        }
    }
}

static void rebuild_from_best(void) {
    for (int v = 0; v < MAXN; v++) dg[v] = 0;
    N = bestN;
    for (int i = 0; i < bestM; i++) add_edge(bestU[i], bestV[i]);
}

/* Simulated annealing on edges with the current N fixed. Returns final cost. */
static long anneal(long iters, double T0, double T1, double t_stop) {
    long cur = cost_eval();
    if (cur == 0) return 0;
    int NEW = N - 1;
    double lr = log(T1 / T0);
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && elapsed() > t_stop) break;
        double T = T0 * exp(lr * (double)it / (double)iters);
        int r = rndint(100);
        int kind, u, w = -1, w2 = -1;
        if (r < 35) {
            kind = 0;
            u = (rndint(10) < 3) ? NEW : rndint(N);
            w = rndint(N);
            if (u == w || col[u] == col[w]) continue;
            if (dg[u] >= DEG || dg[w] >= DEG || has_edge(u, w)) continue;
            add_edge(u, w);
        } else if (r < 60) {
            kind = 1;
            u = rndint(N);
            if (dg[u] == 0) continue;
            w = nb[u][rndint(dg[u])];
            del_edge(u, w);
        } else {
            kind = 2;
            u = (rndint(10) < 3) ? NEW : rndint(N);
            if (dg[u] == 0) continue;
            w = nb[u][rndint(dg[u])];
            w2 = rndint(N);
            if (w2 == u || w2 == w || col[w2] == col[u]) continue;
            if (dg[w2] >= DEG || has_edge(u, w2)) continue;
            del_edge(u, w);
            add_edge(u, w2);
        }
        long nc = cost_eval();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            if (kind == 0) {
                del_edge(u, w);
            } else if (kind == 1) {
                add_edge(u, w);
            } else {
                del_edge(u, w2);
                add_edge(u, w);
            }
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    if (DEG > MAXDEG) DEG = MAXDEG;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n > MAXN - 64 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < MAXN; v++) dg[v] = 0;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; continue; }
        if (dg[u] >= DEG || dg[v] >= DEG || has_edge(u, v)) { ok = 0; continue; }
        add_edge(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < n; v++) col[v] = -1;
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < dg[u]; k++) {
                int v = nb[u][k];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    double t_stop = budget * 0.92;
    while (elapsed() < t_stop && bestN < MAXN - 1) {
        rebuild_from_best();
        int nv = N;
        N++;
        col[nv] = rndint(2);
        dg[nv] = 0;
        long c = anneal(ITERS, 1.5, 0.12, t_stop);
        if (c == 0) save_best();
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Helpers for the arc-extension family (from the parent).
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


def _local_side(m, s, nbr, S0, rng, deadline, iters=6000):
    """Plateau local search on a feasible set S0. Returns the largest feasible set seen."""
    if s < 1:
        return list(S0)
    inS = [False] * m
    load = [0] * m
    S = list(S0)
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            load[t] += 1
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        over = {t for t in nbr[x] if load[t] >= s}
        if not over:
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
            if len(S) > len(best):
                best = list(S)
            continue
        cand = [y for y in S if any(t in over for t in nbr[y])]
        if not cand:
            continue
        y = rng.choice(cand)
        for t in nbr[y]:
            load[t] -= 1
        if all(load[t] < s for t in nbr[x]):
            S.remove(y)
            inS[y] = False
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
        else:
            for t in nbr[y]:
                load[t] += 1
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

        SA = _local_side(m, s, point_lines, SA, rng, deadline)
        SB = _local_side(m, s, line_points, SB, rng, deadline)

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
# Simulated annealing over bi-Cayley voltage lifts (parent, used for D >= 4).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Construction phase, limited so the C repair engine gets most of the time.
    pre_deadline = t0 + (0.3 if D >= 4 else 0.2) * time_limit

    if D >= 3:
        cands = _arc_extensions(d, pre_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < pre_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 4:
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < pre_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, pre_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C repair stage: add vertices to the best graph by annealing edges.
    # Skip when the Moore bound already rules out a larger graph.
    if D >= 2 and best_n < lib.moore_bound(d, D):
        remaining = time_limit * 0.88 - (time.monotonic() - t0) - 1.0
        if remaining >= 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining * 0.9, 2)],
                                 stdin_graph=best, timeout=remaining)
                n_c, e_c = lib.parse_graph_text(text)
                if n_c > 0:
                    consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
