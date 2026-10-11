import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates, plus random
# cross-edge perturbation. Every intermediate graph is valid, because
#   * a new vertex w on side s joined to N (opposite side, deg < d) keeps
#     every distance between old vertices, and reaches x within D whenever
#     x lies in the (D-1)-ball of some u in N;
#   * adding a cross edge between opposite sides keeps bipartiteness and
#     can only shorten distances.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 128

static int n, d, D;
static int deg[MAXN];
static int adjv[MAXN][MAXD];
static int side[MAXN];
static int nw;
static uint64_t ball[MAXN][MAXW];
static uint64_t tmpb[MAXN][MAXW];
static uint64_t fullm[MAXW];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adjv[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adjv[u][deg[u]++] = v;
    adjv[v][deg[v]++] = u;
}

static void set_full(void) {
    memset(fullm, 0, sizeof fullm);
    for (int v = 0; v < n; v++)
        fullm[v >> 6] |= 1ULL << (v & 63);
}

static void compute_balls(void) {
    int R = D - 1;
    for (int v = 0; v < n; v++) {
        memset(ball[v], 0, sizeof(uint64_t) * nw);
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(tmpb[v], ball[v], sizeof(uint64_t) * nw);
            for (int i = 0; i < deg[v]; i++) {
                int u = adjv[v][i];
                for (int w = 0; w < nw; w++)
                    tmpb[v][w] |= ball[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            memcpy(ball[v], tmpb[v], sizeof(uint64_t) * nw);
    }
}

static int try_insert(int s, int *chosen, int *nch) {
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (side[v] != s && deg[v] < d)
            cand[nc++] = v;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint64_t)(i + 1));
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(uint64_t) * nw);
    int cnt = 0;
    while (cnt < d) {
        int covered = 1;
        for (int w = 0; w < nw; w++)
            if ((cov[w] & fullm[w]) != fullm[w]) { covered = 0; break; }
        if (covered) break;
        int best = 0, bi = -1;
        for (int i = 0; i < nc; i++) {
            int v = cand[i];
            int g = 0;
            for (int w = 0; w < nw; w++)
                g += __builtin_popcountll(ball[v][w] & ~cov[w]);
            if (g > best) { best = g; bi = i; }
        }
        if (bi < 0) break;
        int v = cand[bi];
        chosen[cnt++] = v;
        for (int w = 0; w < nw; w++)
            cov[w] |= ball[v][w];
        cand[bi] = cand[--nc];
    }
    *nch = cnt;
    for (int w = 0; w < nw; w++)
        if ((cov[w] & fullm[w]) != fullm[w]) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    if (d > MAXD) d = MAXD;
    uint64_t seed = (uint64_t)atoll(argv[3]);
    rs ^= seed * 2654435761ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    double deadline = now() + tl;

    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 1 || n > MAXN - 200 || m < 0) { printf("0 0\n"); return 0; }

    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("0 0\n"); return 0; }
        if (has_edge(u, v) || deg[u] >= d || deg[v] >= d) { printf("0 0\n"); return 0; }
        add_edge(u, v);
    }

    /* 2-colour the input; any odd cycle means we cannot safely extend it. */
    int *col = malloc(sizeof(int) * n);
    int *queue = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int u = queue[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adjv[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    queue[tail++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < n; i++) side[i] = col[i];
    free(col);
    free(queue);

    int *chosen = malloc(sizeof(int) * MAXD);
    int fails = 0;
    if (D >= 2) {
        while (now() < deadline && n < MAXN - 2) {
            nw = (n + 63) / 64;
            set_full();
            compute_balls();
            int done = 0;
            int first = (int)(rnd() & 1ULL);
            for (int si = 0; si < 2 && !done; si++) {
                int s = (si == 0) ? first : 1 - first;
                for (int at = 0; at < 3 && !done; at++) {
                    int nch = 0;
                    if (try_insert(s, chosen, &nch)) {
                        int w = n;
                        n++;
                        deg[w] = 0;
                        side[w] = s;
                        for (int i = 0; i < nch; i++)
                            add_edge(w, chosen[i]);
                        done = 1;
                    }
                }
            }
            if (done) {
                fails = 0;
                continue;
            }
            /* No insertion possible: add a random spare cross edge. */
            int added = 0;
            for (int tries = 0; tries < 60 && !added; tries++) {
                int u = (int)(rnd() % (uint64_t)n);
                int v = (int)(rnd() % (uint64_t)n);
                if (side[u] == side[v] || deg[u] >= d || deg[v] >= d || has_edge(u, v))
                    continue;
                add_edge(u, v);
                added = 1;
            }
            fails++;
            if (!added && fails > 50) break;
            if (fails > 20000) break;
        }
    }

    int E = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (u < adjv[u][i]) E++;
    printf("%d %d\n", n, E);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (u < adjv[u][i])
                printf("%d %d\n", u, adjv[u][i]);
    free(chosen);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Every old vertex
# has degree q+1, so spare capacity is s = d - q - 1.
#   A-side: a point set SA; each P in SA gets a new vertex on all lines through P.
#           Every line must contain <= s points of SA.
#   B-side: a line set SB; each j in SB gets a new vertex on all points of j.
#           Every point must lie on <= s lines of SB.
# The sides are independent, so SA and SB are chosen separately.
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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose x so that every target is hit by <= s chosen elements."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline) if s >= 1 else []
        SB = _greedy_side(m, s, line_points, rng, 40, deadline) if s >= 1 else []
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
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
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
    start = time.monotonic()
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

    def c_augment(n, e, until):
        """Run the C insertion engine on (n, e) until the given monotonic time. None on failure."""
        budget = until - time.monotonic()
        if budget < 0.5 or d > 100:
            return None
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed % 1000003 + 1, round(budget, 2)],
                            stdin_graph=(n, e), timeout=budget + min(3.0, 0.1 * time_limit))
            return lib.parse_graph_text(out)
        except Exception:
            return None

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            res = c_augment(arcs[0][0], arcs[0][1], start + 0.30 * time_limit)
            if res is not None:
                consider(*res)

    # Generalized quadrangle baseline (diameter 4) and voltage-lift search for D >= 4.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        search_end = start + 0.60 * time_limit
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Final greedy insertion in C on the best valid graph found so far.
    res = c_augment(best[0], best[1], start + 0.90 * time_limit)
    if res is not None:
        consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
