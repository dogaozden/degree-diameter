import itertools
import math
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
#define MAXDEG 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2)

/* Grow-and-repair search: keep a valid graph (every pair within distance Drad,
   max degree dmax, bipartite with fixed sides). Repeatedly append one vertex
   on a random side and anneal edge moves (add / rewire / remove) to drive the
   number of pairs at distance > Drad to zero. On success the grown graph becomes
   the new base; on failure we restore the base and retry. */

static int n, dmax, Drad, nw;
static int lastv = -1;
static int deg[MAXN];
static int adjl[MAXN][MAXDEG];
static unsigned char adjm[MAXN][MAXN];
static int side[MAXN];
static int sq[MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int best_n = 0, best_m = 0;
static int best_e[MAXE][2];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > Drad. Zero means valid. */
static long long eval_cost(void) {
    uint64_t (*R)[MAXW] = bufA;
    uint64_t (*S)[MAXW] = bufB;
    nw = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) R[v][w] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < Drad; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) S[v][w] = R[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = R[adjl[v][k]];
                for (int w = 0; w < nw; w++) S[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = R;
        R = S;
        S = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(R[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void rm_from(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adjl[a][k] == b) {
            adjl[a][k] = adjl[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    adjm[a][b] = 1;
    adjm[b][a] = 1;
    adjl[a][deg[a]++] = b;
    adjl[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    adjm[a][b] = 0;
    adjm[b][a] = 0;
    rm_from(a, b);
    rm_from(b, a);
}

static int compute_sides(void) {
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        sq[t++] = s;
        while (h < t) {
            int u = sq[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adjl[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    sq[t++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void clear_graph(void) {
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        memset(adjm[v], 0, (size_t)n);
    }
}

static void save_best(void) {
    best_n = n;
    best_m = 0;
    for (int u = 0; u < n; u++) {
        for (int k = 0; k < deg[u]; k++) {
            int v = adjl[u][k];
            if (u < v && best_m < MAXE) {
                best_e[best_m][0] = u;
                best_e[best_m][1] = v;
                best_m++;
            }
        }
    }
}

static void restore_best(void) {
    clear_graph();
    n = best_n;
    for (int i = 0; i < best_m; i++) add_edge(best_e[i][0], best_e[i][1]);
    lastv = -1;
}

static int pick_vertex(void) {
    if (lastv >= 0 && rndint(3) == 0) return lastv;
    return rndint(n);
}

static long long anneal(long iters, double T0, double T1, clock_t deadline) {
    long long cost = eval_cost();
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && clock() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int type = rndint(10);
        int x = -1, y = -1, z = -1, mt = -1;
        if (type < 6) {
            x = pick_vertex();
            if (deg[x] >= dmax) continue;
            for (int tries = 0; tries < 30 && y < 0; tries++) {
                int b = rndint(n);
                if (side[b] != side[x] && deg[b] < dmax && !adjm[x][b]) y = b;
            }
            if (y < 0) continue;
            add_edge(x, y);
            mt = 0;
        } else if (type < 9) {
            x = pick_vertex();
            if (deg[x] == 0) continue;
            y = adjl[x][rndint(deg[x])];
            z = rndint(n);
            if (z == y || side[z] != side[y] || deg[z] >= dmax || adjm[x][z]) continue;
            del_edge(x, y);
            add_edge(x, z);
            mt = 1;
        } else {
            x = pick_vertex();
            if (deg[x] == 0) continue;
            y = adjl[x][rndint(deg[x])];
            del_edge(x, y);
            mt = 2;
        }
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            if (mt == 0) {
                del_edge(x, y);
            } else if (mt == 1) {
                del_edge(x, z);
                add_edge(x, y);
            } else {
                add_edge(x, y);
            }
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    clock_t t0 = clock();
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    dmax = atoi(argv[1]);
    Drad = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double budget = atof(argv[4]);
    clock_t deadline = t0 + (clock_t)(budget * CLOCKS_PER_SEC);

    int N0 = 0, M0 = 0;
    if (dmax < 1 || dmax > MAXDEG || Drad < 1) {
        printf("0 0\n");
        return 0;
    }
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (adjm[u][v] || deg[u] >= dmax || deg[v] >= dmax) continue;
        add_edge(u, v);
    }
    if (!compute_sides()) {
        printf("0 0\n");
        return 0;
    }

    lastv = -1;
    if (anneal(300000L, 2.0, 0.05, deadline) == 0) save_best();

    while (best_n > 0 && best_n < MAXN - 2 && clock() < deadline) {
        restore_best();
        n++;
        lastv = n - 1;
        deg[lastv] = 0;
        for (int i = 0; i < n; i++) {
            adjm[i][lastv] = 0;
            adjm[lastv][i] = 0;
        }
        side[lastv] = rndint(2);
        if (anneal(20000L, 1.0, 0.05, deadline) == 0) save_best();
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_e[i][0], best_e[i][1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add an A-vertex for each point
# in SA (joined to the lines through it, each line holds <= s of them) and a
# B-vertex for each line in SB (joined to its points, each point on <= s of them).
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
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
    py_deadline = start + 0.3 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for n_c, e_c in _arc_extensions(d, py_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < py_deadline:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, py_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C grow-and-repair stage: start from the best valid graph, try to add vertices.
    if best[0] < lib.moore_bound(d, D) and 2 <= d <= 60 and time_limit >= 3:
        remaining = 0.9 * time_limit - (time.monotonic() - start) - 0.5
        if remaining > 1.0:
            budget = 0.85 * remaining
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                                stdin_graph=best, timeout=remaining)
                n_c, e_c = lib.parse_graph_text(out)
                if n_c > 0:
                    consider(n_c, e_c)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
