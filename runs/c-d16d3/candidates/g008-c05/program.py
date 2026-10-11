import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Combined program.
#
# 1. Arc-extended projective plane graphs (diameter 3). Start from PG(2, q)
#    incidence. Choose SA (points, each adds an A-vertex on its q+1 lines) and
#    SB (lines, each adds a B-vertex on its q+1 points) with spare capacity
#    s = d - q - 1. For d = 16 this reproduces the record 394 via q = 13 and
#    conics.
# 2. Generalized quadrangle W(q) baseline for D = 4.
# 3. Simulated annealing over group voltage lifts for D >= 4.
# 4. C engine: starting from the best graph, it keeps the graph valid at all
#    times and tries (a) greedy vertex insertion whose neighbourhood covers all
#    vertices within D-1 of some neighbour (this is an exact validity test for
#    the new vertex), (b) adding spare cross edges, and (c) removing a random
#    edge when the graph stays valid, which frees capacity for insertions.
#    Every output is re-checked by lib.is_valid; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 40
#define MAXLEV 12
#define MAXM (MAXN * MAXDEG / 2)

typedef uint64_t u64;

static int n, dmax, diam, words, dirty = 1;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static u64 lev[MAXLEV + 1][MAXN][MAXW];
static u64 rs = 1;
static int eu[MAXM], ev[MAXM];

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) {
    return (int)(rnd() % (u64)k);
}

static int pop64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void drop_from(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    drop_from(a, b);
    drop_from(b, a);
}

/* lev[k][v] = bitset of vertices within distance k of v. */
static void compute_levels(void) {
    int k, v, i, w, u;
    words = (n + 63) >> 6;
    for (v = 0; v < n; v++) {
        for (w = 0; w < words; w++) lev[0][v][w] = 0;
        lev[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (k = 0; k < diam; k++) {
        for (v = 0; v < n; v++) {
            for (w = 0; w < words; w++) lev[k + 1][v][w] = lev[k][v][w];
            for (i = 0; i < deg[v]; i++) {
                u = adj[v][i];
                for (w = 0; w < words; w++) lev[k + 1][v][w] |= lev[k][u][w];
            }
        }
    }
    dirty = 0;
}

static long bad_count(void) {
    long bad = 0;
    int v, w, c;
    for (v = 0; v < n; v++) {
        c = 0;
        for (w = 0; w < words; w++) c += pop64(lev[diam][v][w]);
        bad += n - c;
    }
    return bad;
}

static int color_graph(void) {
    static int stack[MAXN];
    int s, v, i, u, top;
    for (v = 0; v < n; v++) col[v] = -1;
    for (s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        top = 0;
        stack[top++] = s;
        while (top > 0) {
            v = stack[--top];
            for (i = 0; i < deg[v]; i++) {
                u = adj[v][i];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    stack[top++] = u;
                } else if (col[u] == col[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int covers_all(const u64 *cov, const u64 *full) {
    int w;
    for (w = 0; w < words; w++)
        if ((cov[w] & full[w]) != full[w]) return 0;
    return 1;
}

/* Insert a new vertex of colour c whose neighbours (colour 1-c, spare degree)
   cover every vertex within distance diam-1 of some neighbour. Exact validity. */
static int try_insert(int c) {
    static int cand[MAXN], used[MAXN], chosen[MAXDEG];
    static u64 cov[MAXW], full[MAXW];
    int nc = 0, nch = 0, r = diam - 1, v, i, j, w, u, best, bestg, g, ok;
    for (v = 0; v < n; v++) {
        used[v] = 0;
        if (col[v] == 1 - c && deg[v] < dmax) cand[nc++] = v;
    }
    if (nc == 0) return 0;
    for (i = nc - 1; i > 0; i--) {
        j = rndint(i + 1);
        v = cand[i];
        cand[i] = cand[j];
        cand[j] = v;
    }
    for (w = 0; w < words; w++) {
        cov[w] = 0;
        full[w] = 0;
    }
    for (v = 0; v < n; v++) full[v >> 6] |= 1ULL << (v & 63);
    ok = 0;
    while (nch < dmax) {
        best = -1;
        bestg = 0;
        for (i = 0; i < nc; i++) {
            u = cand[i];
            if (used[u]) continue;
            g = 0;
            for (w = 0; w < words; w++) g += pop64(lev[r][u][w] & ~cov[w]);
            if (g > bestg) {
                bestg = g;
                best = u;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (w = 0; w < words; w++) cov[w] |= lev[r][best][w];
        if (covers_all(cov, full)) {
            ok = 1;
            break;
        }
    }
    if (!ok) return 0;
    col[n] = c;
    deg[n] = 0;
    for (i = 0; i < nch; i++) add_edge(chosen[i], n);
    n++;
    return 1;
}

/* Add a spare cross edge. Distances only shrink, so validity is kept. */
static int try_add_edge(void) {
    int t, a, b;
    for (t = 0; t < 60; t++) {
        a = rndint(n);
        b = rndint(n);
        if (col[a] == col[b] || deg[a] >= dmax || deg[b] >= dmax) continue;
        if (has_edge(a, b)) continue;
        add_edge(a, b);
        return 1;
    }
    return 0;
}

/* Remove a random edge, keep the removal only if the graph stays valid. */
static void try_remove(void) {
    int t, a = -1, b;
    for (t = 0; t < 30; t++) {
        a = rndint(n);
        if (deg[a] > 0) break;
    }
    if (a < 0 || deg[a] == 0) {
        dirty = 1;
        return;
    }
    b = adj[a][rndint(deg[a])];
    del_edge(a, b);
    compute_levels();
    if (bad_count() != 0) add_edge(a, b);
    dirty = 1;
}

static void print_input(int nn, int m) {
    int i;
    printf("%d %d\n", nn, m);
    for (i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    int d, D, seed, m, i, a, t, nn, E, ok, ins;
    double budget, el;
    clock_t start;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed = atoi(argv[3]);
    budget = atof(argv[4]);
    if (scanf("%d %d", &nn, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (m < 0 || m > MAXM || nn < 0 || nn > MAXN / 2) {
        printf("0 0\n");
        return 0;
    }
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    rs = (u64)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    dmax = d;
    diam = D;
    n = nn;
    for (i = 0; i < n; i++) deg[i] = 0;

    ok = (n >= 2 && d >= 1 && d < MAXDEG - 1 && D >= 2 && D <= MAXLEV);
    if (ok) {
        for (i = 0; i < m && ok; i++) {
            a = eu[i];
            t = ev[i];
            if (a < 0 || a >= n || t < 0 || t >= n || a == t) ok = 0;
            else if (has_edge(a, t) || deg[a] >= dmax || deg[t] >= dmax) ok = 0;
            else add_edge(a, t);
        }
    }
    if (ok) ok = color_graph();
    if (ok) {
        compute_levels();
        ok = (bad_count() == 0);
    }
    if (!ok) {
        print_input(nn, m);
        return 0;
    }

    start = clock();
    for (;;) {
        el = (double)(clock() - start) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        if (dirty) compute_levels();
        ins = 0;
        for (t = 0; t < 6 && !ins && n < MAXN - 2; t++)
            if (try_insert(rndint(2))) ins = 1;
        if (ins) {
            dirty = 1;
            continue;
        }
        if (rndint(10) < 6) {
            if (try_add_edge()) dirty = 1;
        } else {
            try_remove();
        }
    }

    if (dirty) compute_levels();
    if (bad_count() != 0) {
        print_input(nn, m);
        return 0;
    }
    E = 0;
    for (a = 0; a < n; a++) E += deg[a];
    E /= 2;
    printf("%d %d\n", n, E);
    for (a = 0; a < n; a++)
        for (i = 0; i < deg[a]; i++)
            if (adj[a][i] > a) printf("%d %d\n", a, adj[a][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
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
# Simulated annealing over bi-Cayley voltage lifts (D >= 4).
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

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T = float(time_limit)
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

    # Arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        arcs = _arc_extensions(d, t0 + 0.12 * T, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t0 + 0.2 * T:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for D >= 4.
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        end = t0 + 0.4 * T
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C search: vertex insertion, spare edges and validity-preserving edge removal.
    budget = t0 + 0.8 * T - time.monotonic()
    if D >= 3 and budget >= 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=best,
                            timeout=budget + min(5.0, 0.1 * T) + 1.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
