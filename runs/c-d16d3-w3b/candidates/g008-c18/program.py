import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: insertion plus annealing on bipartite graphs (diameter D).
#
# State: a valid graph (all pairs within D) with a fixed 2-colouring.
#  1. Insertion: a new vertex on side s joined to opposite-side vertices whose
#     (D-1)-balls cover every vertex. Old distances never grow, so validity holds.
#  2. If insertion fails, annealing moves (rewire / add / remove cross edges) with
#     cost = number of unordered pairs at distance > D. A zero-cost state is saved
#     and insertion is retried.
#  3. After RESTART non-zero steps, the best saved graph is reloaded.
# The best valid graph seen is printed. Python re-checks it with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXWD (MAXN / 64)
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)

typedef uint64_t Row[MAXWD];

static int n, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static unsigned char am[MAXN][MAXN];
static Row bufA[MAXN], bufB[MAXN];
static uint64_t rs = 88172645463325252ULL;
static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];
static int have_best = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    am[u][v] = 1; am[v][u] = 1;
}

static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) { adj[u][i] = adj[u][deg[u] - 1]; deg[u]--; return; }
    }
}

static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    am[u][v] = 0; am[v][u] = 0;
}

/* Rows of R-balls: bit w of row v is set iff dist(v, w) <= R. Result is valid until the next call. */
static Row *ball(int R) {
    int Wn = (n + 63) >> 6;
    Row *cur = bufA, *nx = bufB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(nx[v], cur[v], sizeof(uint64_t) * (size_t)Wn);
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < Wn; w++) nx[v][w] |= cur[u][w];
            }
        }
        Row *t = cur; cur = nx; nx = t;
    }
    return cur;
}

static long bad_pairs(void) {
    Row *B = ball(D);
    int Wn = (n + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < Wn; w++) c += popc(B[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int check_bip(void) {
    static int qu[MAXN];
    static int vis[MAXN];
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        vis[s] = 1; col[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (!vis[v]) { vis[v] = 1; col[v] = 1 - col[u]; qu[t++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    return 1;
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (v > u && m < MAXE) { bestU[m] = u; bestV[m] = v; m++; }
        }
    }
    bestN = n; bestM = m;
}

static void load_best(void) {
    n = bestN;
    for (int v = 0; v < n; v++) { deg[v] = 0; memset(am[v], 0, MAXN); }
    for (int i = 0; i < bestM; i++) add_edge(bestU[i], bestV[i]);
}

/* Insert a vertex on the given side covering all vertices within D of it. Requires a valid graph. */
static int try_insert(int side) {
    static int cand[MAXN];
    static int used[MAXN];
    static int chosen[MAXD];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < n; i++) used[i] = 0;
    Row *B = ball(D - 1);
    int Wn = (n + 63) >> 6;
    Row cov;
    memset(cov, 0, sizeof(cov));
    int nch = 0;
    for (;;) {
        int full = 1;
        for (int w = 0; w < Wn; w++) {
            uint64_t want = (w < Wn - 1 || (n & 63) == 0) ? ~0ULL : ((1ULL << (n & 63)) - 1);
            if ((cov[w] & want) != want) { full = 0; break; }
        }
        if (full) break;
        if (nch >= d) return 0;
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < Wn; w++) g += popc(B[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) return 0;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < Wn; w++) cov[w] |= B[best][w];
    }
    if (n >= MAXN - 1) return 0;
    int x = n;
    n++;
    memset(am[x], 0, MAXN);
    for (int w = 0; w < x; w++) am[w][x] = 0;
    deg[x] = 0;
    col[x] = side;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], x);
    return 1;
}

/* a-b becomes a-w, with w on the same side as b. */
static int mv_rewire(int *a, int *b, int *w) {
    int x = -1;
    for (int t = 0; t < 64 && x < 0; t++) {
        int c = rndi(n);
        if (deg[c] > 0) x = c;
    }
    if (x < 0) return 0;
    int y = adj[x][rndi(deg[x])];
    int z = -1;
    for (int t = 0; t < 64; t++) {
        int c = rndi(n);
        if (c != y && col[c] == col[y] && deg[c] < d && !am[x][c]) { z = c; break; }
    }
    if (z < 0) return 0;
    del_edge(x, y);
    add_edge(x, z);
    *a = x; *b = y; *w = z;
    return 1;
}

static int mv_add(int *a, int *b) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) {
        int c = rndi(n);
        if (deg[c] < d) { x = c; break; }
    }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rndi(n);
        if (col[c] != col[x] && deg[c] < d && !am[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *a = x; *b = y;
    return 1;
}

static int mv_remove(int *a, int *b) {
    int x = -1;
    for (int t = 0; t < 64 && x < 0; t++) {
        int c = rndi(n);
        if (deg[c] > 0) x = c;
    }
    if (x < 0) return 0;
    int y = adj[x][rndi(deg[x])];
    del_edge(x, y);
    *a = x; *b = y;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    clock_t t0 = clock();

    int N0 = 0, M0 = 0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 2 || d < 1 || d > MAXD ||
        D < 1 || M0 < 0) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    for (int v = 0; v < n; v++) { deg[v] = 0; memset(am[v], 0, MAXN); }
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (am[u][v] || deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }
    if (!check_bip()) { printf("0 0\n"); return 0; }

    long cur = bad_pairs();
    long it = 0, since = 0;
    const long RESTART = 4000;
    if (cur == 0) { save_best(); have_best = 1; }

    for (;;) {
        if ((it & 31) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        if (cur == 0) {
            save_best();
            have_best = 1;
            int s0 = rndi(2);
            if (try_insert(s0) || try_insert(1 - s0)) { since = 0; continue; }
        }
        double T = 0.15 + 0.9 * (1.0 - (double)since / (double)RESTART);
        int kind, a = 0, b = 0, w = 0, ok;
        int r = rndi(100);
        if (r < 55) { kind = 0; ok = mv_rewire(&a, &b, &w); }
        else if (r < 90) { kind = 1; ok = mv_add(&a, &b); }
        else { kind = 2; ok = mv_remove(&a, &b); }
        if (!ok) { since++; continue; }

        long nb = bad_pairs();
        long delta = nb - cur;
        int acc = (delta <= 0) || (rnd01() < exp(-(double)delta / T));
        if (acc) {
            cur = nb;
        } else {
            if (kind == 0) { del_edge(a, w); add_edge(a, b); }
            else if (kind == 1) { del_edge(a, b); }
            else { add_edge(a, b); }
        }
        since++;
        if (cur == 0) {
            since = 0;
        } else if (since >= RESTART && have_best) {
            load_best();
            cur = 0;
            since = 0;
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


def _c_improve(graph, d, D, seed, budget):
    """Run the C engine from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0 or d > 64 or graph[0] > 900:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 4.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each vertex has
# degree q+1, so spare s = d - q - 1. Choose SA (points) with every line holding
# <= s points of SA, and SB (lines) with every point on <= s lines of SB. Add an
# A-vertex per SA point joined to its q+1 lines, and a B-vertex per SB line joined
# to its q+1 points. The two sets are optimized independently.
# ----------------------------------------------------------------------------

_LS_ITERS = 20000


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
    """Randomized greedy choice of elements so that every target is hit by <= s of them."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one A-vertex per SA point and one B-vertex per SB line."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d, best bound first."""
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
        m, edges, pl, lp, index, pts = _pg_data(q)
        SA = _greedy_side(m, s, pl, rng, 30, deadline)
        SB = _greedy_side(m, s, lp, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
                SB = cs
        SA = _local_search(m, s, pl, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, lp, SB, rng, deadline, _LS_ITERS)
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
    """W(q) for the largest prime power q <= min(d-1, 7), or None."""
    for q in range(min(d - 1, 7), 1, -1):
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
# Build. Time plan (fractions of time_limit):
#   D >= 3: arc-extended PG graphs until 0.25
#   D >= 4: GQ baseline, then annealed voltage lifts until 0.55
#   then:   C insertion/annealing from the best graph until ~0.82
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

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    end = start + 0.82 * time_limit - 1.5

    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0])[:3]:
            consider(g)

    if D >= 4:
        if time.monotonic() < start + 0.25 * time_limit:
            consider(_best_gq(d))
        anneal_end = start + 0.55 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            try:
                k = rng.choice(ks)
                base = best[0] // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
                if res is not None:
                    consider(res)
            except Exception:
                break

    budget = end - time.monotonic()
    if budget >= 1.0:
        consider(_c_improve(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
