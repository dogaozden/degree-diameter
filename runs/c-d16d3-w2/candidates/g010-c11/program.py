import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: ball-cover insertion plus local repair.
#
# State: a bipartite graph (fixed sides) with max degree d. bad = number of
# unordered pairs at distance > D. Valid states have bad == 0.
#
# Main loop, from a valid state:
#   1. Insertion: a new vertex w on side s joins a set of spare-degree vertices
#      on the other side whose (D-1)-balls cover every vertex. Then w is within
#      distance D of everything, and old distances never grow. Insert and repeat.
#   2. If no insertion is possible, run an episode: snapshot the state, apply a
#      few random kicks, then simulated annealing on bad (rewire/add/remove moves)
#      for a fixed number of steps. Keep the result if bad returns to 0,
#      otherwise restore the snapshot.
# The best valid graph seen is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define DCAP 64
#define MAXE (MAXN * DCAP)

typedef uint64_t Row[MAXW];

static int n, d, D, W;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static Row BX[MAXN], BY[MAXN];
static int snb[MAXN][DCAP];
static int sdeg[MAXN];
static int sn;
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0;
static int cur_bad;
static double TL;
static clock_t T0;
static uint64_t rs = 1;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }
static int time_up(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC > TL; }
static void setW(void) { W = (n + 63) >> 6; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

/* Bitsets of vertices within distance R. Returns BX or BY. */
static Row *balls(int R) {
    Row *cur = BX, *nxt = BY;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        Row *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

static int bad_pairs(void) {
    Row *r = balls(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(r[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) want = ~0ULL;
        else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

static int try_insert(int sw, Row *reach) {
    static int cand[MAXN];
    static int used[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (side[u] == 1 - sw && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[DCAP];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    if (n >= MAXN - 1) return 0;
    int w = n;
    n++;
    side[w] = sw;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static int move_rewire(int *ua, int *ub, int *uw) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) { int c = rint_(n); if (deg[c] > 0) a = c; }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    int w = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != b && side[c] == side[b] && deg[c] < d && !adjm[a][c]) { w = c; break; }
    }
    if (w < 0) return 0;
    del_edge(a, b);
    add_edge(a, w);
    *ua = a; *ub = b; *uw = w;
    return 1;
}

static int move_add(int *ua, int *ub) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) { int c = rint_(n); if (deg[c] < d) { x = c; break; } }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *ua = x; *ub = y;
    return 1;
}

static int move_remove(int *ua, int *ub) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) { int c = rint_(n); if (deg[c] > 0) a = c; }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    *ua = a; *ub = b;
    return 1;
}

/* One Metropolis step on bad. Returns 1 if accepted. */
static int sa_step(double T) {
    int kind, ua = 0, ub = 0, uw = 0, applied;
    int r = rint_(100);
    if (r < 55) { kind = 0; applied = move_rewire(&ua, &ub, &uw); }
    else if (r < 90) { kind = 1; applied = move_add(&ua, &ub); }
    else { kind = 2; applied = move_remove(&ua, &ub); }
    if (!applied) return 0;
    setW();
    int nbad = bad_pairs();
    int delta = nbad - cur_bad;
    if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
        cur_bad = nbad;
        return 1;
    }
    if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
    else if (kind == 1) { del_edge(ua, ub); }
    else { add_edge(ua, ub); }
    return 0;
}

static void snapshot(void) {
    sn = n;
    for (int u = 0; u < n; u++) {
        sdeg[u] = deg[u];
        for (int i = 0; i < deg[u]; i++) snb[u][i] = nb[u][i];
    }
}

static void restore(void) {
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++) adjm[u][nb[u][i]] = 0;
    n = sn;
    for (int u = 0; u < n; u++) {
        deg[u] = sdeg[u];
        for (int i = 0; i < deg[u]; i++) {
            nb[u][i] = snb[u][i];
            adjm[u][nb[u][i]] = 1;
        }
    }
    setW();
}

static void save_best(void) {
    if (n <= best_n) return;
    int m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u && m < MAXE) { bestU[m] = u; bestV[m] = nb[u][i]; m++; }
    best_n = n;
    best_m = m;
}

static void episode(void) {
    snapshot();
    int kicks = 1 + rint_(3);
    for (int k = 0; k < kicks; k++) {
        int ua = 0, ub = 0, uw = 0;
        int r = rint_(3);
        if (r == 0) move_rewire(&ua, &ub, &uw);
        else if (r == 1) move_add(&ua, &ub);
        else move_remove(&ua, &ub);
    }
    setW();
    cur_bad = bad_pairs();
    const int L = 300;
    for (int s = 0; s < L && cur_bad > 0 && !time_up(); s++) {
        double T = 0.5 * (1.0 - (double)s / L) + 0.05;
        sa_step(T);
    }
    if (cur_bad > 0) {
        restore();
        cur_bad = 0;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    T0 = clock();

    int N0 = 0, M0 = 0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || M0 < 0 || N0 > MAXN - 8 ||
        d < 1 || d > DCAP || D < 2) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    int *eu = malloc(sizeof(int) * (size_t)(M0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(M0 + 1));
    if (!eu || !ev) return 1;
    int ne = 0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        eu[ne] = u; ev[ne] = v; ne++;
    }
    for (int i = 0; i < ne; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || adjm[u][v]) continue;
        add_edge(u, v);
    }

    /* Two-colour the graph; isolated vertices get side 0. */
    static int queue[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    int bip = 1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (side[v] < 0) { side[v] = 1 - side[u]; queue[qt++] = v; }
                else if (side[v] == side[u]) bip = 0;
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }

    setW();
    cur_bad = bad_pairs();
    if (cur_bad == 0) save_best();
    while (cur_bad != 0 && !time_up()) sa_step(0.4);
    if (cur_bad != 0) { printf("0 0\n"); return 0; }
    save_best();

    while (!time_up()) {
        if (cur_bad != 0) { sa_step(0.3); continue; }
        save_best();
        setW();
        Row *reach = balls(D - 1);
        int first = rint_(2);
        int got = try_insert(first, reach);
        if (!got) got = try_insert(1 - first, reach);
        if (got) {
            setW();
            cur_bad = bad_pairs();
            continue;
        }
        episode();
    }
    if (cur_bad == 0) save_best();

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    free(eu);
    free(ev);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1), each vertex of
# degree q+1, spare s = d - q - 1.
# A-side: a set SA of points, each gets a new vertex joined to the q+1 lines
# through it. Every line may meet at most s points of SA.
# B-side: a set SB of lines, each gets a new vertex joined to the q+1 points on
# it. Every point may lie on at most s lines of SB.
# The two sides are independent. Arcs (conics) give the largest sets.
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
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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
# C engine driver
# ----------------------------------------------------------------------------

def _c_improve(graph, d, D, seed, budget):
    """Run the C repair/insertion engine from graph; return (n, edges) or None."""
    if budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Build
# Time plan (fractions of time_limit):
#   D = 3: arc-extended PG graphs, then C search for the rest (to 0.75).
#   D >= 4: GQ and voltage annealing up to 0.40, then C search (to 0.75).
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

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.12 * time_limit, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        end = t0 + 0.40 * time_limit
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    bound = lib.moore_bound(d, D)
    budget = t0 + 0.75 * time_limit - time.monotonic()
    if best[0] < bound and budget > 1.0:
        consider(_c_improve(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
