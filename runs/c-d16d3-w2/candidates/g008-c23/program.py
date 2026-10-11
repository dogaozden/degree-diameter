import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy ball-cover insertion, then simulated annealing.
#
# Phase 1 (greedy insertion): with R = D-1, a new vertex w joined to a set N of
# opposite-colour vertices reaches every old vertex x lying in the R-ball of
# some u in N, within distance D. Old distances never grow, so validity is kept.
# If no insertion succeeds, a random spare cross edge is added to change the
# spare-degree pattern.
#
# Phase 2 (annealing): energy E = bad - BETA * nalive, where bad counts unordered
# alive pairs at distance > D. Moves: add a vertex (with a random partner loss),
# remove a vertex, or a degree-preserving double-edge swap. The best state with
# bad == 0 is printed, relabelled to 0..n-1.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int alive[MAXN];
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int nalive;
    int cap;
} State;

static State cur, bak, best;
static int have_best = 0;
static int d, D;
static int W = 1;
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t amask[MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) if (cur.adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    cur.adj[u][cur.deg[u]++] = v;
    cur.adj[v][cur.deg[v]++] = u;
}

static void del_one(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) {
        if (cur.adj[u][i] == v) {
            cur.adj[u][i] = cur.adj[u][cur.deg[u] - 1];
            cur.deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

static void compute_balls(int R) {
    W = (cur.cap + 63) >> 6;
    if (W < 1) W = 1;
    for (int v = 0; v < cur.cap; v++) {
        if (!cur.alive[v]) continue;
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < cur.cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < cur.deg[v]; i++) {
                int u = cur.adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < cur.cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
        }
    }
}

static long long compute_bad(void) {
    compute_balls(D);
    long long tot = 0;
    for (int v = 0; v < cur.cap; v++) {
        if (!cur.alive[v]) continue;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(reach[v][w]);
        tot += cur.nalive - pc;
    }
    return tot / 2;
}

static void build_mask(void) {
    for (int w = 0; w < W; w++) amask[w] = 0;
    for (int v = 0; v < cur.cap; v++)
        if (cur.alive[v]) amask[v >> 6] |= 1ULL << (v & 63);
}

static int covered(const uint64_t *cov) {
    for (int w = 0; w < W; w++)
        if ((cov[w] & amask[w]) != amask[w]) return 0;
    return 1;
}

static int try_insert(int side) {
    static int cand[MAXN];
    static int used[MAXN];
    int nc = 0;
    for (int u = 0; u < cur.cap; u++) {
        used[u] = 0;
        if (cur.alive[u] && cur.col[u] == 1 - side && cur.deg[u] < d) cand[nc++] = u;
    }
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covered(cov)) {
        int bu = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc64(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; bu = u; }
        }
        if (bu < 0) break;
        used[bu] = 1;
        chosen[nch++] = bu;
        for (int w = 0; w < W; w++) cov[w] |= reach[bu][w];
    }
    if (!covered(cov)) return 0;
    int w = -1;
    for (int i = 0; i < MAXN; i++) if (!cur.alive[i]) { w = i; break; }
    if (w < 0) return 0;
    cur.alive[w] = 1;
    cur.col[w] = side;
    cur.deg[w] = 0;
    cur.nalive++;
    if (w + 1 > cur.cap) cur.cap = w + 1;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static void phase1(clock_t t0, double until) {
    int fails = 0;
    while (fails < 200 && elapsed(t0) < until) {
        compute_balls(D - 1);
        build_mask();
        int sides[2] = {0, 1};
        if (rndi(2)) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = rndi(cur.cap);
            int v = rndi(cur.cap);
            if (u == v || !cur.alive[u] || !cur.alive[v]) continue;
            if (cur.col[u] == cur.col[v]) continue;
            if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            break;
        }
    }
}

static int move_add(void) {
    int w = -1;
    for (int i = 0; i < MAXN; i++) if (!cur.alive[i]) { w = i; break; }
    if (w < 0) return 0;
    int side = rndi(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < cur.cap; v++)
        if (cur.alive[v] && cur.col[v] == 1 - side) cand[nc++] = v;
    if (nc == 0) return 0;
    int k = nc < d ? nc : d;
    for (int i = 0; i < k; i++) {
        int j = i + rndi(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    cur.alive[w] = 1;
    cur.col[w] = side;
    cur.deg[w] = 0;
    cur.nalive++;
    if (w + 1 > cur.cap) cur.cap = w + 1;
    for (int i = 0; i < k; i++) {
        int p = cand[i];
        if (cur.deg[p] >= d) {
            int q = cur.adj[p][rndi(cur.deg[p])];
            del_edge(p, q);
        }
        add_edge(w, p);
    }
    return 1;
}

static int move_remove(void) {
    if (cur.nalive <= 2) return 0;
    int w, tries = 0;
    do {
        w = rndi(cur.cap);
        tries++;
    } while (!cur.alive[w] && tries < 100000);
    if (!cur.alive[w]) return 0;
    while (cur.deg[w] > 0) {
        int u = cur.adj[w][0];
        del_edge(w, u);
    }
    cur.alive[w] = 0;
    cur.nalive--;
    return 1;
}

static int move_swap(void) {
    int u, x, tries = 0;
    do {
        u = rndi(cur.cap);
        tries++;
    } while ((!cur.alive[u] || cur.deg[u] == 0) && tries < 100000);
    if (!cur.alive[u] || cur.deg[u] == 0) return 0;
    int v = cur.adj[u][rndi(cur.deg[u])];
    int s = cur.col[u];
    tries = 0;
    do {
        x = rndi(cur.cap);
        tries++;
    } while ((!cur.alive[x] || cur.deg[x] == 0 || cur.col[x] != s) && tries < 100000);
    if (!cur.alive[x] || cur.deg[x] == 0 || cur.col[x] != s) return 0;
    int y = cur.adj[x][rndi(cur.deg[x])];
    if (x == u || y == v) return 0;
    if (has_edge(u, y) || has_edge(x, v)) return 0;
    del_edge(u, v);
    del_edge(x, y);
    add_edge(u, y);
    add_edge(x, v);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 64) { printf("0 0\n"); return 0; }
    memset(&cur, 0, sizeof(cur));
    cur.cap = N0;
    cur.nalive = N0;
    for (int i = 0; i < N0; i++) cur.alive[i] = 1;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int i = 0; i < N0; i++) cur.col[i] = -1;
    for (int s = 0; s < N0; s++) {
        if (cur.col[s] >= 0) continue;
        cur.col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < cur.deg[u]; i++) {
                int v = cur.adj[u][i];
                if (cur.col[v] < 0) {
                    cur.col[v] = 1 - cur.col[u];
                    queue[qt++] = v;
                }
            }
        }
    }
    for (int u = 0; u < N0; u++) {
        for (int i = cur.deg[u] - 1; i >= 0; i--) {
            if (i >= cur.deg[u]) continue;
            int v = cur.adj[u][i];
            if (cur.col[v] == cur.col[u]) del_edge(u, v);
        }
    }

    clock_t t0 = clock();
    const double BETA = 2.0;
    const double T0 = 2.0, T1 = 0.03;

    phase1(t0, budget * 0.35);

    long long bad = compute_bad();
    double E = (double)bad - BETA * cur.nalive;
    if (bad == 0) {
        best = cur;
        have_best = 1;
    }
    double start2 = elapsed(t0);

    while (1) {
        double el = elapsed(t0);
        if (el > budget) break;
        double span = budget - start2;
        double frac = span > 0 ? (el - start2) / span : 1.0;
        if (frac < 0) frac = 0;
        if (frac > 1) frac = 1;
        double T = T0 * pow(T1 / T0, frac);

        bak = cur;
        double r = rndu();
        int ok;
        if (r < 0.35) ok = move_add();
        else if (r < 0.45) ok = move_remove();
        else ok = move_swap();
        if (!ok) continue;

        bad = compute_bad();
        double E2 = (double)bad - BETA * cur.nalive;
        if (E2 <= E || rndu() < exp(-(E2 - E) / T)) {
            E = E2;
            if (bad == 0 && (!have_best || cur.nalive > best.nalive)) {
                best = cur;
                have_best = 1;
            }
        } else {
            cur = bak;
        }
    }

    State *s = have_best ? &best : &cur;
    static int id[MAXN];
    int n = 0;
    for (int i = 0; i < s->cap; i++) id[i] = s->alive[i] ? n++ : -1;
    long m = 0;
    for (int u = 0; u < s->cap; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] > u) m++;
    }
    printf("%d %ld\n", n, m);
    for (int u = 0; u < s->cap; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) {
            int v = s->adj[u][i];
            if (v > u) printf("%d %d\n", id[u], id[v]);
        }
    }
    return 0;
}
"""


def _c_run(graph, d, D, seed, budget):
    """Run the C engine from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 32:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence; each old vertex has degree q+1, spare s = d-q-1.
# A-side: a set SA of points, each gets a new vertex joined to its q+1 lines.
# B-side: a set SB of lines, each gets a new vertex joined to its q+1 points.
# Each line (resp. point) may be hit by at most s chosen points (resp. lines).
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
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit at most s times."""
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
        if s < 0:
            continue
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
# Generalized quadrangle W(q) (diameter 4).
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
# Annealed group voltage lifts (bi-Cayley graphs over Z_m x| Z_k2), used for D >= 5.
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
            nx = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nx.append(v)
            count += len(nx)
            frontier = nx
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
#   D == 3 : arc-extended PG graphs as the start.
#   D == 4 : generalized quadrangle W(q) as the start.
#   D >= 5 : annealed group lifts for a short slice, then the C engine.
# The C engine (insertion then annealing) gets the rest of the budget.
# K_{d,d} (diameter 2) is the always-valid fallback. Every result is checked
# with lib.is_valid before it is returned.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            for g in _arc_extensions(d, start + 0.10 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    if D >= 5:
        try:
            anneal_end = start + 0.30 * time_limit
            ks = [1, 2, 2, 3, 4]
            while time.monotonic() < anneal_end:
                k = rng.choice(ks)
                base = best[0] // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                consider(_anneal(d, D, k, order, mul, rng, anneal_end, iters=400))
        except Exception:
            pass

    budget = 0.85 * time_limit - elapsed() - 1.0
    if budget >= 0.5:
        consider(_c_run(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
