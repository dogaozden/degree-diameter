import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex addition on a valid bipartite graph with diameter 3.
#
# Adding a vertex x never increases any existing distance, so a pure addition
# is valid iff x reaches every vertex within 3 steps. x joins a set S of
# opposite-side vertices with spare degree, and dist(x, v) <= 3 holds exactly
# when v lies within distance 2 of some s in S. The engine finds S by greedy
# set cover over those 2-balls, with randomized ties and occasional random
# picks, and keeps every addition that covers all vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXD 40

static int n, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static int stamp[MAXN];
static int stc = 0;
static uint64_t rs = 0x2545F4914F6CDD1DULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static int full_ok(void) {
    static int dist[MAXN], q[MAXN];
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        q[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int u = q[h++];
            if (dist[u] >= D) continue;
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    q[t++] = v;
                }
            }
        }
        if (t != n) return 0;
    }
    return 1;
}

static int color_graph(void) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int visit(int x, unsigned char *unc, int apply, int st) {
    if (!unc[x] || stamp[x] == st) return 0;
    stamp[x] = st;
    if (apply) unc[x] = 0;
    return 1;
}

/* Number of uncovered vertices within distance 2 of c; marks them covered if apply. */
static int ball_cover(int c, unsigned char *unc, int apply) {
    if (stc > 2000000000) {
        memset(stamp, 0, sizeof(stamp));
        stc = 0;
    }
    int st = ++stc;
    int g = 0;
    g += visit(c, unc, apply, st);
    for (int i = 0; i < deg[c]; i++) {
        int u = adj[c][i];
        g += visit(u, unc, apply, st);
        for (int j = 0; j < deg[u]; j++) g += visit(adj[u][j], unc, apply, st);
    }
    return g;
}

/* Greedy cover: pick S (opposite side, spare degree) so every vertex is within 2 of S. */
static int try_add(int side_new, int *S, unsigned char *unc, int *gain) {
    static unsigned char used[MAXN];
    int cs = 1 - side_new;
    int remaining = n, ns = 0;
    for (int v = 0; v < n; v++) {
        unc[v] = 1;
        used[v] = 0;
    }
    while (remaining > 0 && ns < d) {
        int best = -1, bestg = 0, ties = 0;
        for (int c = 0; c < n; c++) {
            gain[c] = 0;
            if (side[c] != cs || deg[c] >= d || used[c]) continue;
            int g = ball_cover(c, unc, 0);
            gain[c] = g;
            if (g > bestg) {
                bestg = g;
                best = c;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndi(ties) == 0) best = c;
            }
        }
        if (best < 0) break;
        if (rndi(100) < 10) {
            int cnt = 0, pick = -1;
            for (int c = 0; c < n; c++) {
                if (gain[c] > 0) {
                    cnt++;
                    if (rndi(cnt) == 0) pick = c;
                }
            }
            if (pick >= 0) best = pick;
        }
        S[ns++] = best;
        used[best] = 1;
        remaining -= ball_cover(best, unc, 1);
    }
    return remaining == 0 ? ns : -1;
}

static int add_vertex(int side_new, unsigned char *unc, int *gain) {
    int S[MAXD];
    if (n >= MAXN - 1) return 0;
    int ns = try_add(side_new, S, unc, gain);
    if (ns <= 0) return 0;
    int id = n++;
    deg[id] = 0;
    side[id] = side_new;
    for (int i = 0; i < ns; i++) add_edge(id, S[i]);
    return 1;
}

static void output_graph(void) {
    int m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m++;
    printf("%d %d\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
}

static unsigned char unc_buf[MAXN];
static int gain_buf[MAXN];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double budget = atof(argv[4]);
    if (d < 1 || d >= MAXD || D != 3) {
        printf("0 0\n");
        return 0;
    }

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2) {
        n = 0;
        m0 = 0;
    }
    if (n < 0 || n > MAXN / 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int ok = 1;
    if (n == 0) {
        /* No start graph: K_{d,d} is valid for diameter 2 and hence 3. */
        n = 2 * d;
        for (int a = 0; a < d; a++) {
            side[a] = 0;
            side[d + a] = 1;
            for (int b = 0; b < d; b++) add_edge(a, d + b);
        }
    } else {
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
                deg[u] >= d || deg[v] >= d || has_edge(u, v)) {
                ok = 0;
                break;
            }
            add_edge(u, v);
        }
        if (ok) ok = color_graph();
        if (ok) ok = full_ok();
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int fails = 0;
    while (fails < 4000) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        if (n >= MAXN - 1) break;
        int sn = rndi(2);
        if (add_vertex(sn, unc_buf, gain_buf) || add_vertex(1 - sn, unc_buf, gain_buf)) {
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!full_ok()) {
        printf("0 0\n");
        return 0;
    }
    output_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
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
    """True if every target t is hit by <= s entries of S (repeats counted)."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets so every target is hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
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
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
        SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
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
# Simulated annealing over bi-Cayley voltage lifts (D >= 4 path).
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
# D = 3 pipeline: best arc/projective start, then C greedy vertex addition.
# ----------------------------------------------------------------------------

def _c_extend(graph, d, D, seed, left):
    """Run the C engine from `graph` for about `left` seconds of the remaining budget. None on failure."""
    n, e = graph
    timeout = max(1.0, 0.85 * left - 1.5)
    budget = max(0.5, timeout - 1.5)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=(n, e), timeout=timeout)
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
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

    if D >= 3:
        arc_deadline = start + 0.2 * time_limit
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)
        for q in range(2, min(d - 1, 23) + 1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))

    if D == 3:
        left = time_limit - (time.monotonic() - start)
        if left > 6:
            res = _c_extend(best, d, D, seed, left)
            if res is not None:
                consider(*res)
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for D >= 4.
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
