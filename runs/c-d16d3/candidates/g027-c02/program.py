import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex-insertion annealing.
#
# Start from a valid bipartite graph. Keep the two sides fixed, so every edge
# joins opposite sides and the graph stays bipartite. The cost is the number of
# unordered vertex pairs at distance > D, computed with bitset balls.
#   - When cost is 0, the current graph is valid: save it and insert a new
#     vertex on the side with more spare degree, joined to up to d spare vertices.
#   - Between insertions, anneal with moves: rewire an edge endpoint, add an
#     edge in spare degree, or remove an edge. Stuck runs restart from the best.
# Output is the largest valid graph seen. Python checks it with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXDEG 64
#define WMAX ((MAXN + 63) / 64)

static int n = 0;
static int dcap = 0;
static int diam = 0;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];

static int bn = 0;
static int bdeg[MAXN];
static int bside[MAXN];
static int badj[MAXN][MAXDEG];

static uint64_t bufA[MAXN][WMAX];
static uint64_t bufB[MAXN][WMAX];
static uint64_t rng_state = 1;

static uint64_t rnd64(void) {
    uint64_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rng_state = x;
    return x;
}

static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int is_adj(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

/* Number of unordered pairs at distance > diam (unreachable pairs count). */
static long evaluate(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = bufA;
    uint64_t (*nxt)[WMAX] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int t = 0; t < diam; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*tmp)[WMAX] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_best(void) {
    bn = n;
    for (int v = 0; v < n; v++) {
        bdeg[v] = deg[v];
        bside[v] = side[v];
        memcpy(badj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void load_best(void) {
    n = bn;
    for (int v = 0; v < n; v++) {
        deg[v] = bdeg[v];
        side[v] = bside[v];
        memcpy(adj[v], badj[v], sizeof(int) * (size_t)bdeg[v]);
    }
}

/* Insert a vertex on the side opposite to the side with the most spare degree,
   joined to as many spare vertices of that side as possible. */
static int grow_vertex(void) {
    long sp[2] = {0, 0};
    for (int v = 0; v < n; v++) sp[side[v]] += dcap - deg[v];
    if (sp[0] == 0 && sp[1] == 0) return 0;
    int t;
    if (sp[0] > sp[1]) t = 0;
    else if (sp[1] > sp[0]) t = 1;
    else t = rndint(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (side[v] == t && deg[v] < dcap) cand[nc++] = v;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
    int x = n;
    n++;
    side[x] = 1 - t;
    deg[x] = 0;
    for (int i = 0; i < nc && deg[x] < dcap; i++) add_edge(x, cand[i]);
    return 1;
}

static int accept_move(long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

static void print_graph(void) {
    long m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    printf("%d %ld\n", n, m / 2);
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (u < adj[u][k]) printf("%d %d\n", u, adj[u][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed seconds\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double t0 = now_sec();
    rng_state = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rng_state == 0) rng_state = 88172645463325252ULL;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }
    dcap = d;
    diam = D;

    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sn > MAXN / 2 || sm < 0 || sm > MAXN * MAXDEG) { sn = 0; sm = 0; }
    int ok = (sn > 0);
    int *eu = malloc(sizeof(int) * (size_t)(sm + 1));
    int *ev = malloc(sizeof(int) * (size_t)(sm + 1));
    for (int i = 0; i < sm && ok; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) ok = 0;
    }
    if (ok) {
        n = sn;
        for (int v = 0; v < n; v++) deg[v] = 0;
        for (int i = 0; i < sm && ok; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) ok = 0;
            else if (is_adj(u, v) || deg[u] >= dcap || deg[v] >= dcap) ok = 0;
            else add_edge(u, v);
        }
    }
    if (ok) {
        for (int v = 0; v < n; v++) side[v] = -1;
        int *queue = malloc(sizeof(int) * (size_t)n);
        for (int s = 0; s < n && ok; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            queue[qt++] = s;
            while (qh < qt && ok) {
                int u = queue[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int v = adj[u][k];
                    if (side[v] == -1) {
                        side[v] = 1 - side[u];
                        queue[qt++] = v;
                    } else if (side[v] == side[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        free(queue);
    }
    if (!ok) {
        /* Fallback start: K_{d,d}, diameter 2. */
        n = 2 * d;
        for (int v = 0; v < n; v++) {
            deg[v] = 0;
            side[v] = (v < d) ? 0 : 1;
        }
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++)
                add_edge(i, d + j);
    }
    free(eu);
    free(ev);

    bn = 0;
    long f = evaluate();
    if (f == 0) save_best();
    long minf = f, since = 0, iter = 0;
    const double T_hi = 1.5, T_lo = 0.08;
    const long cycle = 100000, stuck_limit = 60000;
    const int maxN = MAXN - 2;

    while (1) {
        if ((iter & 127) == 0 && now_sec() - t0 >= budget) break;
        iter++;

        if (f == 0) {
            if (bn == 0 || n >= bn) save_best();
            if (n >= maxN) break;
            if (!grow_vertex()) break;
            f = evaluate();
            minf = f;
            since = 0;
            continue;
        }

        if (++since > stuck_limit) {
            if (bn > 0) {
                load_best();
                f = evaluate();
            }
            minf = f;
            since = 0;
            continue;
        }

        double phase = (double)(iter % cycle) / (double)cycle;
        double T = T_hi * pow(T_lo / T_hi, phase);
        int mt = rndint(100);
        long f2;

        if (mt < 70) {
            /* Rewire: keep u, replace the other end v by a same-side w. */
            int u = rndint(n);
            if (deg[u] == 0) continue;
            int v = adj[u][rndint(deg[u])];
            int w = -1;
            for (int tr = 0; tr < 40 && w < 0; tr++) {
                int c = rndint(n);
                if (c != v && side[c] == side[v] && deg[c] < dcap && !is_adj(u, c)) w = c;
            }
            if (w < 0) continue;
            del_edge(u, v);
            add_edge(u, w);
            f2 = evaluate();
            if (accept_move(f2 - f, T)) f = f2;
            else {
                del_edge(u, w);
                add_edge(u, v);
            }
        } else if (mt < 85) {
            /* Add an edge between spare vertices on opposite sides. */
            int u = rndint(n);
            if (deg[u] >= dcap) continue;
            int w = -1;
            for (int tr = 0; tr < 40 && w < 0; tr++) {
                int c = rndint(n);
                if (side[c] != side[u] && deg[c] < dcap && !is_adj(u, c)) w = c;
            }
            if (w < 0) continue;
            add_edge(u, w);
            f2 = evaluate();
            if (accept_move(f2 - f, T)) f = f2;
            else del_edge(u, w);
        } else {
            /* Remove an edge. */
            int u = rndint(n);
            if (deg[u] == 0) continue;
            int v = adj[u][rndint(deg[u])];
            del_edge(u, v);
            f2 = evaluate();
            if (accept_move(f2 - f, T)) f = f2;
            else add_edge(u, v);
        }

        if (f < minf) {
            minf = f;
            since = 0;
        }
    }

    if (bn > 0) load_best();
    print_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Attach a new A-vertex to all
# lines through each chosen point (each line may take at most s such points),
# and a new B-vertex to all points of each chosen line (each point may take at
# most s such lines). The result has diameter 3.
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
# Simulated annealing over bi-Cayley voltage lifts (used only for D >= 5).
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

    # Python constructions: arc-extended projective planes (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() - t0 < 0.15 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing, only for larger diameters.
    if D >= 5:
        rng = random.Random(seed)
        deadline = t0 + 0.4 * time_limit
        ks = [1, 2, 2, 3, 4]
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

    # Main search: C vertex-insertion annealing from the best construction.
    if D >= 3 and d <= 64:
        elapsed = time.monotonic() - t0
        budget = 0.8 * time_limit - elapsed - 2.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=budget + 6.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
