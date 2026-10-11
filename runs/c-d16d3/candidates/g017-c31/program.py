import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite repair search with vertex insertion.
#
# Input: a valid bipartite graph (max degree d, diameter <= D). The engine
# appends two new vertices (one on each side) and runs simulated annealing over
# degree-preserving edge switches, edge additions and edge removals. The cost is
# the number of unordered vertex pairs at distance > D, computed with bitset
# ball expansion. Whenever the cost reaches zero, the graph is recorded, two more
# vertices are added, and the search continues. The largest recorded graph is
# printed. If nothing beats the input, it prints "0 0" and Python keeps its own.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define DCAP 64

static int d_, D_, n_;
static int col[MAXN];
static int deg[MAXN];
static int adj[MAXN][DCAP];
static unsigned char M[MAXN][MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static int snap_n = 0, snap_m = 0;
static int snap_a[MAXN * DCAP / 2 + 8];
static int snap_b[MAXN * DCAP / 2 + 8];
static uint64_t rs = 88172645463325252ULL;
static int bfsq[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) {
    return (int)(rnd() % (uint64_t)k);
}

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    M[a][b] = 1;
    M[b][a] = 1;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void remove_from(int v, int u) {
    for (int i = 0; i < deg[v]; i++) {
        if (adj[v][i] == u) {
            adj[v][i] = adj[v][deg[v] - 1];
            deg[v]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    M[a][b] = 0;
    M[b][a] = 0;
    remove_from(a, b);
    remove_from(b, a);
}

/* Number of unordered pairs at distance > D_ (unreachable counts). */
static long long cost_eval(void) {
    int W = (n_ + 63) / 64;
    uint64_t *R0 = bufA, *R1 = bufB;
    memset(R0, 0, sizeof(uint64_t) * (size_t)n_ * (size_t)W);
    for (int v = 0; v < n_; v++)
        R0[(size_t)v * W + (size_t)(v / 64)] |= 1ULL << (v % 64);
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n_; v++) {
            uint64_t *out = R1 + (size_t)v * W;
            const uint64_t *in = R0 + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *nb = R0 + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) out[w] |= nb[w];
            }
        }
        uint64_t *t = R0;
        R0 = R1;
        R1 = t;
    }
    long long unreached = 0;
    for (int v = 0; v < n_; v++) {
        int c = 0;
        const uint64_t *in = R0 + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(in[w]);
        unreached += n_ - c;
    }
    return unreached / 2;
}

static int pick_side(int side) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(n_);
        if (col[v] == side) return v;
    }
    return -1;
}

static void take_snapshot(void) {
    snap_n = n_;
    snap_m = 0;
    for (int v = 0; v < n_; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (u > v) {
                snap_a[snap_m] = v;
                snap_b[snap_m] = u;
                snap_m++;
            }
        }
    }
}

static int extend_two(void) {
    if (n_ + 2 > MAXN) return 0;
    col[n_] = 0;
    col[n_ + 1] = 1;
    deg[n_] = 0;
    deg[n_ + 1] = 0;
    n_ += 2;
    return 1;
}

static void print_and_exit(void) {
    if (snap_n == 0) {
        printf("0 0\n");
        return;
    }
    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++) printf("%d %d\n", snap_a[i], snap_b[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double budget = atof(argv[4]);
    if (d_ < 1 || d_ > DCAP || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    n_ = n;
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || M[u][v] ||
            deg[u] >= d_ || deg[v] >= d_) { bad = 1; break; }
        add_edge(u, v);
    }
    if (!bad) {
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && !bad; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            bfsq[qt++] = s;
            while (qh < qt) {
                int x = bfsq[qh++];
                for (int i = 0; i < deg[x]; i++) {
                    int y = adj[x][i];
                    if (col[y] < 0) {
                        col[y] = 1 - col[x];
                        bfsq[qt++] = y;
                    } else if (col[y] == col[x]) {
                        bad = 1;
                        break;
                    }
                }
                if (bad) break;
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    if (cost_eval() == 0) take_snapshot();
    if (!extend_two()) {
        print_and_exit();
        return 0;
    }
    long long cur = cost_eval();

    clock_t t0 = clock();
    double T = 1.0, T0 = 1.0, T1 = 0.05;
    unsigned long long it = 0;
    while (1) {
        it++;
        if ((it & 63ULL) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
            T = T0 * pow(T1 / T0, el / budget);
        }
        int type = 0, ma = -1, mb = -1, mc = -1, me = -1;
        double r = rnd01();
        if (r < 0.6) {
            type = 0;
            int a = pick_side(0), c = pick_side(0);
            if (a < 0 || c < 0 || a == c || deg[a] == 0 || deg[c] == 0) continue;
            int b = adj[a][rndint(deg[a])];
            int e = adj[c][rndint(deg[c])];
            if (b == e || M[a][e] || M[c][b]) continue;
            ma = a; mb = b; mc = c; me = e;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
        } else if (r < 0.85) {
            type = 1;
            int a = pick_side(0), b = pick_side(1);
            if (a < 0 || b < 0 || deg[a] >= d_ || deg[b] >= d_ || M[a][b]) continue;
            ma = a; mb = b;
            add_edge(a, b);
        } else {
            type = 2;
            int a = pick_side(0);
            if (a < 0 || deg[a] == 0) continue;
            int b = adj[a][rndint(deg[a])];
            ma = a; mb = b;
            del_edge(a, b);
        }

        long long nc = cost_eval();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) {
                take_snapshot();
                if (extend_two()) cur = cost_eval();
                else break;
            }
        } else {
            if (type == 0) {
                del_edge(ma, me);
                del_edge(mc, mb);
                add_edge(ma, mb);
                add_edge(mc, me);
            } else if (type == 1) {
                del_edge(ma, mb);
            } else {
                add_edge(ma, mb);
            }
        }
    }
    print_and_exit();
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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
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


_LP = None  # line_points for the current q, set in _arc_extensions


def _arc_graph(m, edges, point_lines, S):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in _LP[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    global _LP
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        _LP = line_points
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S)
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
# Simulated annealing over bi-Cayley voltage lifts (used for D != 3).
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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # D = 3: repair search in C, starting from the best arc graph.
    # Skip if already at the Moore bound (calibration case) or outside the C limits.
    if D == 3 and 3 <= d <= 64 and best_n < lib.moore_bound(d, D):
        elapsed = time.monotonic() - start
        budget = max(0.5, 0.75 * time_limit - elapsed - 1.0)
        timeout = max(1.0, min(budget + 4.0, time_limit - (time.monotonic() - start) - 1.0))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=timeout)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    # Other diameters (and degenerate D = 3 degrees): generalized quadrangle and voltage lifts.
    if D != 3 or d < 3 or d > 64:
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

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
