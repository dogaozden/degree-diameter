import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each old vertex has degree q+1, so with d >= q+1 it has spare s = d-q-1.
# A point set S_A with at most s points on every line gives new point-side
# vertices A_P (one per P in S_A) joined to the q+1 lines through P. A line set
# S_B with at most s lines through every point gives new line-side vertices B_j
# joined to the q+1 points on j. The two sets are chosen independently; the
# diameter stays 3 for any choice. Order is 2m + |S_A| + |S_B|.
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


def _arc_graph(m, edges, point_lines, line_points, S_A, S_B):
    """Old PG incidence plus A-vertices for S_A (joined to lines through P) and B-vertices for S_B (joined to points on j)."""
    n = 2 * m + len(S_A) + len(S_B)
    E = list(edges)
    for t, P in enumerate(S_A):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    base_b = 2 * m + len(S_A)
    for t, j in enumerate(S_B):
        b = base_b + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        # Points and lines are indexed by the same vectors, so S serves as both sets.
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S, S)
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
# Simulated annealing over bi-Cayley voltage lifts.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
# C growth engine: starts from a valid graph and searches for a valid graph with
# two more vertices (one per side), repeatedly. Moves are edge rewirings that keep
# max degree <= d and bipartiteness; cost = number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXD / 2 + 64)
#define ITERS 20000

static int N, DMAX, DIAM;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static unsigned char side[MAXN];
static unsigned char am[MAXN][MAXN];
static uint64_t BUF0[MAXN][MAXW];
static uint64_t BUF1[MAXN][MAXW];
static uint64_t rng_s = 88172645463325252ULL;
static int cand[MAXN];
static int BU[MAXE], BV[MAXE];
static int bestN = 0, bestM = 0;
static int have_best = 0;

static uint64_t rnd64(void) {
    rng_s ^= rng_s >> 12;
    rng_s ^= rng_s << 25;
    rng_s ^= rng_s >> 27;
    return rng_s * 2685821657736338717ULL;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    am[u][v] = 1;
    am[v][u] = 1;
}

static void del_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_from(u, v);
    del_from(v, u);
    am[u][v] = 0;
    am[v][u] = 0;
}

static long long cost_eval(void) {
    uint64_t (*cur)[MAXW] = BUF0;
    uint64_t (*nxt)[MAXW] = BUF1;
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt[v];
            memcpy(o, cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *in = cur[adj[v][i]];
                for (int w = 0; w < W; w++) o[w] |= in[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int pick_cands(int a, int exclude, int *out) {
    int k = 0;
    for (int x = 0; x < N; x++) {
        if (side[x] == side[a] || x == exclude || x == a) continue;
        if (deg[x] >= DMAX || am[a][x]) continue;
        out[k++] = x;
    }
    return k;
}

static long long anneal(long long iters, double tstop, double T0, double T1) {
    long long cur = cost_eval();
    if (cur == 0) return 0;
    for (long long it = 0; it < iters; it++) {
        if ((it & 31) == 0 && now_sec() > tstop) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int type = 0, a, b = -1, c = -1;
        if (rndint(5) == 0) {
            a = rndint(N);
            if (deg[a] >= DMAX) continue;
            int k = pick_cands(a, -1, cand);
            if (k == 0) continue;
            c = cand[rndint(k)];
            type = 1;
            add_edge(a, c);
        } else {
            a = rndint(N);
            if (deg[a] == 0) continue;
            b = adj[a][rndint(deg[a])];
            int k = pick_cands(a, b, cand);
            if (k == 0) continue;
            c = cand[rndint(k)];
            type = 2;
            del_edge(a, b);
            add_edge(a, c);
        }
        long long nc = cost_eval();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) return 0;
        } else {
            if (type == 1) {
                del_edge(a, c);
            } else {
                del_edge(a, c);
                add_edge(a, b);
            }
        }
    }
    return cur;
}

static int snap_edges(int *U, int *V) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (v < u) {
                U[m] = v;
                V[m] = u;
                m++;
            }
        }
    }
    return m;
}

static void save_best(void) {
    have_best = 1;
    bestN = N;
    bestM = snap_edges(BU, BV);
}

static void clear_graph(void) {
    for (int i = 0; i < N; i++) {
        memset(am[i], 0, (size_t)N);
        deg[i] = 0;
    }
    N = 0;
}

static void restore(int n, const int *U, const int *V, int m) {
    clear_graph();
    N = n;
    for (int i = 0; i < m; i++) add_edge(U[i], V[i]);
}

static void fill_new(int x) {
    while (deg[x] < DMAX) {
        int k = pick_cands(x, -1, cand);
        if (k == 0) break;
        int c = cand[rndint(k)];
        add_edge(x, c);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rng_s ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rng_s == 0) rng_s = 1;
    double budget = atof(argv[4]);
    double tend = now_sec() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (DMAX < 1 || DMAX > MAXD || DIAM < 1 || n < 1 || n > MAXN - 400 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || am[u][v] ||
            deg[u] >= DMAX || deg[v] >= DMAX) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    static int color[MAXN];
    static int qu[MAXN];
    for (int i = 0; i < N; i++) color[i] = -1;
    int bip = 1;
    for (int s = 0; s < N && bip; s++) {
        if (color[s] != -1) continue;
        int head = 0, tail = 0;
        color[s] = 0;
        qu[tail++] = s;
        while (head < tail && bip) {
            int x = qu[head++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adj[x][i];
                if (color[y] == -1) {
                    color[y] = 1 - color[x];
                    qu[tail++] = y;
                } else if (color[y] == color[x]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }
    for (int i = 0; i < N; i++) side[i] = (unsigned char)color[i];

    if (cost_eval() == 0) {
        save_best();
    } else {
        while (now_sec() < tend) {
            if (anneal(ITERS, tend, 2.0, 0.15) == 0) {
                save_best();
                break;
            }
        }
    }

    while (have_best && now_sec() < tend && bestN + 2 <= MAXN) {
        restore(bestN, BU, BV, bestM);
        int A = N;
        int B = N + 1;
        N += 2;
        side[A] = 0;
        side[B] = 1;
        deg[A] = 0;
        deg[B] = 0;
        fill_new(A);
        fill_new(B);
        if (anneal(ITERS, tend, 2.0, 0.15) == 0) save_best();
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", BU[i], BV[i]);
    return 0;
}
"""


def _c_grow(start_graph, d, D, seed, budget):
    """Run the C growth engine from start_graph; return a candidate (n, edges) or None."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, int(seed) % (2 ** 31), round(budget, 2)],
                         stdin_graph=start_graph, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(text)
    except (RuntimeError, ValueError, OSError):
        return None
    if n <= 0:
        return None
    return n, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    pre_deadline = start + (0.3 if D >= 4 else 0.1) * time_limit
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

    # Arc-extended projective plane graphs. Diameter 3, so valid for all D >= 3.
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

    # Annealed group voltage lifts (short phase).
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
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

    # C growth from the best graph found so far, using most of the remaining time.
    if d >= 3 and D >= 2 and best_n < lib.moore_bound(d, D):
        budget = 0.85 * time_limit - (time.monotonic() - start) - 3.0
        if budget >= 3.0:
            grown = _c_grow(best, d, D, seed, budget)
            if grown is not None:
                consider(grown[0], grown[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
