"""Program for bipartite graphs with max degree d and diameter D.

Pipeline:
1. Python builds arc-extended projective-plane graphs (D >= 3), a generalized
   quadrangle (D >= 4), and a short annealed voltage-lift search.
2. C engine "vertex insertion annealing": starting from the best valid graph,
   it adds one vertex at a time. Each new vertex is annealed with edge
   add / edge swap / endpoint rewire moves that keep the graph bipartite and
   within the degree cap, minimizing the number of ordered pairs at distance
   greater than D (bitset ball computation). On failure the state is restored
   to the last valid graph.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define MAXE 24000

static int dmax = 3, Dist = 3;
static int N = 0, NE = 0;
static int side[MAXN], deg[MAXN];
static unsigned char adjm[MAXN][MAXN];
static int eu[MAXE], ev[MAXE];
static int seu[MAXE], sev[MAXE], sNE = 0, sN = 0;
static int beu[MAXE], bev[MAXE], bNE = 0, bN = 0;
static uint64_t rs = 88172645463325252ULL;
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int off[MAXN + 1], pos[MAXN], nb[2 * MAXE];

static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    int u = a, v = b;
    if (side[u] == 1) { int t = u; u = v; v = t; }
    eu[NE] = u; ev[NE] = v; NE++;
    adjm[u][v] = 1; adjm[v][u] = 1;
    deg[u]++; deg[v]++;
}

static void del_edge(int i) {
    int u = eu[i], v = ev[i];
    adjm[u][v] = 0; adjm[v][u] = 0;
    deg[u]--; deg[v]--;
    NE--;
    if (i != NE) { eu[i] = eu[NE]; ev[i] = ev[NE]; }
}

/* Number of ordered pairs (v,w) with dist(v,w) > Dist. Zero means valid. */
static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    off[0] = 0;
    for (int v = 0; v < N; v++) { off[v + 1] = off[v] + deg[v]; pos[v] = off[v]; }
    for (int e = 0; e < NE; e++) {
        nb[pos[eu[e]]++] = ev[e];
        nb[pos[ev[e]]++] = eu[e];
    }
    uint64_t (*A)[MAXW] = RA, (*B)[MAXW] = RB;
    for (int v = 0; v < N; v++) {
        memset(A[v], 0, sizeof(uint64_t) * (size_t)W);
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < Dist; t++) {
        for (int v = 0; v < N; v++) {
            memcpy(B[v], A[v], sizeof(uint64_t) * (size_t)W);
            for (int k = off[v]; k < off[v + 1]; k++) {
                int u = nb[k];
                for (int w = 0; w < W; w++) B[v][w] |= A[u][w];
            }
        }
        uint64_t (*T)[MAXW] = A; A = B; B = T;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(A[v][w]);
        cost += N - c;
    }
    return cost;
}

/* Add an edge from a random vertex to a random opposite-side vertex with spare degree. */
static int try_add_move(void) {
    for (int t = 0; t < 40; t++) {
        int u = rndint(N);
        if (deg[u] >= dmax) continue;
        int w = rndint(N);
        if (side[w] == side[u] || deg[w] >= dmax || adjm[u][w]) continue;
        add_edge(u, w);
        return 1;
    }
    return 0;
}

/* Anneal until cost 0 (returns 1) or budget exhausted (returns 0). */
static int anneal(long long iters, double T0, double T1, double deadline) {
    long long cur = eval_cost();
    if (cur == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 63) == 0 && cpu_now() > deadline) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int kind = rndint(100);
        int mt = 0, a = 0, b = 0, c = 0, e = 0;
        if (kind < 35) {
            if (!try_add_move()) continue;
            mt = 0;
        } else if (kind < 70) {
            if (NE < 2) continue;
            int i = rndint(NE), j = rndint(NE);
            if (i == j) continue;
            a = eu[i]; b = ev[i]; c = eu[j]; e = ev[j];
            if (a == c || b == e || adjm[a][e] || adjm[c][b]) continue;
            int hi = i > j ? i : j, lo = i > j ? j : i;
            del_edge(hi);
            del_edge(lo);
            add_edge(a, e);
            add_edge(c, b);
            mt = 1;
        } else {
            if (NE < 1) continue;
            int i = rndint(NE);
            a = eu[i]; b = ev[i];
            int w = -1;
            for (int t = 0; t < 40; t++) {
                int cand = rndint(N);
                if (side[cand] == 1 && cand != b && deg[cand] < dmax && !adjm[a][cand]) {
                    w = cand;
                    break;
                }
            }
            if (w < 0) continue;
            del_edge(i);
            add_edge(a, w);
            mt = 2;
        }
        long long c2 = eval_cost();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            if (mt == 0) {
                del_edge(NE - 1);
            } else if (mt == 1) {
                del_edge(NE - 1);
                del_edge(NE - 1);
                add_edge(a, b);
                add_edge(c, e);
            } else {
                del_edge(NE - 1);
                add_edge(a, b);
            }
        }
    }
    return 0;
}

static void save_snapshot(void) {
    sN = N; sNE = NE;
    for (int i = 0; i < NE; i++) { seu[i] = eu[i]; sev[i] = ev[i]; }
}

static void restore_snapshot(void) {
    while (NE > 0) del_edge(NE - 1);
    N = sN;
    for (int i = 0; i < sNE; i++) add_edge(seu[i], sev[i]);
}

static void save_best(void) {
    bN = N; bNE = NE;
    for (int i = 0; i < NE; i++) { beu[i] = eu[i]; bev[i] = ev[i]; }
}

static void echo_input(int n, int m, const int *iu, const int *iv) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", iu[i], iv[i]);
}

static int iu_buf[MAXE], iv_buf[MAXE];

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed time\n"); return 1; }
    dmax = atoi(argv[1]);
    Dist = atoi(argv[2]);
    if (dmax < 1) dmax = 1;
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double deadline = cpu_now() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 200 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &iu_buf[i], &iv_buf[i]) != 2) { printf("0 0\n"); return 0; }
    }

    static int ioff[MAXN + 1], ipos[MAXN], inb[2 * MAXE], col[MAXN], qu[MAXN], idg[MAXN];
    int ok = 1;
    for (int v = 0; v < n; v++) idg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u = iu_buf[i], v = iv_buf[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) { ok = 0; break; }
        idg[u]++; idg[v]++;
    }
    if (ok) {
        for (int v = 0; v < n; v++) if (idg[v] > dmax) ok = 0;
    }
    if (!ok) { echo_input(n, m, iu_buf, iv_buf); return 0; }

    ioff[0] = 0;
    for (int v = 0; v < n; v++) { ioff[v + 1] = ioff[v] + idg[v]; ipos[v] = ioff[v]; }
    for (int i = 0; i < m; i++) {
        inb[ipos[iu_buf[i]]++] = iv_buf[i];
        inb[ipos[iv_buf[i]]++] = iu_buf[i];
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt && ok) {
            int u = qu[qh++];
            for (int k = ioff[u]; k < ioff[u + 1]; k++) {
                int w = inb[k];
                if (col[w] < 0) { col[w] = 1 - col[u]; qu[qt++] = w; }
                else if (col[w] == col[u]) { ok = 0; break; }
            }
        }
    }
    if (!ok) { echo_input(n, m, iu_buf, iv_buf); return 0; }

    N = n; NE = 0;
    for (int v = 0; v < n; v++) { side[v] = col[v]; deg[v] = 0; }
    for (int i = 0; i < m; i++) add_edge(iu_buf[i], iv_buf[i]);
    save_best();

    int successes = 0;
    while (cpu_now() < deadline && N < MAXN - 1) {
        save_snapshot();
        int x = N;
        side[x] = rndint(2);
        deg[x] = 0;
        N++;
        int good = anneal(60000, 3.0, 0.15, deadline);
        if (good) {
            save_best();
            successes++;
        } else {
            restore_snapshot();
        }
    }

    printf("%d %d\n", bN, bNE);
    for (int i = 0; i < bNE; i++) printf("%d %d\n", beu[i], bev[i]);
    return 0;
}
'''


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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per point of S (on lines through it) and a new B-vertex per line of S (on its points)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) baseline (D = 4).
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
# Short simulated annealing over bi-Cayley voltage lifts (fallback search).
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


def _group_phase(d, D, rng, best_n, deadline):
    """Short annealed voltage-lift search; returns a list of (n, edges) candidates."""
    results = []
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
            results.append(res)
    return results


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        for cand in _arc_extensions(d, t0 + 0.1 * time_limit, random.Random(seed * 7919 + d)):
            consider(cand)

    if D >= 4:
        consider(_best_gq(d))

    # Short group voltage-lift search, a small share of the budget.
    for cand in _group_phase(d, D, rng, best[0], t0 + 0.1 * time_limit):
        consider(cand)

    # Main search: C vertex-insertion annealing from the best valid graph.
    elapsed = time.monotonic() - t0
    budget = 0.78 * time_limit - elapsed
    if d <= 4:
        budget = min(budget, 2.0)
    if budget > 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3)],
                            stdin_graph=best,
                            timeout=budget + max(2.0, 0.08 * time_limit))
            consider(lib.parse_graph_text(out))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
