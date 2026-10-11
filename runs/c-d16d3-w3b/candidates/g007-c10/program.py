import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: maximum "load-bounded" point set in a bipartite incidence graph.
#
# Input: a bipartite graph on vertices 0..n-1, chosen side = 0..n/2-1,
# constraint side = n/2..n-1. Find a set S of chosen vertices such that every
# constraint vertex has at most s neighbours in S. Iterated local search with
# add moves, plateau swap moves and a tabu list.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 0x2545F4914F6CDD1DULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int S_;
static int *off, *adj, *load, *inS;
static long *tabu;
static int cnt_;

static int feasible(int v) {
    for (int k = off[v]; k < off[v + 1]; k++) if (load[adj[k]] >= S_) return 0;
    return 1;
}
static void addv(int v) {
    inS[v] = 1; cnt_++;
    for (int k = off[v]; k < off[v + 1]; k++) load[adj[k]]++;
}
static void remv(int v) {
    inS[v] = 0; cnt_--;
    for (int k = off[v]; k < off[v + 1]; k++) load[adj[k]]--;
}

int main(int argc, char **argv) {
    S_ = argc > 1 ? atoi(argv[1]) : 1;
    double tl = argc > 2 ? atof(argv[2]) : 1.0;
    uint64_t seed = argc > 3 ? (uint64_t)atoll(argv[3]) : 1;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 0 || m < 0) return 1;
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    int *deg = calloc((size_t)n + 1, sizeof(int));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 1;
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n) return 1;
        deg[eu[i]]++; deg[ev[i]]++;
    }
    int H = n / 2;
    if (H == 0 || S_ < 1) { printf("0\n\n"); return 0; }
    off = malloc(sizeof(int) * (size_t)(n + 2));
    off[0] = 0;
    for (int v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    adj = malloc(sizeof(int) * (size_t)(2 * m + 1));
    int *fillc = calloc((size_t)n + 1, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        adj[off[u] + fillc[u]++] = v;
        adj[off[v] + fillc[v]++] = u;
    }
    load = calloc((size_t)n + 1, sizeof(int));
    inS = calloc((size_t)n + 1, sizeof(int));
    tabu = calloc((size_t)n + 1, sizeof(long));
    int *bestS = calloc((size_t)n + 1, sizeof(int));
    int *freel = malloc(sizeof(int) * (size_t)(H + 1));
    int *rem = malloc(sizeof(int) * (size_t)(H + 1));
    int *perm = malloc(sizeof(int) * (size_t)(H + 1));

    for (int i = 0; i < H; i++) perm[i] = i;
    for (int i = H - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    for (int i = 0; i < H; i++) if (feasible(perm[i])) addv(perm[i]);
    int best = cnt_;
    for (int v = 0; v < H; v++) bestS[v] = inS[v];

    long it = 0;
    const long TT = 7;
    const double T = 0.35;
    clock_t t0 = clock();
    while (1) {
        it++;
        if ((it & 127) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        int nf = 0;
        for (int v = 0; v < H; v++)
            if (!inS[v] && tabu[v] <= it && feasible(v)) freel[nf++] = v;
        if (nf > 0) {
            addv(freel[rndint(nf)]);
        } else {
            int v = -1;
            for (int t = 0; t < 60; t++) {
                int c = rndint(H);
                if (!inS[c] && tabu[c] <= it) { v = c; break; }
            }
            if (v < 0) continue;
            int nr = 0;
            for (int k = off[v]; k < off[v + 1]; k++) {
                int c = adj[k];
                while (load[c] >= S_) {
                    int nm = 0;
                    for (int j = off[c]; j < off[c + 1]; j++) if (inS[adj[j]]) nm++;
                    if (nm == 0) break;
                    int pick = rndint(nm);
                    int u = -1;
                    for (int j = off[c]; j < off[c + 1]; j++) {
                        if (inS[adj[j]]) {
                            if (pick == 0) { u = adj[j]; break; }
                            pick--;
                        }
                    }
                    if (u < 0) break;
                    remv(u);
                    rem[nr++] = u;
                    tabu[u] = it + TT;
                }
            }
            addv(v);
            int extra = nr - 1;
            if (extra > 0 && rnd01() >= exp(-extra / T)) {
                remv(v);
                for (int i = 0; i < nr; i++) addv(rem[i]);
            }
        }
        if (cnt_ > best) {
            best = cnt_;
            for (int v = 0; v < H; v++) bestS[v] = inS[v];
        }
    }
    printf("%d\n", best);
    for (int v = 0; v < H; v++) if (bestS[v]) printf("%d ", v);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# NEW construction: independent dual arcs on PG(2, q).
#
# Let S_A be a set of points and S_B a set of lines of PG(2, q). Add one
# A-vertex per point P in S_A, joined to the q+1 lines through P, and one
# B-vertex per line L in S_B, joined to the q+1 points on L. The constraints
# are: every line carries at most s points of S_A, and every point lies on at
# most s lines of S_B. These two conditions are independent, so S_A and S_B
# are each a (k, s)-arc (up to duality) and can be chosen separately, each by
# the C local search above. Diameter stays 3 (checked by lib.is_valid).
# With s = 2, q = 13 (d = 16) each arc can have about 22 points,
# giving 2*183 + 2*22 = 410 vertices before the fill stages.
# ----------------------------------------------------------------------------

def _pg_adj(q):
    """Return (m, edges, pl, lp) for PG(2, q): points 0..m-1, lines m..2m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]   # point -> line indices
    lp = [[] for _ in range(m)]   # line index -> points
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _arc_run(s, m, edges, budget, seed):
    """Run the C search on a bipartite graph (chosen side 0..m-1); return verified chosen indices."""
    try:
        out = lib.run_c(C_SOURCE, [s, round(budget, 2), seed],
                        stdin_graph=(2 * m, edges), timeout=budget + 30)
    except RuntimeError:
        return []
    toks = out.split()
    if not toks:
        return []
    k = int(toks[0])
    S = [int(x) for x in toks[1:1 + k]]
    if len(S) != k or len(set(S)) != k or any(not 0 <= P < m for P in S):
        return []
    nb = [[] for _ in range(m)]
    for u, v in edges:
        nb[u].append(v)
    load = {}
    for P in S:
        for c in nb[P]:
            load[c] = load.get(c, 0) + 1
    if any(x > s for x in load.values()):
        return []
    return S


def _ext(m, edges, pl, lp, SA, SB):
    """Old PG incidence plus an A-vertex per point of SA and a B-vertex per line of SB."""
    na = len(SA)
    n = 2 * m + na + len(SB)
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, L in enumerate(SB):
        y = 2 * m + na + t
        for Q in lp[L]:
            E.append((Q, y))
    return n, E


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3). Unchanged from the parent.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


def _cross_saturate(n, edges, d, n_new, rng):
    """Add random cross edges (touching a vertex >= n_new) while degree allows; return new edge list."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    col = _bipartition(n, adj)
    have = set()
    for u, v in edges:
        have.add((u, v) if col[u] == 0 else (v, u))
    L = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R
             if (a, b) not in have and (a >= n_new or b >= n_new)]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
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
# Simulated annealing over bi-Cayley voltage lifts (unchanged from the parent).
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
    deadline = start + 0.8 * time_limit
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

    # NEW: independent dual-arc extension of PG(2, q), arcs found by C search.
    # Diameter 3, so valid for all D >= 3.
    if D >= 3:
        qs = sorted([q for q in range(2, d - 1)
                     if lib.is_prime_power(q) and d - q - 1 >= 1], reverse=True)[:3]
        arc_total = 0.35 * time_limit
        per = arc_total / max(1, 2 * len(qs))
        for idx, q in enumerate(qs):
            if per < 0.3:
                break
            s = d - q - 1
            m, pg_edges, pl, lp = _pg_adj(q)
            rel = [(v - m, u + m) for u, v in pg_edges]   # lines become the chosen side
            SA = _arc_run(s, m, pg_edges, per, seed * 1009 + idx * 2 + 1)
            SB = _arc_run(s, m, rel, per, seed * 1009 + idx * 2 + 2)
            n_c, e_c = _ext(m, pg_edges, pl, lp, SA, SB)
            consider(n_c, e_c)

    if D >= 3 and best_n > 2:
        n_arc = best_n

        # Stage 1: plain greedy fill.
        n_f, e_f = _fill(best_n, best[1], d, D, start + 0.5 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

        # Stage 2: cross-saturation followed by fill, each checked exactly.
        trial_rng = random.Random(seed * 31337 + d)
        chain_deadline = start + 0.62 * time_limit
        while time.monotonic() < chain_deadline:
            n_b, e_b = best
            e_sat = _cross_saturate(n_b, e_b, d, n_arc, trial_rng)
            if len(e_sat) == len(e_b):
                break
            n_s, e_s = _fill(n_b, e_sat, d, D, chain_deadline, trial_rng)
            consider(n_s, e_s)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main fallback search: annealed group voltage lifts.
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
