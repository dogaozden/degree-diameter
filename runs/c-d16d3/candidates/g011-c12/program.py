import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealed vertex insertion / edge rewiring for bipartite graphs of
# max degree d and diameter <= D. The state is always tracked with its number
# of bad pairs (distance > D). Energy = bad - (number of active vertices), so
# the search prefers larger graphs and only accepts invalid intermediate states
# with annealing probability. The best valid state is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 1024
#define MAXW 16
#define MAXDEG 128
#define MAXLOG 8192
#define MAXEDGE 40000
#define EXTRA 160

static int d, D, nin, NV, W, nact;
static int active[MAXV], side[MAXV], deg[MAXV];
static int nb[MAXV][MAXDEG];
static unsigned char A[MAXV][MAXV];
static uint64_t BUF[2][MAXV][MAXW];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    A[u][v] = A[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void remove_from(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (nb[u][k] == v) {
            nb[u][k] = nb[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    A[u][v] = A[v][u] = 0;
    remove_from(u, v);
    remove_from(v, u);
}

/* Operation log for undo. */
enum { OP_ADD = 1, OP_DEL = 2, OP_ACT = 3, OP_DEACT = 4 };
typedef struct { int t, u, v; } Op;
static Op lg[MAXLOG];
static int nlg = 0;

static void do_op(int t, int u, int v) {
    if (nlg >= MAXLOG - 1) return;
    lg[nlg].t = t; lg[nlg].u = u; lg[nlg].v = v; nlg++;
    switch (t) {
        case OP_ADD: add_edge(u, v); break;
        case OP_DEL: del_edge(u, v); break;
        case OP_ACT: active[u] = 1; nact++; break;
        case OP_DEACT: active[u] = 0; nact--; break;
    }
}

static void undo_all(void) {
    while (nlg > 0) {
        Op o = lg[--nlg];
        switch (o.t) {
            case OP_ADD: del_edge(o.u, o.v); break;
            case OP_DEL: add_edge(o.u, o.v); break;
            case OP_ACT: active[o.u] = 0; nact--; break;
            case OP_DEACT: active[o.u] = 1; nact++; break;
        }
    }
}

/* Number of unordered active pairs at distance > D. */
static long evaluate(void) {
    int c = 0;
    for (int v = 0; v < NV; v++) if (active[v]) {
        for (int w = 0; w < W; w++) BUF[0][v][w] = 0;
        BUF[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        int s = c, z = c ^ 1;
        for (int v = 0; v < NV; v++) if (active[v]) {
            for (int w = 0; w < W; w++) BUF[z][v][w] = BUF[s][v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) BUF[z][v][w] |= BUF[s][u][w];
            }
        }
        c = z;
    }
    long total = 0;
    for (int v = 0; v < NV; v++) if (active[v]) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += pop64(BUF[c][v][w]);
        total += (long)(nact - pc);
    }
    return total / 2;
}

static int pick_active(void) {
    for (int t = 0; t < 100000; t++) {
        int v = rndint(NV);
        if (active[v]) return v;
    }
    return -1;
}

static int try_add_edge(void) {
    for (int t = 0; t < 50; t++) {
        int u = pick_active(); if (u < 0) return 0;
        int v = pick_active(); if (v < 0) return 0;
        if (u == v || side[u] == side[v] || A[u][v]) continue;
        if (deg[u] >= d || deg[v] >= d) continue;
        do_op(OP_ADD, u, v);
        return 1;
    }
    return 0;
}

static int try_del_edge(void) {
    for (int t = 0; t < 50; t++) {
        int u = pick_active(); if (u < 0) return 0;
        if (deg[u] == 0) continue;
        int v = nb[u][rndint(deg[u])];
        do_op(OP_DEL, u, v);
        return 1;
    }
    return 0;
}

static int try_activate(void) {
    int v = -1;
    for (int t = 0; t < 200; t++) {
        int c = rndint(NV);
        if (!active[c]) { v = c; break; }
    }
    if (v < 0) return 0;
    do_op(OP_ACT, v, 0);
    int cand[MAXV];
    int nc = 0;
    for (int w = 0; w < NV; w++)
        if (active[w] && w != v && side[w] != side[v] && deg[w] < d) cand[nc++] = w;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = cand[i]; cand[i] = cand[j]; cand[j] = tmp;
    }
    int want = 1 + rndint(d);
    for (int i = 0; i < nc && i < want && deg[v] < d; i++) {
        int w = cand[i];
        if (deg[w] < d) do_op(OP_ADD, v, w);
    }
    return 1;
}

static int try_deactivate(void) {
    if (nact <= 2) return 0;
    int v = pick_active();
    if (v < 0) return 0;
    while (deg[v] > 0) do_op(OP_DEL, v, nb[v][deg[v] - 1]);
    do_op(OP_DEACT, v, 0);
    return 1;
}

static int bestN = -1, bestM = 0;
static int *bestE = NULL;

static void save_best(void) {
    int idx[MAXV];
    int k = 0;
    for (int v = 0; v < NV; v++) idx[v] = active[v] ? k++ : -1;
    int m = 0;
    for (int v = 0; v < NV; v++) if (active[v]) {
        for (int j = 0; j < deg[v]; j++) {
            int u = nb[v][j];
            if (u > v) {
                bestE[2 * m] = idx[v];
                bestE[2 * m + 1] = idx[u];
                m++;
            }
        }
    }
    bestN = k;
    bestM = m;
}

static int EU[MAXEDGE], EV[MAXEDGE];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;

    int min_ = 0;
    nin = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (d < 1 || D < 1 || d > MAXDEG || nin < 0 || nin > MAXV - 2) {
        printf("0 0\n");
        return 0;
    }
    NV = nin + EXTRA;
    if (NV > MAXV) NV = MAXV;
    if (NV < 2) NV = 2;
    W = (NV + 63) / 64;

    int ne = 0;
    for (int i = 0; i < min_; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (ne < MAXEDGE && u >= 0 && u < nin && v >= 0 && v < nin && u != v) {
            EU[ne] = u; EV[ne] = v; ne++;
        }
    }

    /* Bipartition of the input by propagation over the edge list. */
    int col[MAXV];
    for (int i = 0; i < NV; i++) col[i] = -1;
    for (int s = 0; s < nin; s++) if (col[s] < 0) {
        col[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int e = 0; e < ne; e++) {
                int a = EU[e], b = EV[e];
                if (col[a] >= 0 && col[b] < 0) { col[b] = 1 - col[a]; changed = 1; }
                else if (col[b] >= 0 && col[a] < 0) { col[a] = 1 - col[b]; changed = 1; }
            }
        }
    }
    for (int i = 0; i < NV; i++) side[i] = (i < nin) ? (col[i] > 0 ? 1 : 0) : (i & 1);

    nact = 0;
    for (int i = 0; i < nin; i++) { active[i] = 1; nact++; }
    for (int e = 0; e < ne; e++) {
        int u = EU[e], v = EV[e];
        if (side[u] == side[v] || A[u][v] || deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }
    if (nin == 0) {
        active[0] = active[1] = 1;
        nact = 2;
        add_edge(0, 1);
    }

    bestE = (int *)malloc(sizeof(int) * 2 * (size_t)(NV * d + 2));
    if (!bestE) { printf("0 0\n"); return 0; }

    long cur_bad = evaluate();
    if (cur_bad == 0) save_best();

    clock_t t0 = clock();
    double T0 = 1.2, T1 = 0.02, T = T0;
    long it = 0;
    while (1) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
            double f = el / tl;
            T = T0 * pow(T1 / T0, f);
        }
        it++;
        int old_nact = nact;
        long old_bad = cur_bad;
        nlg = 0;
        int r = rndint(100);
        int ok;
        if (r < 30) ok = try_add_edge();
        else if (r < 45) ok = try_del_edge();
        else if (r < 70) {
            ok = try_del_edge();
            if (ok) try_add_edge();
        }
        else if (r < 90) ok = try_activate();
        else ok = try_deactivate();

        if (!ok) { undo_all(); nlg = 0; continue; }

        long nbad = evaluate();
        double dE = (double)(nbad - old_bad) - (double)(nact - old_nact);
        if (dE <= 0 || rnd01() < exp(-dE / T)) {
            cur_bad = nbad;
            nlg = 0;
            if (cur_bad == 0 && nact > bestN) save_best();
        } else {
            undo_all();
            nlg = 0;
        }
    }

    if (bestN < 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A vertex per point of S (joined to its pencil) and a new B per line of S."""
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
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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


# ----------------------------------------------------------------------------
# C search wrapper.
# ----------------------------------------------------------------------------

def _c_search(d, D, start_graph, seed, end_at):
    """Run the C annealer from start_graph until end_at (monotonic clock). Returns (n, edges) or None."""
    budget = end_at - time.monotonic() - 2.5
    if budget < 1.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed) % 2_000_000_011, f"{budget:.2f}"],
                        stdin_graph=start_graph, timeout=budget + 2.0)
        return lib.parse_graph_text(out)
    except Exception:
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

    if D == 3:
        # New search: C annealing that inserts vertices and rewires edges
        # from the best construction. Skip if already at the Moore bound.
        if best_n < lib.moore_bound(d, D):
            res = _c_search(d, D, best, seed, start + 0.85 * time_limit)
            if res is not None:
                consider(res[0], res[1])
    else:
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
