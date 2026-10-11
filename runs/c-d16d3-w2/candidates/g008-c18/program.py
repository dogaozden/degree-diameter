import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to all q+1 lines through P; for each j in S
# add a new B-vertex joined to all q+1 points on line j. Diameter stays 3.
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


def _arc_graph(m, edges, point_lines, S, line_points):
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity cover fill (diameter 3).
#
# A new vertex x on one side is at distance 2 from its own side only if its
# neighbourhood covers that whole side. Greedily pick such a cover among spare
# opposite-side vertices and accept x only if lib.is_valid still holds.
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
                g = sum(1 for u in adj[v] if u in uncovered)
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
# C engine: spare-transfer annealing for vertex insertion.
#
# The graph is kept bipartite with fixed sides and max degree d. The state is
# grown one vertex at a time. For each new vertex, simulated annealing minimises
# the number of vertex pairs at distance > D (bitset ball computation) using
# three degree-safe moves:
#   swap      : double edge swap (a-b, c-e  ->  a-e, c-b), degrees unchanged
#   add       : join two spare vertices on opposite sides
#   transfer  : move a spare slot: join spare x to y, drop edge y-z (z gets spare)
# plus a rare remove move. Whenever cost hits 0 the state is saved as the best.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int DEG, DIAM, CAP, W, N;
static int *side, *deg, *adj;
static uint64_t *bufA, *bufB;
static int *bside, *bdeg, *badj, bN, have_best;
static clock_t t_begin;
static double budget;

static double elapsed(void) { return (double)(clock() - t_begin) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long bad_pairs(void) {
    int WN = (N + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *r = nxt + (size_t)v * W;
            const uint64_t *cv = cur + (size_t)v * W;
            for (int w = 0; w < WN; w++) r[w] = cv[w];
            const int *av = adj + (size_t)v * DEG;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *cu = cur + (size_t)av[k] * W;
                for (int w = 0; w < WN; w++) r[w] |= cu[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *cv = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < WN; w++) c += popc(cv[w]);
        tot += N - c;
    }
    return tot / 2;
}

static int has_edge(int u, int v) {
    const int *a = adj + (size_t)u * DEG;
    for (int k = 0; k < deg[u]; k++) if (a[k] == v) return 1;
    return 0;
}
static void rem_from(int u, int v) {
    int *a = adj + (size_t)u * DEG;
    for (int k = 0; k < deg[u]; k++) {
        if (a[k] == v) { a[k] = a[--deg[u]]; return; }
    }
}
static void add_e(int u, int v) {
    adj[(size_t)u * DEG + deg[u]++] = v;
    adj[(size_t)v * DEG + deg[v]++] = u;
}
static void del_e(int u, int v) { rem_from(u, v); rem_from(v, u); }

typedef struct { int op, u, v; } Op;   /* op 0 = added edge, 1 = deleted edge */
static Op lg[16];
static int nlg;
static void L_add(int u, int v) {
    add_e(u, v); lg[nlg].op = 0; lg[nlg].u = u; lg[nlg].v = v; nlg++;
}
static void L_del(int u, int v) {
    del_e(u, v); lg[nlg].op = 1; lg[nlg].u = u; lg[nlg].v = v; nlg++;
}
static void undo_all(void) {
    while (nlg > 0) {
        nlg--;
        if (lg[nlg].op == 0) del_e(lg[nlg].u, lg[nlg].v);
        else add_e(lg[nlg].u, lg[nlg].v);
    }
}

static int find_spare(void) {
    int s = rndint(N);
    for (int i = 0; i < N; i++) {
        int v = s + i; if (v >= N) v -= N;
        if (deg[v] < DEG) return v;
    }
    return -1;
}
static int find_spare_opp(int x) {
    int s = rndint(N);
    for (int i = 0; i < N; i++) {
        int v = s + i; if (v >= N) v -= N;
        if (side[v] != side[x] && deg[v] < DEG && !has_edge(x, v)) return v;
    }
    return -1;
}

/* Double edge swap: a-b, c-e -> a-e, c-b (same-side a, c). Degrees preserved. */
static int move_swap(void) {
    int a = rndint(N);
    if (deg[a] == 0) return 0;
    int b = adj[(size_t)a * DEG + rndint(deg[a])];
    int c = rndint(N);
    if (c == a || side[c] != side[a] || deg[c] == 0) return 0;
    int e = adj[(size_t)c * DEG + rndint(deg[c])];
    if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
    L_del(a, b); L_del(c, e); L_add(a, e); L_add(c, b);
    return 1;
}

/* Join two spare vertices on opposite sides. */
static int move_add(void) {
    int x = find_spare();
    if (x < 0) return 0;
    int y = find_spare_opp(x);
    if (y < 0) return 0;
    L_add(x, y);
    return 1;
}

/* Spare transfer: join spare x to y (opposite side), drop y-z; z becomes spare. */
static int move_transfer(void) {
    int x = find_spare();
    if (x < 0) return 0;
    int y = -1;
    for (int t = 0; t < 32; t++) {
        int c = rndint(N);
        if (side[c] != side[x] && deg[c] > 0 && !has_edge(x, c)) { y = c; break; }
    }
    if (y < 0) return 0;
    int z = adj[(size_t)y * DEG + rndint(deg[y])];
    L_del(y, z);
    L_add(x, y);
    return 1;
}

static int move_remove(void) {
    int a = rndint(N);
    if (deg[a] == 0) return 0;
    int b = adj[(size_t)a * DEG + rndint(deg[a])];
    L_del(a, b);
    return 1;
}

static long long cur_cost;

/* Simulated annealing on bad_pairs. Returns 1 if the state becomes valid (cost 0). */
static int anneal(long long moves, double Th, double Tl) {
    cur_cost = bad_pairs();
    if (cur_cost == 0) return 1;
    for (long long it = 0; it < moves; it++) {
        if ((it & 127) == 0 && elapsed() > budget) break;
        double T = Th * pow(Tl / Th, (double)it / (double)moves);
        double r = rnd01();
        int ok;
        nlg = 0;
        if (r < 0.40) ok = move_swap();
        else if (r < 0.75) ok = move_add();
        else if (r < 0.97) ok = move_transfer();
        else ok = move_remove();
        if (!ok) continue;
        long long c2 = bad_pairs();
        long long dl = c2 - cur_cost;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur_cost = c2;
            nlg = 0;
            if (cur_cost == 0) return 1;
        } else {
            undo_all();
            nlg = 0;
        }
    }
    return cur_cost == 0;
}

static void save_best(void) {
    bN = N; have_best = 1;
    memcpy(bside, side, sizeof(int) * N);
    memcpy(bdeg, deg, sizeof(int) * N);
    memcpy(badj, adj, sizeof(int) * (size_t)N * DEG);
}
static void restore_best(void) {
    N = bN;
    memcpy(side, bside, sizeof(int) * N);
    memcpy(deg, bdeg, sizeof(int) * N);
    memcpy(adj, badj, sizeof(int) * (size_t)N * DEG);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    if (DEG < 1) { printf("1 0\n"); return 0; }
    rs ^= ((uint64_t)seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    t_begin = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0) { n0 = 0; m0 = 0; }
    int ecap = (m0 > DEG * DEG ? m0 : DEG * DEG) + 2;
    int *eu = malloc(sizeof(int) * ecap), *ev = malloc(sizeof(int) * ecap);
    int bad_input = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { bad_input = 1; m0 = i; break; }
    }
    if (n0 == 0) {
        if (DIAM >= 2) {
            n0 = 2 * DEG; m0 = 0;
            for (int a = 0; a < DEG; a++)
                for (int b = 0; b < DEG; b++) { eu[m0] = a; ev[m0] = DEG + b; m0++; }
        } else {
            n0 = 2; m0 = 1; eu[0] = 0; ev[0] = 1;
        }
    }

    CAP = n0 + 512;
    W = (CAP + 63) / 64;
    side = malloc(sizeof(int) * CAP);
    deg = calloc(CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG, sizeof(int));
    bufA = calloc((size_t)CAP * W, sizeof(uint64_t));
    bufB = calloc((size_t)CAP * W, sizeof(uint64_t));
    bside = malloc(sizeof(int) * CAP);
    bdeg = calloc(CAP, sizeof(int));
    badj = calloc((size_t)CAP * DEG, sizeof(int));

    N = n0;
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int i = 0; i < m0 && !bad_input; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { bad_input = 1; break; }
        if (has_edge(u, v)) continue;
        if (deg[u] >= DEG || deg[v] >= DEG) { bad_input = 1; break; }
        add_e(u, v);
    }
    if (!bad_input) {
        int *q = malloc(sizeof(int) * (N + 1));
        for (int s = 0; s < N && !bad_input; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt && !bad_input) {
                int u = q[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int v = adj[(size_t)u * DEG + k];
                    if (side[v] < 0) { side[v] = 1 - side[u]; q[qt++] = v; }
                    else if (side[v] == side[u]) bad_input = 1;
                }
            }
        }
        free(q);
    }
    if (bad_input) { printf("0 0\n"); return 0; }

    if (bad_pairs() == 0 || anneal(300000, 2.0, 0.1)) save_best();

    long long mv = 20000;
    int fails = 0;
    while (have_best && elapsed() < budget && N < CAP) {
        restore_best();
        side[N] = rndint(2);
        deg[N] = 0;
        N++;
        int ok = anneal(mv, 2.0, 0.1);
        if (ok) {
            save_best();
            fails = 0;
            mv = 20000;
        } else {
            fails++;
            if (fails % 2 == 0 && mv < 4000000) mv *= 2;
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    restore_best();
    long long m = 0;
    for (int u = 0; u < N; u++) if (side[u] == 0) m += deg[u];
    printf("%d %lld\n", N, m);
    for (int u = 0; u < N; u++) {
        if (side[u] != 0) continue;
        for (int k = 0; k < deg[u]; k++)
            printf("%d %d\n", u, adj[(size_t)u * DEG + k]);
    }
    return 0;
}
"""


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Algebraic starts (diameter 3): arc-extended projective planes, then cover fill.
    if D >= 3:
        cands = _arc_extensions(d, start + 0.12 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)
        if best_n > 2:
            n_f, e_f = _fill(best_n, best[1], d, D, start + 0.22 * time_limit,
                             random.Random(seed * 104729 + d))
            consider(n_f, e_f)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: C spare-transfer annealing grows the best valid graph.
    left = start + 0.80 * time_limit - time.monotonic() - 1.0
    if left > 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(left, 2)],
                            stdin_graph=best, timeout=left + 15.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
