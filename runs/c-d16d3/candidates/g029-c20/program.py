import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite grow-and-anneal search.
#
# Starts from a valid graph (the Python constructions), keeps the bipartition
# fixed, and repeatedly adds one vertex to the smaller side once the current
# graph is valid. Between growths it anneals over edge moves (add an edge
# between spare-capacity vertices, or rewire one end of an edge), minimising the
# number of vertex pairs at distance > D. Output is the largest valid graph seen.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define STALL 30000LL

static int d, D;
static int N, NCAP, WMAX;
static int *col, *deg, *adj;
static int *bdeg, *badj, bestN;
static int *sp0, *sp1;
static u64 *bufA, *bufB;
static int cost_now;
static double T = 0.5;
static u64 rs = 1;

static u64 rnext(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static double rnd01(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { return (int)(rnext() % (u64)n); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    int base = a * d;
    for (int i = 0; i < deg[a]; i++)
        if (adj[base + i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a * d + deg[a]++] = b;
    adj[b * d + deg[b]++] = a;
}

static void rem_nbr(int a, int b) {
    int base = a * d;
    for (int i = 0; i < deg[a]; i++) {
        if (adj[base + i] == b) {
            adj[base + i] = adj[base + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    rem_nbr(a, b);
    rem_nbr(b, a);
}

/* Number of unordered vertex pairs at distance > D. */
static int cost_eval(void) {
    int Wn = (N + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)Wn);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < D; s++) {
        for (int v = 0; v < N; v++) {
            u64 *r = nxt + (size_t)v * Wn;
            const u64 *c = cur + (size_t)v * Wn;
            memcpy(r, c, sizeof(u64) * (size_t)Wn);
            int base = v * d;
            for (int i = 0; i < deg[v]; i++) {
                const u64 *q = cur + (size_t)adj[base + i] * Wn;
                for (int w = 0; w < Wn; w++) r[w] |= q[w];
            }
        }
        u64 *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        const u64 *r = cur + (size_t)v * Wn;
        int c = 0;
        for (int w = 0; w < Wn; w++) c += pc64(r[w]);
        miss += N - c;
    }
    return (int)(miss / 2);
}

static int collect_spare(int c, int *out) {
    int k = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == c && deg[v] < d) out[k++] = v;
    return k;
}

static void move_add(void) {
    int n0 = collect_spare(0, sp0);
    int n1 = collect_spare(1, sp1);
    if (n0 == 0 || n1 == 0) return;
    for (int t = 0; t < 20; t++) {
        int x = sp0[rndint(n0)];
        int y = sp1[rndint(n1)];
        if (!has_edge(x, y)) {
            add_edge(x, y);
            cost_now = cost_eval();  /* adding an edge never increases the cost */
            return;
        }
    }
}

static void move_rewire(void) {
    int u = rndint(N);
    if (deg[u] == 0) return;
    int v = adj[u * d + rndint(deg[u])];
    int n = collect_spare(col[v], sp0);
    if (n == 0) return;
    int w = sp0[rndint(n)];
    if (w == v || has_edge(u, w)) return;
    del_edge(u, v);
    add_edge(u, w);
    int c2 = cost_eval();
    int delta = c2 - cost_now;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        cost_now = c2;
    } else {
        del_edge(u, w);
        add_edge(u, v);
    }
}

static void save_best(void) {
    bestN = N;
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(badj, adj, sizeof(int) * (size_t)N * (size_t)d);
}

static void restore_best(void) {
    N = bestN;
    memcpy(deg, bdeg, sizeof(int) * (size_t)N);
    memcpy(adj, badj, sizeof(int) * (size_t)N * (size_t)d);
}

static void grow(void) {
    int c0 = 0, c1 = 0;
    for (int v = 0; v < N; v++) {
        if (col[v] == 0) c0++;
        else c1++;
    }
    col[N] = (c0 <= c1) ? 0 : 1;
    deg[N] = 0;
    N++;
}

static void set_complete(void) {
    N = 2 * d;
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        col[v] = (v < d) ? 0 : 1;
    }
    for (int a = 0; a < d; a++)
        for (int b = d; b < 2 * d; b++)
            add_edge(a, b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    if (d < 1) return 1;
    rs = (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t c0 = clock();
    time_t w0 = time(NULL);

    int nin = 0, mIn = 0;
    if (scanf("%d %d", &nin, &mIn) != 2) { nin = 0; mIn = 0; }
    if (nin < 0) nin = 0;
    if (mIn < 0) mIn = 0;
    int *eu = malloc(sizeof(int) * (size_t)(mIn + 1));
    int *ev = malloc(sizeof(int) * (size_t)(mIn + 1));
    int mRead = 0;
    for (int i = 0; i < mIn; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= nin || b >= nin) continue;
        eu[mRead] = a;
        ev[mRead] = b;
        mRead++;
    }

    NCAP = (nin > 2 * d ? nin : 2 * d) + 4000;
    WMAX = (NCAP + 63) >> 6;
    col = malloc(sizeof(int) * (size_t)NCAP);
    deg = malloc(sizeof(int) * (size_t)NCAP);
    bdeg = malloc(sizeof(int) * (size_t)NCAP);
    sp0 = malloc(sizeof(int) * (size_t)NCAP);
    sp1 = malloc(sizeof(int) * (size_t)NCAP);
    adj = malloc(sizeof(int) * (size_t)NCAP * (size_t)d);
    badj = malloc(sizeof(int) * (size_t)NCAP * (size_t)d);
    bufA = malloc(sizeof(u64) * (size_t)NCAP * (size_t)WMAX);
    bufB = malloc(sizeof(u64) * (size_t)NCAP * (size_t)WMAX);

    N = nin;
    for (int v = 0; v < N; v++) { deg[v] = 0; col[v] = -1; }
    for (int i = 0; i < mRead; i++) {
        int a = eu[i], b = ev[i];
        if (a == b || deg[a] >= d || deg[b] >= d || has_edge(a, b)) continue;
        add_edge(a, b);
    }

    /* Bipartite 2-colouring; fall back to K_{d,d} if the input is not bipartite. */
    int ok = (N > 0);
    int *queue = sp1;
    for (int s = 0; s < N && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt && ok) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u * d + i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    queue[qt++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) set_complete();

    cost_now = cost_eval();
    bestN = 0;
    if (cost_now == 0) save_best();

    long long stall = 0, iters = 0;
    double stopWall = floor(tl) - 1.0;
    while (1) {
        if ((iters & 63) == 0) {
            if ((double)(clock() - c0) > tl * (double)CLOCKS_PER_SEC) break;
            if (difftime(time(NULL), w0) >= stopWall) break;
        }
        iters++;
        if (cost_now == 0) {
            save_best();
            if (N + 1 >= NCAP) break;
            grow();
            cost_now = cost_eval();
            stall = 0;
            T = 0.2 + 0.8 * rnd01();
            continue;
        }
        if (++stall > STALL) {
            stall = 0;
            T = 0.2 + 0.8 * rnd01();
            if (bestN > 0) {
                restore_best();
                cost_now = cost_eval();
            }
            continue;
        }
        if (rnd01() < 0.25) move_add();
        else move_rewire();
    }

    if (bestN == 0) {
        set_complete();
        save_best();
    }
    long long M = 0;
    for (int v = 0; v < bestN; v++) M += bdeg[v];
    M /= 2;
    printf("%d %lld\n", bestN, M);
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bdeg[v]; i++) {
            int u = badj[v * d + i];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (projective-plane arc extensions, GQ, voltage lifts).
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A vertex per element of S (joined to its lines) and a new B vertex per element of S (joined to its points)."""
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


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
# Build: Python constructions as a safe start, then the C grow-and-anneal search.
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
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Phase 1a: arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        arc_deadline = t0 + 0.15 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Phase 1b: generalized quadrangle (diameter 4).
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Phase 1c: short annealed voltage lifts.
    lift_deadline = t0 + 0.25 * time_limit
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < lift_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: C engine grows the best valid graph and anneals to add vertices.
    elapsed = time.monotonic() - t0
    budget = time_limit - elapsed - 8.0
    if budget >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
