import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex augmentation with bitset ball covers.
#
# Given a valid bipartite graph with max degree d and diameter D, repeatedly
# try to add a new vertex x on a random side. x picks neighbours y (opposite
# side, spare degree) greedily so that the radius-(D-1) balls of the chosen
# neighbours cover every old vertex. Then every old vertex is within D of x,
# and old pairs only get closer, so the graph stays valid. Restarts with
# random tie-breaking keep the best graph found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXDEG 64
#define MAXM (MAXN * MAXDEG / 2)
#define FAILMAX 2000

typedef uint64_t u64;

static int DEG = 0, DIAM = 0;
static int N = 0, W = 1;
static int n0 = 0, m0 = 0;
static int adjn[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN], col0[MAXN];
static int EU[MAXM], EV[MAXM];
static int bEU[MAXM], bEV[MAXM];
static int bestN = 0, bestM = 0;
static u64 bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static u64 (*BALL)[MAXW] = bufA;
static u64 rs = 0x9E3779B97F4A7C15ULL;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int popc(u64 x) {
#if defined(__GNUC__)
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static double now_sec(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

/* BALL[v] = set of vertices within distance DIAM-1 of v (current graph). */
static void compute_balls(void) {
    W = (N + 63) >> 6;
    if (W == 0) W = 1;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) bufA[v][w] = 0;
        bufA[v][v >> 6] |= 1ULL << (v & 63);
    }
    u64 (*cur)[MAXW] = bufA, (*nx)[MAXW] = bufB;
    for (int k = 1; k <= DIAM - 1; k++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cur[v][w];
            for (int i = 0; i < adjn[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nx[v][w] |= cur[u][w];
            }
        }
        u64 (*t)[MAXW] = cur;
        cur = nx;
        nx = t;
    }
    BALL = cur;
}

/* Try to add one new vertex on colour 'side'. Returns 1 on success. */
static int try_add(int side) {
    u64 full[MAXW], cov[MAXW];
    int chosen[MAXDEG];
    int nch = 0;
    int done = 0;
    if (N >= MAXN) return 0;
    for (int w = 0; w < W; w++) { full[w] = 0; cov[w] = 0; }
    for (int v = 0; v < N; v++) full[v >> 6] |= 1ULL << (v & 63);

    while (nch < DEG) {
        int best = -1, bestg = 0, ties = 0;
        for (int y = 0; y < N; y++) {
            if (col[y] == side || adjn[y] >= DEG) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(BALL[y][w] & ~cov[w]);
            if (g > bestg) {
                bestg = g;
                best = y;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if ((int)(rnd() % (u64)ties) == 0) best = y;
            }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= BALL[best][w];
        done = 1;
        for (int w = 0; w < W; w++) {
            if ((cov[w] & full[w]) != full[w]) { done = 0; break; }
        }
        if (done) break;
    }
    if (!done || nch == 0) return 0;

    int x = N;
    col[x] = side;
    adjn[x] = 0;
    for (int i = 0; i < nch; i++) {
        int y = chosen[i];
        adj[x][adjn[x]++] = y;
        adj[y][adjn[y]++] = x;
    }
    N++;
    compute_balls();
    return 1;
}

static void reset_from_start(void) {
    N = n0;
    for (int v = 0; v < N; v++) { adjn[v] = 0; col[v] = col0[v]; }
    for (int i = 0; i < m0; i++) {
        int u = EU[i], v = EV[i];
        adj[u][adjn[u]++] = v;
        adj[v][adjn[v]++] = u;
    }
    compute_balls();
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < adjn[v]; i++) {
            int u = adj[v][i];
            if (u > v && m < MAXM) { bEU[m] = v; bEV[m] = u; m++; }
        }
    }
    bestN = N;
    bestM = m;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (u64)seed * 0xD1B54A32D192ED03ULL + 0x12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || n0 > MAXN || m0 < 0 || m0 > MAXM || DEG < 1 || DEG > MAXDEG || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= n0 || v < 0 || v >= n0 || u == v) { printf("0 0\n"); return 0; }
        EU[i] = u;
        EV[i] = v;
    }

    static int dg[MAXN];
    for (int v = 0; v < n0; v++) dg[v] = 0;
    for (int i = 0; i < m0; i++) { dg[EU[i]]++; dg[EV[i]]++; }
    for (int v = 0; v < n0; v++) {
        if (dg[v] > DEG) { printf("0 0\n"); return 0; }
    }

    /* Bipartition of the start graph. */
    N = n0;
    for (int v = 0; v < n0; v++) { adjn[v] = 0; col0[v] = -1; }
    for (int i = 0; i < m0; i++) {
        int u = EU[i], v = EV[i];
        adj[u][adjn[u]++] = v;
        adj[v][adjn[v]++] = u;
    }
    static int stackv[MAXN];
    int bad = 0;
    for (int s = 0; s < n0 && !bad; s++) {
        if (col0[s] >= 0) continue;
        col0[s] = 0;
        int sp = 0;
        stackv[sp++] = s;
        while (sp > 0 && !bad) {
            int u = stackv[--sp];
            for (int i = 0; i < adjn[u]; i++) {
                int v = adj[u][i];
                if (col0[v] < 0) {
                    col0[v] = 1 - col0[u];
                    stackv[sp++] = v;
                } else if (col0[v] == col0[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) { printf("0 0\n"); return 0; }

    bestN = n0;
    bestM = m0;
    for (int i = 0; i < m0; i++) { bEU[i] = EU[i]; bEV[i] = EV[i]; }

    double t0 = now_sec();
    double tend = t0 + budget * 0.9;
    while (now_sec() < tend) {
        reset_from_start();
        int fails = 0;
        while (fails < FAILMAX && N < MAXN) {
            int side = (int)(rnd() & 1ULL);
            if (try_add(side)) fails = 0;
            else fails++;
            if (now_sec() >= tend) break;
        }
        if (N > bestN) save_best();
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bEU[i], bEV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), with deletions.
# ----------------------------------------------------------------------------

_LS_ITERS = 12000


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


def _loads_ok(S, caps, nbr):
    """True if every target t is hit by <= caps[t] elements of S, where element x hits nbr[x]."""
    m = len(caps)
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(m))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target t is hit by <= caps[t] chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < caps[t] for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, caps, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the capacitated set problem."""
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= caps[t]:
                if not cur:
                    ok = False
                    break
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _best_side(m, caps, nbr, rng, deadline, seeds):
    """Best capacitated set found by greedy, supplied seeds, then local search."""
    cands = [_greedy_side(m, caps, nbr, rng, 12, deadline)]
    for S in seeds:
        if _loads_ok(S, caps, nbr):
            cands.append(list(S))
    start = max(cands, key=len)
    return _local_search(m, caps, nbr, start, rng, deadline, _LS_ITERS)


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pick_deletions(edges, m, r, rng):
    """Random matching of up to r PG incidences, as (point, line) pairs with line index 0..m-1."""
    inc = [(u, v - m) for u, v in edges]
    rng.shuffle(inc)
    usedP, usedL, R = set(), set(), []
    for P, L in inc:
        if len(R) >= r:
            break
        if P in usedP or L in usedL:
            continue
        usedP.add(P)
        usedL.add(L)
        R.append((P, L))
    return R


def _arc_graph(m, edges, R, point_lines, line_points, SA, SB):
    """PG incidence minus deleted matching R, plus one new A-vertex per SA point and one B-vertex per SB line."""
    Rset = set(R)
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = [(u, v) for u, v in edges if (u, v - m) not in Rset]
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 0 else []
        rs_ = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline:
            r = rs_[trial] if trial < len(rs_) else rng.choice(rs_)
            trial += 1
            R = _pick_deletions(edges, m, r, rng) if r > 0 else []
            delP = [0] * m
            delL = [0] * m
            for P, L in R:
                delP[P] += 1
                delL[L] += 1
            capL = [s + delL[L] for L in range(m)]
            capP = [s + delP[P] for P in range(m)]
            seeds = [conic] if not R else []
            SA = _best_side(m, capL, point_lines, rng, q_deadline, seeds)
            SB = _best_side(m, capP, line_points, rng, q_deadline, seeds)
            if not (_loads_ok(SA, capL, point_lines) and _loads_ok(SB, capP, line_points)):
                continue
            out.append(_arc_graph(m, edges, R, point_lines, line_points, SA, SB))
            if trial > 40:
                break
    out.sort(key=lambda t: -t[0])
    return out[:30]


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
    tl = float(time_limit)
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

    # Construction phase: arc-extended PG graphs (D >= 3), GQ (D >= 4).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.3 * tl, random.Random(seed * 7919 + d))
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.4 * tl:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing for the other diameters.
    if D != 3:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < start + 0.4 * tl:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, start + 0.4 * tl, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Augmentation phase: C engine adds vertices to the best valid graph.
    elapsed = time.monotonic() - start
    budget = 0.85 * tl - elapsed
    if budget > 0.5 and best_n >= 2:
        timeout = max(1.0, min(budget + 3.0, 0.95 * tl - elapsed))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                            stdin_graph=(best_n, best[1]), timeout=timeout)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
