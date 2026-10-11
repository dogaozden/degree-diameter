import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a multiset SA of points. Each entry P gets a new vertex joined to the
#         q+1 lines through P. Every line may hold at most s entries of SA.
# B-side: a multiset SB of lines, symmetric.
#
# Diameter 3 holds for any multisets SA, SB (see the distance argument in the
# notes of earlier rounds). Old vertices keep their distances, since adding
# vertices only shortens paths.
#
# NEW IN THIS VERSION: a C engine ("exact-cost vertex insertion"). Adding a new
# vertex v to a valid graph can only create bad pairs that involve v, because
# old distances can only shrink. So the cost of inserting v with neighbour set
# S is exactly the number of vertices outside the radius-D ball of v. The C
# engine anneals S (size <= d, neighbours on the other side with spare degree)
# to make that cost zero, and repeats this while time remains.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXD 64
#define MAXE (MAXN * MAXD)

static uint64_t adjB[MAXN][MAXW];
static int deg[MAXN];
static int side[MAXN];
static int EU[MAXE], EV[MAXE];
static int cand[MAXN];
static int N = 0, M = 0;
static int DIAM = 3, DEGMAX = 3;
static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double wall_now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static void add_edge(int u, int v) {
    adjB[u][v >> 6] |= 1ULL << (v & 63);
    adjB[v][u >> 6] |= 1ULL << (u & 63);
    deg[u]++;
    deg[v]++;
    EU[M] = u;
    EV[M] = v;
    M++;
}

/* Number of vertices in 0..v NOT within distance DIAM of v, when v is the new
   vertex (index N) joined to the set S. Old vertices are assumed valid among
   themselves, so only pairs involving v can be bad. */
static int ball_cost(const int *S, int ns, int v) {
    int W = (v + 1 + 63) >> 6;
    uint64_t cur[MAXW], fr[MAXW], nxt[MAXW];
    memset(cur, 0, sizeof cur);
    memset(fr, 0, sizeof fr);
    cur[v >> 6] |= 1ULL << (v & 63);
    for (int i = 0; i < ns; i++) {
        int s = S[i];
        cur[s >> 6] |= 1ULL << (s & 63);
        fr[s >> 6] |= 1ULL << (s & 63);
    }
    for (int step = 2; step <= DIAM; step++) {
        memset(nxt, 0, sizeof nxt);
        for (int w = 0; w < W; w++) {
            uint64_t x = fr[w];
            while (x) {
                int b = __builtin_ctzll(x);
                x &= x - 1;
                int u = (w << 6) + b;
                for (int k = 0; k < W; k++) nxt[k] |= adjB[u][k];
            }
        }
        int any = 0;
        for (int k = 0; k < W; k++) {
            nxt[k] &= ~cur[k];
            cur[k] |= nxt[k];
            fr[k] = nxt[k];
            if (nxt[k]) any = 1;
        }
        if (!any) break;
    }
    int reach = 0;
    for (int k = 0; k < W; k++) reach += __builtin_popcountll(cur[k]);
    return (v + 1) - reach;
}

static int count_cands(int X) {
    int nc = 0;
    for (int v = 0; v < N; v++)
        if (side[v] != X && deg[v] < DEGMAX) nc++;
    return nc;
}

static int in_set(const int *S, int ns, int x) {
    for (int i = 0; i < ns; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Try to insert one new vertex on side X. Returns 1 on success. */
static int try_insert(int X, long iters, double T0) {
    int nc = 0;
    for (int v = 0; v < N; v++)
        if (side[v] != X && deg[v] < DEGMAX) cand[nc++] = v;
    if (nc == 0) return 0;
    int want = DEGMAX < nc ? DEGMAX : nc;
    int S[MAXD], old[MAXD];
    int ns = 0;
    while (ns < want) {
        int c = cand[rndint(nc)];
        if (!in_set(S, ns, c)) S[ns++] = c;
    }
    int v = N;
    int cur = ball_cost(S, ns, v);
    for (long it = 0; it < iters && cur != 0; it++) {
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.02;
        int nold = ns;
        memcpy(old, S, sizeof(int) * (size_t)ns);
        int r = rndint(3);
        if (r == 0 && ns < want) {
            int c = cand[rndint(nc)];
            if (in_set(S, ns, c)) continue;
            S[ns++] = c;
        } else if (r == 1 && ns > 1) {
            int i = rndint(ns);
            S[i] = S[--ns];
        } else {
            int i = rndint(ns);
            int c = cand[rndint(nc)];
            if (in_set(S, ns, c)) continue;
            S[i] = c;
        }
        int nc2 = ball_cost(S, ns, v);
        int delta = nc2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc2;
        } else {
            ns = nold;
            memcpy(S, old, sizeof(int) * (size_t)nold);
        }
    }
    if (cur != 0) return 0;
    side[v] = X;
    for (int i = 0; i < ns; i++) add_edge(v, S[i]);
    N++;
    return 1;
}

static int col[MAXN];
static int bq[MAXN];

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    long seed = argc > 3 ? atol(argv[3]) : 1;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    DEGMAX = d;
    DIAM = D;
    rng_state ^= (uint64_t)seed * 2654435761ULL + 12345ULL;
    if (rng_state == 0) rng_state = 1;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 0 || m < 0 || n > MAXN - 2 || m > MAXE) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        EU[i] = u;
        EV[i] = v;
    }

    N = n;
    M = 0;
    int ok = (DEGMAX >= 1 && DEGMAX <= MAXD);
    for (int i = 0; i < m && ok; i++) {
        int u = EU[i], v = EV[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if ((adjB[u][v >> 6] >> (v & 63)) & 1ULL) { ok = 0; break; }
        adjB[u][v >> 6] |= 1ULL << (v & 63);
        adjB[v][u >> 6] |= 1ULL << (u & 63);
        deg[u]++;
        deg[v]++;
    }
    for (int v = 0; v < n && ok; v++)
        if (deg[v] > DEGMAX) ok = 0;
    if (ok) {
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            bq[qt++] = s;
            while (qh < qt && ok) {
                int u = bq[qh++];
                for (int w = 0; w < n; w++) {
                    if (!((adjB[u][w >> 6] >> (w & 63)) & 1ULL)) continue;
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        bq[qt++] = w;
                    } else if (col[w] == col[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }
    for (int v = 0; v < n; v++) side[v] = col[v];
    M = m;

    double t0 = wall_now();
    while (wall_now() - t0 < tl && N < MAXN - 2) {
        int X = rndint(2);
        if (count_cands(X) == 0) {
            if (count_cands(1 - X) == 0) break;
            continue;
        }
        try_insert(X, 3000, 2.0);
    }

    printf("%d %d\n", N, M);
    for (int i = 0; i < M; i++) printf("%d %d\n", EU[i], EV[i]);
    return 0;
}
'''


def _c_insert(n, edges, d, D, seed, budget):
    """Run the C insertion engine on a valid graph; return (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=(n, edges), timeout=budget + 15.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Arc-extension construction (unchanged from parent).
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
    """Iterated greedy over multisets with every target hit <= s times."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
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
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Phase 1: arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    # Phase 2: generalized quadrangle (diameter 4) and voltage-lift search (D >= 4).
    if D >= 4 and time.monotonic() < start + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 4:
        deadline = start + 0.4 * time_limit
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

    # Phase 3: exact-cost vertex insertion in C on the best valid graph found.
    c_budget = start + 0.85 * time_limit - time.monotonic() - 3.0
    if c_budget >= 1.0:
        try:
            n2, e2 = _c_insert(best[0], best[1], d, D, seed, c_budget)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
