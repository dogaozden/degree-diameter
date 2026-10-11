import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXDEG 64

static int N, DD, DIA;
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static int col[MAXN];
static int dist[MAXN];
static int qu[MAXN];
static unsigned long long rs = 88172645463325252ULL;

static unsigned rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (unsigned)(rs >> 11);
}

static int read_graph(void) {
    int n, m, i;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 0 || n > MAXN - 64 || m < 0) return 0;
    N = n;
    for (i = 0; i < N; i++) deg[i] = 0;
    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) return 0;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) return 0;
        nb[u][deg[u]++] = v;
        nb[v][deg[v]++] = u;
    }
    return 1;
}

static int color_graph(void) {
    int s, h, t, k;
    for (s = 0; s < N; s++) col[s] = -1;
    for (s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        h = 0; t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qu[t++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int diam_ok(void) {
    int s, i, k;
    for (s = 0; s < N; s++) {
        int h = 0, t = 0;
        for (i = 0; i < N; i++) dist[i] = -1;
        qu[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int u = qu[h++];
            if (dist[u] >= DIA) continue;
            for (k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    qu[t++] = v;
                }
            }
        }
        if (t != N) return 0;
    }
    return 1;
}

/* Add a new vertex of colour c adjacent to cand[0..k-1]; keep it only if the diameter bound holds. */
static int attempt(int c, const int *cand, int k) {
    int x = N, i;
    if (x >= MAXN - 1) return 0;
    N++;
    deg[x] = 0;
    col[x] = c;
    for (i = 0; i < k; i++) {
        int v = cand[i];
        nb[v][deg[v]++] = x;
        nb[x][deg[x]++] = v;
    }
    if (diam_ok()) return 1;
    for (i = 0; i < k; i++) deg[cand[i]]--;
    deg[x] = 0;
    N--;
    return 0;
}

static void output(void) {
    int u, k, m = 0;
    for (u = 0; u < N; u++)
        for (k = 0; k < deg[u]; k++)
            if (nb[u][k] > u) m++;
    printf("%d %d\n", N, m);
    for (u = 0; u < N; u++)
        for (k = 0; k < deg[u]; k++)
            if (nb[u][k] > u) printf("%d %d\n", u, nb[u][k]);
}

int main(int argc, char **argv) {
    static int cand[MAXN];
    double budget;
    clock_t t0;
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIA = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 2654435761ULL + 12345ULL;
    budget = atof(argv[4]);
    if (DD < 1 || DD > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    if (!read_graph()) {
        printf("0 0\n");
        return 0;
    }
    if (N == 0) {
        N = 2;
        deg[0] = deg[1] = 1;
        nb[0][0] = 1;
        nb[1][0] = 0;
    }
    if (!color_graph() || !diam_ok()) {
        output();
        return 0;
    }
    t0 = clock();
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < budget) {
        int c = (int)(rnd() & 1u);
        int nc = 0, v, i, kmax, k;
        for (v = 0; v < N; v++)
            if (col[v] == 1 - c && deg[v] < DD) cand[nc++] = v;
        if (nc == 0) continue;
        for (i = nc - 1; i > 0; i--) {
            int j = (int)(rnd() % (unsigned)(i + 1));
            int tmp = cand[i];
            cand[i] = cand[j];
            cand[j] = tmp;
        }
        kmax = nc < DD ? nc : DD;
        if (rnd() & 1u) k = kmax;
        else k = 1 + (int)(rnd() % (unsigned)kmax);
        attempt(c, cand, k);
    }
    output();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). With spare
# s = d - q - 1 per old vertex: a point set SA gives A-vertices joined to the
# q+1 lines through each point (each line holds <= s points of SA); a line set
# SB gives B-vertices joined to the q+1 points on each line (each point lies on
# <= s lines of SB). SA and SB are chosen independently.
# Order = 2(q^2+q+1) + |SA| + |SB|. Diameter stays 3.
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so every target is hit by <= s of them."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one A-vertex per SA point and one B-vertex per SB line."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates for each prime power q with q + 1 <= d."""
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
        if _loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points):
            out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (D = 4).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """(order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        cands = _arc_candidates(d, start + 0.25 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.4 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts, for D >= 4 only.
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        anneal_deadline = start + 0.4 * time_limit
        while time.monotonic() < anneal_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C augmentation: try to add new vertices to the best graph, keeping diameter <= D.
    remaining = end - time.monotonic()
    if remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.5, 2)],
                             stdin_graph=best, timeout=remaining - 0.5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
