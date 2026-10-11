import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (Python): arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. SA points get a new vertex joined
# to their q+1 lines (each line holds <= s of them); SB lines get a new vertex
# joined to their q+1 points (each point lies on <= s of them).
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy for the load-constrained set problem."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
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
            if len(cur) >= s:
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
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
    """Return (n, edges) candidates for the most promising prime powers q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    qs = qs[:3]
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
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
# Voltage-lift annealing (only used for D >= 4 as a cheap extra source).
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
# Stage 2 (C): incremental ILS that grows a valid bipartite graph by vertex
# insertion. A new vertex is attached to spare vertices of the opposite colour;
# its neighbourhood is pruned to a minimal valid set. Perturbation removes
# random vertices and re-grows; a state is kept only if the order did not drop.
# Validity is distance <= D between all alive pairs (checked by BFS).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 64

static int d, D, cap, nv, nalive;
static int *alive, *deg, *col, *adj, *vis, *qbuf, *cand;
static int vstamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double budget;
static clock_t t0;

typedef struct { int *alive, *deg, *col, *adj; int nv, nalive; } Snap;
static Snap S;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

/* Number of alive vertices within distance D of s (including s). */
static int bfs_count(int s) {
    if (++vstamp == 0x7fffffff) {
        memset(vis, 0, sizeof(int) * (size_t)cap);
        vstamp = 1;
    }
    int head = 0, tail = 0, cnt = 1;
    qbuf[tail++] = s;
    vis[s] = vstamp;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int end = tail;
        while (head < end) {
            int u = qbuf[head++];
            int *row = adj + (size_t)u * d;
            for (int i = 0; i < deg[u]; i++) {
                int w = row[i];
                if (vis[w] != vstamp) {
                    vis[w] = vstamp;
                    qbuf[tail++] = w;
                    cnt++;
                }
            }
        }
    }
    return cnt;
}

static int full_valid(void) {
    for (int v = 0; v < nv; v++) {
        if (!alive[v]) continue;
        if (bfs_count(v) != nalive) return 0;
    }
    return 1;
}

static void add_half(int a, int b) {
    adj[(size_t)a * d + deg[a]] = b;
    deg[a]++;
}

static void remove_half(int a, int b) {
    int *row = adj + (size_t)a * d;
    for (int i = 0; i < deg[a]; i++) {
        if (row[i] == b) {
            row[i] = row[deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void connect(int a, int b) { add_half(a, b); add_half(b, a); }
static void disconnect(int a, int b) { remove_half(a, b); remove_half(b, a); }

static void delete_vertex(int v) {
    for (int i = 0; i < deg[v]; i++) remove_half(adj[(size_t)v * d + i], v);
    deg[v] = 0;
    alive[v] = 0;
    nalive--;
}

static int alloc_slot(void) {
    for (int i = 0; i < nv; i++)
        if (!alive[i]) return i;
    if (nv < cap) return nv++;
    return -1;
}

static void snap_alloc(void) {
    S.alive = malloc(sizeof(int) * (size_t)cap);
    S.deg = malloc(sizeof(int) * (size_t)cap);
    S.col = malloc(sizeof(int) * (size_t)cap);
    S.adj = malloc(sizeof(int) * (size_t)cap * d);
}

static void snap_save(void) {
    memcpy(S.alive, alive, sizeof(int) * (size_t)cap);
    memcpy(S.deg, deg, sizeof(int) * (size_t)cap);
    memcpy(S.col, col, sizeof(int) * (size_t)cap);
    memcpy(S.adj, adj, sizeof(int) * (size_t)cap * d);
    S.nv = nv;
    S.nalive = nalive;
}

static void snap_restore(void) {
    memcpy(alive, S.alive, sizeof(int) * (size_t)cap);
    memcpy(deg, S.deg, sizeof(int) * (size_t)cap);
    memcpy(col, S.col, sizeof(int) * (size_t)cap);
    memcpy(adj, S.adj, sizeof(int) * (size_t)cap * d);
    nv = S.nv;
    nalive = S.nalive;
}

/* Try to add one vertex with a pruned neighbourhood. Returns 1 on success. */
static int try_add(void) {
    int c = rndint(2);
    int nc = 0;
    for (int v = 0; v < nv; v++)
        if (alive[v] && col[v] != c && deg[v] < d) cand[nc++] = v;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int k = nc < d ? nc : d;
    int x = alloc_slot();
    if (x < 0) return 0;
    alive[x] = 1;
    deg[x] = 0;
    col[x] = c;
    nalive++;
    for (int i = 0; i < k; i++) connect(x, cand[i]);
    if (bfs_count(x) != nalive) {
        for (int i = 0; i < k; i++) disconnect(x, cand[i]);
        alive[x] = 0;
        nalive--;
        return 0;
    }
    /* Prune neighbours that are not needed, keeping spare capacity elsewhere. */
    int order[MAXD];
    int m = deg[x];
    memcpy(order, adj + (size_t)x * d, sizeof(int) * (size_t)m);
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = order[i];
        order[i] = order[j];
        order[j] = t;
    }
    for (int i = 0; i < m; i++) {
        int u = order[i];
        disconnect(x, u);
        if (!full_valid()) connect(x, u);
    }
    return 1;
}

static int spare_total(void) {
    int s = 0;
    for (int v = 0; v < nv; v++)
        if (alive[v] && deg[v] < d) s++;
    return s;
}

/* Load a graph (with validity and bipartiteness checks). Returns 1 if valid. */
static int load_graph(int n, int m, const int *eu, const int *ev) {
    nv = n;
    nalive = n;
    for (int i = 0; i < cap; i++) {
        alive[i] = 0;
        deg[i] = 0;
        col[i] = -1;
    }
    for (int i = 0; i < n; i++) alive[i] = 1;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d) return 0;
        for (int k = 0; k < deg[u]; k++)
            if (adj[(size_t)u * d + k] == v) return 0;
        connect(u, v);
    }
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        qbuf[tail++] = s;
        while (head < tail) {
            int u = qbuf[head++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[(size_t)u * d + i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    qbuf[tail++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return full_valid();
}

int main(int argc, char **argv) {
    t0 = clock();
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    rs = 88172645463325252ULL ^ (seed * 2654435761ULL + 1234567ULL);
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0) n = 0;
    if (m < 0) m = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    int got = 0;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        eu[got] = a;
        ev[got] = b;
        got++;
    }
    m = got;

    cap = n + 4096;
    alive = calloc((size_t)cap, sizeof(int));
    deg = calloc((size_t)cap, sizeof(int));
    col = calloc((size_t)cap, sizeof(int));
    adj = calloc((size_t)cap * d, sizeof(int));
    vis = calloc((size_t)cap, sizeof(int));
    qbuf = calloc((size_t)cap, sizeof(int));
    cand = calloc((size_t)cap, sizeof(int));
    snap_alloc();

    int ok = (n > 0) && load_graph(n, m, eu, ev);
    if (!ok) {
        /* Fallback: K_{d,d}, valid for D >= 2. */
        int fn = 2 * d;
        int fm = d * d;
        int *fu = malloc(sizeof(int) * (size_t)fm);
        int *fv = malloc(sizeof(int) * (size_t)fm);
        int t = 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) {
                fu[t] = i;
                fv[t] = d + j;
                t++;
            }
        if (fn > cap) { printf("0 0\n"); return 0; }
        if (!load_graph(fn, fm, fu, fv)) { printf("0 0\n"); return 0; }
        free(fu);
        free(fv);
    }

    /* Iterated local search. */
    while (elapsed() < budget) {
        if (spare_total() == 0) break;
        snap_save();
        int before = nalive;
        int r = rndint(3);
        int good = 1;
        for (int k = 0; k < r && nalive > 1; k++) {
            int v;
            do { v = rndint(nv); } while (!alive[v]);
            delete_vertex(v);
        }
        if (r > 0 && !full_valid()) good = 0;
        if (good)
            for (int t = 0; t < 40; t++) try_add();
        if (!good || nalive < before) snap_restore();
    }

    /* Output compacted graph. */
    int *id = malloc(sizeof(int) * (size_t)(nv + 1));
    int k = 0;
    for (int v = 0; v < nv; v++) id[v] = alive[v] ? k++ : -1;
    int E = 0;
    for (int v = 0; v < nv; v++) {
        if (!alive[v]) continue;
        for (int i = 0; i < deg[v]; i++)
            if (adj[(size_t)v * d + i] > v) E++;
    }
    printf("%d %d\n", k, E);
    for (int v = 0; v < nv; v++) {
        if (!alive[v]) continue;
        for (int i = 0; i < deg[v]; i++) {
            int w = adj[(size_t)v * d + i];
            if (w > v) printf("%d %d\n", id[v], id[w]);
        }
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

    # Stage 1: arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    # For D >= 4: generalized quadrangle and a short voltage-lift annealing.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        rng = random.Random(seed)
        anneal_deadline = start + 0.3 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
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

    # Stage 2: C incremental ILS starting from the best graph found so far.
    c_budget = 0.85 * time_limit - (time.monotonic() - start) - 3.0
    if D >= 3 and d <= 64 and c_budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, int(seed) & 0x7FFFFFFF, f"{c_budget:.2f}"],
                            stdin_graph=best, timeout=c_budget + 10.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
