import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: growth by annealing on a bipartite graph.
#
# Input: a valid bipartite graph (n0 vertices). The engine keeps the bipartition,
# the degree bound d and diameter bound D as hard constraints. It repeatedly adds
# one new isolated vertex on the lighter side and anneals the edge set (add, delete,
# endpoint switch, double edge swap) to minimise the number of vertex pairs at
# distance > D. Each time it reaches zero bad pairs it records the graph and tries
# to grow again. The best valid graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GROW_MAX 64

typedef struct { int type, a, b, c, e; } Move;

static int DM = 1, DIAM = 3;
static int N = 0, CAP = 0, W = 1;
static int *deg = NULL, *adjl = NULL, *side = NULL;
static unsigned char *am = NULL;
static uint64_t *RA = NULL, *RB = NULL;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    adjl[u * DM + deg[u]] = v;
    deg[u]++;
    adjl[v * DM + deg[v]] = u;
    deg[v]++;
    am[u * CAP + v] = 1;
    am[v * CAP + u] = 1;
}

static void remove_nb(int u, int v) {
    int k;
    for (k = 0; k < deg[u]; k++) {
        if (adjl[u * DM + k] == v) {
            adjl[u * DM + k] = adjl[u * DM + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    remove_nb(u, v);
    remove_nb(v, u);
    am[u * CAP + v] = 0;
    am[v * CAP + u] = 0;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long bad_pairs(void) {
    uint64_t *P = RA, *Q = RB, *tmp;
    int v, k, r, w;
    for (v = 0; v < N; v++) {
        uint64_t *p = P + (size_t)v * W;
        for (w = 0; w < W; w++) p[w] = 0;
        p[v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            uint64_t *q = Q + (size_t)v * W;
            const uint64_t *p = P + (size_t)v * W;
            for (w = 0; w < W; w++) q[w] = p[w];
            for (k = 0; k < deg[v]; k++) {
                const uint64_t *pu = P + (size_t)adjl[v * DM + k] * W;
                for (w = 0; w < W; w++) q[w] |= pu[w];
            }
        }
        tmp = P; P = Q; Q = tmp;
    }
    {
        long long tot = 0;
        for (v = 0; v < N; v++) {
            const uint64_t *p = P + (size_t)v * W;
            int c = 0;
            for (w = 0; w < W; w++) c += popc64(p[w]);
            tot += N - c;
        }
        return tot / 2;
    }
}

static int eligible(int v, int s, int mode) {
    if (side[v] != s) return 0;
    return mode == 0 ? (deg[v] < DM) : (deg[v] > 0);
}

static int pick_vertex(int s, int mode) {
    int t, v, cnt = 0, pick = -1;
    for (t = 0; t < 32; t++) {
        v = rndint(N);
        if (eligible(v, s, mode)) return v;
    }
    for (v = 0; v < N; v++) {
        if (eligible(v, s, mode)) {
            cnt++;
            if (rndint(cnt) == 0) pick = v;
        }
    }
    return pick;
}

static int propose(Move *mv) {
    int t = rndint(100), a, b, c, e;
    if (t < 30) { /* ADD */
        a = pick_vertex(0, 0);
        b = pick_vertex(1, 0);
        if (a < 0 || b < 0 || am[a * CAP + b]) return 0;
        mv->type = 0; mv->a = a; mv->b = b;
        return 1;
    }
    if (t < 45) { /* DELETE */
        a = pick_vertex(0, 1);
        if (a < 0) return 0;
        mv->type = 1; mv->a = a; mv->b = adjl[a * DM + rndint(deg[a])];
        return 1;
    }
    if (t < 80) { /* SWITCH one endpoint */
        a = pick_vertex(0, 1);
        if (a < 0) return 0;
        b = adjl[a * DM + rndint(deg[a])];
        c = pick_vertex(1, 0);
        if (c < 0 || c == b || am[a * CAP + c]) return 0;
        mv->type = 2; mv->a = a; mv->b = b; mv->c = c;
        return 1;
    }
    /* DOUBLE SWAP: (a,b),(c,e) -> (a,e),(c,b); all degrees preserved */
    a = pick_vertex(0, 1);
    c = pick_vertex(0, 1);
    if (a < 0 || c < 0 || a == c) return 0;
    b = adjl[a * DM + rndint(deg[a])];
    e = adjl[c * DM + rndint(deg[c])];
    if (am[a * CAP + e] || am[c * CAP + b]) return 0;
    mv->type = 3; mv->a = a; mv->b = b; mv->c = c; mv->e = e;
    return 1;
}

static void apply_move(const Move *m) {
    switch (m->type) {
    case 0: add_edge(m->a, m->b); break;
    case 1: del_edge(m->a, m->b); break;
    case 2: del_edge(m->a, m->b); add_edge(m->a, m->c); break;
    default:
        del_edge(m->a, m->b);
        del_edge(m->c, m->e);
        add_edge(m->a, m->e);
        add_edge(m->c, m->b);
        break;
    }
}

static void undo_move(const Move *m) {
    switch (m->type) {
    case 0: del_edge(m->a, m->b); break;
    case 1: add_edge(m->a, m->b); break;
    case 2: del_edge(m->a, m->c); add_edge(m->a, m->b); break;
    default:
        del_edge(m->a, m->e);
        del_edge(m->c, m->b);
        add_edge(m->a, m->b);
        add_edge(m->c, m->e);
        break;
    }
}

/* Anneal the current graph until it has no bad pairs (returns 1) or time runs out (returns 0). */
static int anneal(double t_end) {
    const long long CYCLE = 200000;
    const double T0 = 1.5, T1 = 0.08;
    long long cur = bad_pairs();
    double f;
    if (cur == 0) return 1;
    f = pow(T1 / T0, 1.0 / (double)CYCLE);
    for (;;) {
        double T = T0;
        long long it;
        for (it = 0; it < CYCLE; it++) {
            Move mv;
            if ((it & 63) == 0 && now() >= t_end) return 0;
            if (propose(&mv)) {
                long long nc, delta;
                apply_move(&mv);
                nc = bad_pairs();
                delta = nc - cur;
                if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                    cur = nc;
                    if (cur == 0) return 1;
                } else {
                    undo_move(&mv);
                }
            }
            T *= f;
        }
    }
    return 0;
}

static int snapshot(int *bu, int *bv) {
    int m = 0, v, k;
    for (v = 0; v < N; v++) {
        for (k = 0; k < deg[v]; k++) {
            int u = adjl[v * DM + k];
            if (u > v) {
                bu[m] = v;
                bv[m] = u;
                m++;
            }
        }
    }
    return m;
}

int main(int argc, char **argv) {
    int d, D, n0, m0, i, k, ok = 1, best_n, best_m, c0, c1, s;
    unsigned long long seed;
    double budget;
    int *eu, *ev, *bu, *bv, *qu;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            m0 = i;
            break;
        }
    }
    DM = d > 1 ? d : 1;
    DIAM = D;
    CAP = n0 + GROW_MAX;
    W = (CAP + 63) / 64;
    deg = calloc((size_t)CAP, sizeof(int));
    side = calloc((size_t)CAP, sizeof(int));
    adjl = calloc((size_t)CAP * DM, sizeof(int));
    am = calloc((size_t)CAP * CAP, 1);
    RA = calloc((size_t)CAP * W, sizeof(uint64_t));
    RB = calloc((size_t)CAP * W, sizeof(uint64_t));
    bu = malloc(sizeof(int) * ((size_t)CAP * DM + 1));
    bv = malloc(sizeof(int) * ((size_t)CAP * DM + 1));
    qu = malloc(sizeof(int) * (size_t)CAP);
    N = n0;
    if (d < 1 || D < 1) ok = 0;
    for (i = 0; i < m0 && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v || am[u * CAP + v] ||
            deg[u] >= DM || deg[v] >= DM) {
            ok = 0;
        } else {
            add_edge(u, v);
        }
    }
    if (ok) {
        for (i = 0; i < N; i++) side[i] = -1;
        for (i = 0; i < N && ok; i++) {
            int qh = 0, qt = 0, x, y;
            if (side[i] >= 0) continue;
            side[i] = 0;
            qu[qt++] = i;
            while (qh < qt && ok) {
                x = qu[qh++];
                for (k = 0; k < deg[x]; k++) {
                    y = adjl[x * DM + k];
                    if (side[y] < 0) {
                        side[y] = 1 - side[x];
                        qu[qt++] = y;
                    } else if (side[y] == side[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    best_n = n0;
    best_m = m0;
    for (i = 0; i < m0; i++) {
        bu[i] = eu[i];
        bv[i] = ev[i];
    }
    if (ok && bad_pairs() == 0) {
        while (N < CAP && now() < budget) {
            c0 = 0;
            c1 = 0;
            for (i = 0; i < N; i++) {
                if (side[i]) c1++;
                else c0++;
            }
            s = (c0 <= c1) ? 0 : 1;
            side[N] = s;
            deg[N] = 0;
            N++;
            if (!anneal(budget)) break;
            best_m = snapshot(bu, bv);
            best_n = N;
        }
    }
    printf("%d %d\n", best_n, best_m);
    for (i = 0; i < best_m; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Asymmetric arc-extended projective plane graphs (diameter 3).
#
# Start from PG(2,q) incidence (points 0..m-1, lines m..2m-1). Pick a set SA of
# points, each line holding at most s of them, and a set TB of lines, each point
# lying on at most s of them, where s = d - q - 1 is the spare degree. The two
# sets are chosen independently. For P in SA add an A-vertex joined to the q+1
# lines through P. For j in TB add a B-vertex joined to the q+1 points on j.
# Every pair of new vertices shares a neighbour, and the diameter stays 3.
# ----------------------------------------------------------------------------

def _pg_data(q):
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]   # point -> lines through it (line indices)
    lp = [[] for _ in range(m)]   # line -> points on it (point indices)
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, pl, lp, index


def _ok(S, s, loads, m):
    cnt = [0] * m
    for P in S:
        for x in loads[P]:
            cnt[x] += 1
            if cnt[x] > s:
                return False
    return True


def _greedy(m, s, loads, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * m
        S = []
        for P in order:
            if all(cnt[x] < s for x in loads[P]):
                S.append(P)
                for x in loads[P]:
                    cnt[x] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, pl, lp, SA, TB):
    n = 2 * m + len(SA) + len(TB)
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    base = 2 * m + len(SA)
    for t, j in enumerate(TB):
        y = base + t
        for Q in lp[j]:
            E.append((Q, y))
    return n, E


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        m, edges, pl, lp, index = _pg_data(q)
        out.append((2 * m, edges))  # plain incidence graph
        s = d - q - 1
        if s < 1:
            continue
        SA = _greedy(m, s, pl, rng, 40, deadline)
        TB = _greedy(m, s, lp, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _ok(cs, s, pl, m):
                SA = cs
            if len(cs) > len(TB) and _ok(cs, s, lp, m):
                TB = cs
        out.append(_arc_graph(m, edges, pl, lp, SA, TB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    deadline = t0 + 0.3 * time_limit
    rng = random.Random(seed * 7919 + d)

    if D >= 3:
        for n_c, e_c in _arc_candidates(d, deadline, rng):
            consider(n_c, e_c)

    if D >= 4:
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

    # Growth search in C, started from the best construction. Skip when the
    # graph already meets the Moore bound (it cannot be beaten).
    if D >= 3 and best_n < lib.moore_bound(d, D):
        elapsed = time.monotonic() - t0
        budget = max(1.0, 0.6 * time_limit - elapsed)
        timeout = budget + 0.25 * time_limit
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=(best_n, best_e), timeout=timeout)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
