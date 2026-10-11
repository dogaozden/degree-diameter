import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: voltage annealing over bi-Cayley lifts of a semidirect product.
#
# Base: NB vertices per side, DEG darts per base vertex (a DEG-regular bipartite
# base made of DEG random permutations). Group: Z_m x|_r Z_k with order GO,
# chosen at random among all valid (k, r). The lift has 2*NB*GO vertices.
#
# Cost: lift is an automorphism-transitive cover on each fibre, so the
# distance-<=DIAM ball of one representative per base vertex on each side is
# enough. cost = total number of vertices outside those balls. cost == 0 means
# the lift is a valid graph. Simulated annealing on the voltages, with random
# restarts (new group, new base, new voltages) after a stall.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define MAXD 16
#define MAXND 256
#define MAXG 2048
#define MAXB 8
#define MAXSK 24

static int DEG, DIAM, NB, GO;
static int SM, SK, SR;
static int POWR[MAXSK];
static int nv;
static int adjv[MAXV][MAXD];
static int dgr[MAXV];
static int du[MAXND], dvv[MAXND], dgv[MAXND];
static int ND;
static int dist_[MAXV], queue_[MAXV];
static int optSK[MAXG], optR[MAXG], nopt;
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void enum_groups(void) {
    nopt = 0;
    for (int sk = 1; sk <= MAXSK && sk <= GO; sk++) {
        if (GO % sk) continue;
        int sm = GO / sk;
        if (sm == 1) {
            if (nopt < MAXG) { optSK[nopt] = sk; optR[nopt] = 0; nopt++; }
            continue;
        }
        for (int r = 1; r < sm; r++) {
            if (gcd_i(r, sm) != 1) continue;
            if (powmod_i(r, sk, sm) != 1) continue;
            if (nopt < MAXG) { optSK[nopt] = sk; optR[nopt] = r; nopt++; }
        }
    }
}

static void set_group(int idx) {
    SK = optSK[idx];
    SR = optR[idx];
    SM = GO / SK;
    long long p = 1 % SM;
    for (int b = 0; b < SK; b++) {
        POWR[b] = (int)p;
        p = p * SR % SM;
    }
}

/* element (a,b) coded a*SK+b; (a,b)(c,d) = (a + r^b c, b + d) */
static int gmul(int x, int y) {
    int a = x / SK, b = x % SK, c = y / SK, d = y % SK;
    int aa = (a + POWR[b] * c) % SM;
    return aa * SK + (b + d) % SK;
}

static void random_instance(void) {
    set_group(rnd(nopt));
    ND = DEG * NB;
    for (int j = 0; j < DEG; j++) {
        int p[MAXB];
        for (int i = 0; i < NB; i++) p[i] = i;
        for (int i = NB - 1; i > 0; i--) {
            int k = rnd(i + 1);
            int t = p[i];
            p[i] = p[k];
            p[k] = t;
        }
        for (int i = 0; i < NB; i++) {
            int t = j * NB + i;
            du[t] = i;
            dvv[t] = p[i];
            dgv[t] = rnd(GO);
        }
    }
}

static int has_edge(int a, int b) {
    for (int i = 0; i < dgr[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

/* A-vertex (i,x) has index i*GO+x; B-vertex (j,y) has index NB*GO+j*GO+y.
   Dart (u,v,g) joins (u,x) to (v, x*g) for every x in the group. */
static void build_graph(void) {
    nv = 2 * NB * GO;
    for (int v = 0; v < nv; v++) dgr[v] = 0;
    for (int t = 0; t < ND; t++) {
        for (int x = 0; x < GO; x++) {
            int a = du[t] * GO + x;
            int b = NB * GO + dvv[t] * GO + gmul(x, dgv[t]);
            if (dgr[a] >= MAXD || dgr[b] >= MAXD) continue;
            if (has_edge(a, b)) continue;
            adjv[a][dgr[a]++] = b;
            adjv[b][dgr[b]++] = a;
        }
    }
}

static long long eval_cost(void) {
    build_graph();
    long long cost = 0;
    for (int s = 0; s < 2 * NB; s++) {
        int src = (s < NB) ? s * GO : NB * GO + (s - NB) * GO;
        for (int v = 0; v < nv; v++) dist_[v] = -1;
        int qh = 0, qt = 0;
        queue_[qt++] = src;
        dist_[src] = 0;
        while (qh < qt) {
            int u = queue_[qh++];
            if (dist_[u] >= DIAM) continue;
            for (int i = 0; i < dgr[u]; i++) {
                int w = adjv[u][i];
                if (dist_[w] < 0) {
                    dist_[w] = dist_[u] + 1;
                    queue_[qt++] = w;
                }
            }
        }
        cost += nv - qt;
    }
    return cost;
}

static void print_graph(void) {
    long long m = 0;
    for (int v = 0; v < nv; v++) m += dgr[v];
    m /= 2;
    printf("%d %lld\n", nv, m);
    for (int v = 0; v < nv; v++)
        for (int i = 0; i < dgr[v]; i++)
            if (v < adjv[v][i]) printf("%d %d\n", v, adjv[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    NB = atoi(argv[5]);
    GO = atoi(argv[6]);
    long stallLim = (argc >= 8) ? atol(argv[7]) : 6000;
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || NB < 1 || NB > MAXB ||
        GO < 1 || GO > MAXG || 2 * NB * GO > MAXV || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    enum_groups();
    if (nopt == 0) {
        printf("0 0\n");
        return 0;
    }

    clock_t c0 = clock();
    int found = 0;
    while (!found) {
        double frac = (double)(clock() - c0) / CLOCKS_PER_SEC / tl;
        if (frac >= 1.0) break;
        random_instance();
        long long cur = eval_cost();
        long long bestRun = cur;
        long stall = 0;
        while (cur > 0) {
            frac = (double)(clock() - c0) / CLOCKS_PER_SEC / tl;
            if (frac >= 1.0) break;
            if (stall > stallLim) break;
            int t = rnd(ND);
            int old = dgv[t];
            int nw = old;
            if (GO > 1) nw = (old + 1 + rnd(GO - 1)) % GO;
            dgv[t] = nw;
            long long c2 = eval_cost();
            double T = (0.3 + 0.03 * (double)cur) * (1.0 - frac) + 0.02;
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                dgv[t] = old;
            }
            if (c2 < bestRun) {
                bestRun = c2;
                stall = 0;
            } else {
                stall++;
            }
        }
        if (cur == 0) found = 1;
    }

    if (found) {
        print_graph();
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _cand_matrix(cand_balls, n):
    """Boolean matrix M[i, w] = 1 iff vertex w lies in the ball of candidate i."""
    nb = (n + 7) // 8
    buf = b"".join(x.to_bytes(nb, "little") for x in cand_balls)
    arr = np.frombuffer(buf, dtype=np.uint8).reshape(len(cand_balls), nb)
    return np.unpackbits(arr, axis=1, bitorder="little")[:, :n].astype(bool)


def _weighted_cover(B, cand_ids, n, d, nrng, randomize):
    """Hardest-first weighted set cover: rare uncovered vertices weigh more."""
    k = B.shape[0]
    uncov = np.ones(n, dtype=bool)
    avail = np.ones(k, dtype=bool)
    chosen = []
    for _ in range(d):
        if not uncov.any():
            break
        sub = B[:, uncov]
        cnt = sub.sum(axis=0)
        if (cnt == 0).any():
            return None
        w = 1.0 / cnt
        score = sub.astype(np.float64) @ w
        if randomize:
            score = score * (1.0 + 0.08 * nrng.random(k))
        score[~avail] = -1.0
        i = int(np.argmax(score))
        if score[i] <= 0:
            break
        avail[i] = False
        chosen.append(cand_ids[i])
        uncov &= ~B[i]
    return chosen if not uncov.any() else None


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _local_cover(cands, ball, full, d, rng, iters, deadline):
    """Plateau-walking swap search for a cover of `full` by at most d candidates."""
    pool = list(cands)
    if not pool:
        return None
    k = min(d, len(pool))
    chosen = rng.sample(pool, k)
    union = 0
    for s in chosen:
        union |= ball[s]
    if union == full:
        return chosen
    score = union.bit_count()
    for _ in range(iters):
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        s = rng.choice(pool)
        if s in chosen:
            continue
        trial = chosen[:]
        trial[i] = s
        u = 0
        for t in trial:
            u |= ball[t]
        sc = u.bit_count()
        if sc >= score:
            chosen, score = trial, sc
            if u == full:
                return chosen
    return None


def _find_cover(cands, ball, n, full, d, rng, deadline):
    """Try weighted covers, then greedy, then swap search."""
    B = _cand_matrix([ball[s] for s in cands], n)
    nrng = np.random.default_rng(rng.randrange(1 << 30))
    for attempt in range(12):
        if time.monotonic() >= deadline:
            return None
        chosen = _weighted_cover(B, cands, n, d, nrng, attempt > 0)
        if chosen:
            return chosen
    for attempt in range(60):
        if time.monotonic() >= deadline:
            return None
        chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
        if chosen:
            return chosen
    if time.monotonic() < deadline:
        return _local_cover(cands, ball, full, d, rng, 400, deadline)
    return None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = _find_cover(cands, ball, n, full, d, rng, deadline)
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
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


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _volt_run(d, D, seed, nb, go, budget):
    """Run the C voltage search for base size nb and group order go; return parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", nb, go, 6000],
                    stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(out)


def _consider(state, d, D, n, e):
    """Keep (n, e) if it is valid and larger than the current best."""
    if n > state["best"][0] and lib.is_valid(n, e, d, D):
        state["best"] = (n, e)


def _lift_loop(d, D, state, deadline, rng, consider):
    """Python lift search: non-cyclic group lifts, Haar graphs, cyclic lifts."""
    group_p = 0.85 if D >= 5 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        best_n = state["best"][0]
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m


def _voltage_phase(d, D, seed, state, vend, rng, consider):
    """Repeated short C voltage searches over base sizes, each aimed just above the best order."""
    tries = {1: 0, 2: 0, 3: 0, 4: 0}
    call = 0
    while True:
        now = time.monotonic()
        budget = min(5.0, vend - now)
        if budget < 1.0:
            break
        nb = min(tries, key=lambda b: (tries[b], b))
        tries[nb] += 1
        best_n = state["best"][0]
        go = best_n // (2 * nb) + 1 + rng.randrange(3)
        call += 1
        try:
            n, e = _volt_run(d, D, seed * 7919 + call, nb, go, budget)
            consider(n, e)
        except Exception:
            pass


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    state = {"best": lib.haar_graph(d, range(d))}

    def consider(n, e):
        _consider(state, d, D, n, e)

    target = D >= 4 and d >= 5

    # D = 3 (non-calibration): projective planes for the few largest prime powers.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        for i, q in enumerate(pg_qs):
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            end_i = start + 0.3 * tl * (i + 1) / len(pg_qs)
            n2, e2 = _pipeline(pg_n, pg_e, d, D, end_i, rng)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q) and a saturated variant, grown by the pipeline.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
            consider(sat[0], sat[1])
            gq_end = start + (0.12 if target else 0.2) * tl
            first = True
            while time.monotonic() < gq_end:
                src = gq if first else rng.choice([gq, sat, state["best"]])
                first = False
                pn, pe = _pipeline(src[0], src[1], d, D, gq_end, rng)
                consider(pn, pe)

    if target:
        # Short Python lift pass, then the bold voltage search over semidirect lifts.
        _lift_loop(d, D, state, start + 0.2 * tl, rng, consider)
        _voltage_phase(d, D, seed, state, start + 0.87 * tl, rng, consider)
    else:
        _lift_loop(d, D, state, start + 0.85 * tl, rng, consider)

    best = state["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
