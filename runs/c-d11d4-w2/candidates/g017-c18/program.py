import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New construction for D = 4: bi-Cayley graphs over small groups.
#
# Let G = Z_m x| Z_k (element (a, b) coded as a*k + b). Pick S of size d in G and
# join a_g to b_{g s} for each s in S. Every vertex has degree d, the graph is
# bipartite, and left multiplication is an automorphism, so only distances from
# a_1 and b_1 matter:
#   a-side: G = {1} u P2 u P4, where P2 = S S^{-1}, P4 = P2 P2
#   b-side: G = S u (P2 S)
# A simulated annealer over S (move: replace one element) drives the uncovered
# count to zero. Each success gives a valid graph on 2|G| vertices.
# ----------------------------------------------------------------------------

BICAY_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXG 2048

static int NG, MM, KK, DD;
static int PW[MAXG];
static int IV[MAXG];
static int MT[MAXG * MAXG];
static int markA[MAXG], markB[MAXG];
static int stA = 0, stB = 0;
static int S[MAXD], bestS[MAXD];
static int P2[MAXD * MAXD];
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

static int mul_raw(int x, int y) {
    int a = x / KK, b = x % KK;
    int c = y / KK, e = y % KK;
    long long t = (long long)a + (long long)PW[b] * (long long)c;
    int a2 = (int)(t % MM);
    int b2 = (b + e) % KK;
    return a2 * KK + b2;
}

static int inv_raw(int x) {
    int a = x / KK, b = x % KK;
    int nb = (KK - b) % KK;
    long long t = -((long long)PW[nb] * (long long)a) % MM;
    if (t < 0) t += MM;
    return (int)t * KK + nb;
}

static int in_set(int g, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == g) return 1;
    return 0;
}

/* Number of uncovered elements on the a-side plus on the b-side. */
static int cost(void) {
    int np = 0;
    for (int i = 0; i < DD; i++)
        for (int j = 0; j < DD; j++)
            P2[np++] = MT[S[i] * NG + IV[S[j]]];

    stA++;
    int ca = 1;
    markA[0] = stA;
    for (int i = 0; i < np; i++) {
        int p = P2[i];
        if (markA[p] != stA) { markA[p] = stA; ca++; }
    }
    for (int i = 0; i < np; i++) {
        const int *row = MT + (size_t)P2[i] * NG;
        for (int j = 0; j < np; j++) {
            int x = row[P2[j]];
            if (markA[x] != stA) { markA[x] = stA; ca++; }
        }
    }

    stB++;
    int cb = 0;
    for (int i = 0; i < DD; i++) {
        if (markB[S[i]] != stB) { markB[S[i]] = stB; cb++; }
    }
    for (int i = 0; i < np; i++) {
        const int *row = MT + (size_t)P2[i] * NG;
        for (int j = 0; j < DD; j++) {
            int x = row[S[j]];
            if (markB[x] != stB) { markB[x] = stB; cb++; }
        }
    }
    return (NG - ca) + (NG - cb);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DD = atoi(argv[1]);
    MM = atoi(argv[2]);
    KK = atoi(argv[3]);
    long long r = atoll(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    double tl = atof(argv[6]);
    if (DD < 1 || DD > MAXD || MM < 1 || KK < 1 || (long long)MM * KK > MAXG || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    NG = MM * KK;
    if (NG < DD + 1) {
        printf("0 0\n");
        return 0;
    }
    long long rr = ((r % MM) + MM) % MM;
    PW[0] = 1 % MM;
    for (int b = 1; b < KK; b++)
        PW[b] = (int)((long long)PW[b - 1] * rr % MM);
    if (KK > 1 && (((long long)PW[KK - 1] * rr) % MM) != 1 % MM) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < NG; x++)
        for (int y = 0; y < NG; y++)
            MT[(size_t)x * NG + y] = mul_raw(x, y);
    for (int x = 0; x < NG; x++) {
        IV[x] = inv_raw(x);
        if (MT[(size_t)x * NG + IV[x]] != 0) {
            printf("0 0\n");
            return 0;
        }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    for (int i = 0; i < DD; i++) {
        int g;
        do { g = rnd(NG); } while (in_set(g, i));
        S[i] = g;
    }
    int c = cost();
    int bestc = c;
    memcpy(bestS, S, sizeof S);

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;
    const long stallLim = 4000;
    while (bestc > 0) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
        if (frac >= 1.0) break;
        int i = rnd(DD);
        int g = rnd(NG);
        if (in_set(g, DD)) continue;
        int old = S[i];
        S[i] = g;
        int c2 = cost();
        double dl = (double)(c2 - c);
        double T = 0.5 + 1.5 * (1.0 - frac);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            c = c2;
            if (c < bestc) {
                bestc = c;
                memcpy(bestS, S, sizeof S);
                stall = 0;
            } else {
                stall++;
            }
        } else {
            S[i] = old;
            stall++;
        }
        if (stall > stallLim) {
            for (int j = 0; j < DD; j++) {
                int h;
                do { h = rnd(NG); } while (in_set(h, j));
                S[j] = h;
            }
            c = cost();
            if (c < bestc) {
                bestc = c;
                memcpy(bestS, S, sizeof S);
            }
            stall = 0;
        }
    }

    if (bestc != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * NG, NG * DD);
    for (int g = 0; g < NG; g++)
        for (int i = 0; i < DD; i++)
            printf("%d %d\n", g, NG + MT[(size_t)g * NG + bestS[i]]);
    return 0;
}
"""


def _bicay_candidates(N, rng):
    """Groups Z_m x| Z_k of order N as (m, k, r) triples, in random order."""
    out = []
    for k in range(1, min(N, 60) + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            out.append((m, 1, 1))
            continue
        if m < 2:
            continue
        rs_ = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        for r in rng.sample(rs_, min(3, len(rs_))):
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _bicay_stage(d, best_n, rng, deadline, consider):
    """Search bi-Cayley graphs of order 2N for N = best_n/2 + 1, +2, ... until the deadline."""
    N = best_n // 2 + 1
    cap = min(lib.moore_bound(d, 4) // 2, 1000)
    while N <= cap and time.monotonic() < deadline - 0.3:
        for (m, k, r) in _bicay_candidates(N, rng)[:4]:
            budget = min(1.0, deadline - time.monotonic())
            if budget < 0.3:
                break
            try:
                out = lib.run_c(BICAY_SOURCE,
                                [d, m, k, r, rng.randrange(1 << 30), f"{budget:.2f}"],
                                timeout=budget + 3.0)
                n, e = lib.parse_graph_text(out)
            except Exception:
                continue
            if n > 0 and lib.is_valid(n, e, d, 4):
                consider(n, e)
                break
        N += 1


# ----------------------------------------------------------------------------
# Python constructions and glue (carried over from the parent).
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


# ----------------------------------------------------------------------------
# Build.
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
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Time plan. D = 4 with d >= 5 (the target) uses the bi-Cayley stage.
    bicay = D == 4 and d >= 5
    if bicay:
        pipe_end = start + 0.20 * tl
        bic_end = start + 0.70 * tl
        deadline = start + 0.85 * tl
    else:
        pipe_end = start + 0.5 * tl
        deadline = start + 0.85 * tl

    # D = 3 (non-calibration): projective planes for the few largest prime powers q with q + 1 <= d.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        t0 = time.monotonic()
        span = max(0.0, 0.3 * (deadline - t0))
        for i, q in enumerate(pg_qs):
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            slice_end = t0 + span * (i + 1) / len(pg_qs)
            n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q) and a saturated variant with spare degree filled.
    sat = None
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
            consider(sat[0], sat[1])
            first = True
            while time.monotonic() < pipe_end:
                if first:
                    src = gq
                else:
                    src = rng.choice([gq, sat, best])
                first = False
                pn, pe = _pipeline(src[0], src[1], d, D, pipe_end, rng)
                consider(pn, pe)

    # New stage: bi-Cayley graphs over Z_m x| Z_k of order N, growing N while feasible.
    if bicay:
        _bicay_stage(d, best_n, rng, bic_end, consider)

    # Main search: non-cyclic group lifts, Haar and cyclic lifts.
    group_p = 0.85 if D >= 5 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
