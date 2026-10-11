import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on voltage lifts of a bipartite base graph
# over the group G = Z_m x| Z_k2 (element (a, b) is coded a*k2 + b).
#
# Lift: base has K vertices per side and DEG perfect matchings' worth of darts
# (dart (i, perm_p(i)) for each p). Dart j with voltage g joins (A,i,x) to
# (B,perm(i), x*g) for all x in G. Every vertex has degree DEG.
#
# Left multiplication by G is an automorphism of the lift, and it is transitive
# on each fibre, so the diameter is <= DIAM iff every one of the 2K fibre
# representatives reaches all vertices within DIAM steps. The cost is the
# total number of unreached (source, vertex) pairs, plus a penalty for parallel
# darts with equal voltage (which would create duplicate edges). Cost 0 means
# a valid graph; the engine prints it and stops.
#
# argv: DEG DIAM seed time m k2 r K
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 2048
#define MAXK 4
#define MAXD 40
#define MAXDART (MAXK * MAXD)
#define MAXNV (2 * MAXK * MAXG)
#define PENALTY 30
#define STALL_LIMIT 4000

static int G, K, DEG, DIAM, NDART, NV;
static int mulT[MAXG * MAXG];
static int invT[MAXG];
static int dA[MAXDART], dB[MAXDART], gv[MAXDART];
static int Aadj[MAXK][MAXD], Badj[MAXK][MAXD];
static int perm[MAXD][MAXK], invp[MAXD][MAXK];
static int stampArr[MAXNV], distArr[MAXNV], qbuf[MAXNV];
static int stampCur = 0;
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

static void shuffle_arr(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static void build_group(int m, int k2, int r) {
    long long pw[64];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (pw[b - 1] * r) % m;
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, d = y % k2;
            long long aa = ((long long)a + pw[b] * c) % m;
            int bb = (b + d) % k2;
            mulT[x * G + y] = (int)(aa * k2 + bb);
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mulT[x * G + y] == 0) {
                invT[x] = y;
                break;
            }
}

static void init_structure(void) {
    NDART = DEG * K;
    NV = 2 * K * G;
    for (int p = 0; p < DEG; p++) {
        for (int i = 0; i < K; i++) perm[p][i] = i;
        if (p > 0) shuffle_arr(perm[p], K);
        for (int i = 0; i < K; i++) invp[p][perm[p][i]] = i;
    }
    for (int p = 0; p < DEG; p++)
        for (int i = 0; i < K; i++) {
            int j = p * K + i;
            dA[j] = i;
            dB[j] = perm[p][i];
            Aadj[i][p] = j;
        }
    for (int b = 0; b < K; b++)
        for (int p = 0; p < DEG; p++)
            Badj[b][p] = p * K + invp[p][b];
}

/* Vertex id = base * G + x, base < K is side A, base in [K, 2K) is side B. */
static long long eval_cost(void) {
    long long cost = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = s * G;
        stampCur++;
        int qh = 0, qt = 0;
        qbuf[qt++] = src;
        stampArr[src] = stampCur;
        distArr[src] = 0;
        while (qh < qt) {
            int u = qbuf[qh++];
            int du = distArr[u];
            if (du >= DIAM) continue;
            int base = u / G;
            int x = u - base * G;
            if (base < K) {
                for (int p = 0; p < DEG; p++) {
                    int j = Aadj[base][p];
                    int v = (K + dB[j]) * G + mulT[x * G + gv[j]];
                    if (stampArr[v] != stampCur) {
                        stampArr[v] = stampCur;
                        distArr[v] = du + 1;
                        qbuf[qt++] = v;
                    }
                }
            } else {
                int b = base - K;
                for (int p = 0; p < DEG; p++) {
                    int j = Badj[b][p];
                    int v = dA[j] * G + mulT[x * G + invT[gv[j]]];
                    if (stampArr[v] != stampCur) {
                        stampArr[v] = stampCur;
                        distArr[v] = du + 1;
                        qbuf[qt++] = v;
                    }
                }
            }
        }
        cost += NV - qt;
    }
    for (int i = 0; i < NDART; i++)
        for (int j = i + 1; j < NDART; j++)
            if (dA[i] == dA[j] && dB[i] == dB[j] && gv[i] == gv[j])
                cost += PENALTY;
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int m = atoi(argv[5]);
    int k2 = atoi(argv[6]);
    int r = atoi(argv[7]);
    K = atoi(argv[8]);
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || K < 1 || K > MAXK ||
        m < 2 || k2 < 1 || k2 > 63 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    if (G < 2 || G > MAXG) {
        printf("0 0\n");
        return 0;
    }
    r %= m;
    long long pw = 1 % m;
    for (int i = 0; i < k2; i++) pw = (pw * r) % m;
    if (pw != 1 % m) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 4242ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    build_group(m, k2, r);
    init_structure();
    for (int j = 0; j < NDART; j++) gv[j] = rnd(G);

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long long cur = eval_cost();
    long long bestc = cur;
    long stall = 0;
    double frac = 0.0;
    long iter = 0;
    while (cur > 0) {
        if ((iter & 7) == 0) {
            frac = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
            if (frac >= 1.0) break;
        }
        iter++;
        double T = 1.5 * (1.0 - frac) + 0.15;
        int j = rnd(NDART);
        int old = gv[j];
        int nw = rnd(G - 1);
        if (nw >= old) nw++;
        gv[j] = nw;
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else {
            gv[j] = old;
        }
        if (cur < bestc) {
            bestc = cur;
            stall = 0;
        } else if (++stall > STALL_LIMIT) {
            for (int q2 = 0; q2 < NDART; q2++) gv[q2] = rnd(G);
            cur = eval_cost();
            bestc = cur;
            stall = 0;
        }
    }

    if (cur == 0) {
        long long ne = (long long)K * G * DEG;
        printf("%d %lld\n", NV, ne);
        for (int a = 0; a < K; a++)
            for (int x = 0; x < G; x++)
                for (int p = 0; p < DEG; p++) {
                    int j = Aadj[a][p];
                    int u = a * G + x;
                    int v = (K + dB[j]) * G + mulT[x * G + gv[j]];
                    printf("%d %d\n", u, v);
                }
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


def _group_options(G, rng, cap=12):
    """Return (m, k2, r) triples with m * k2 = G giving Z_m x| Z_k2 (r^k2 = 1 mod m)."""
    opts = []
    for k2 in range(1, min(G, 40) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:cap]:
            opts.append((m, k2, r))
    return opts


def _lift_attempt(d, D, k, G, rng, budget, seed):
    """Run the C lift annealer on a random group of order G with k base vertices per side."""
    opts = _group_options(G, rng)
    if not opts:
        return None
    m, k2, r = rng.choice(opts)
    out = lib.run_c(LIFT_C, [d, D, seed, f"{budget:.2f}", m, k2, r, k],
                    stdin_graph=None, timeout=budget + 3.0)
    n, e = lib.parse_graph_text(out)
    if n > 0 and lib.is_valid(n, e, d, D):
        return n, e
    return None


# ----------------------------------------------------------------------------
# Twin extension: a twin v of x (same side, N(v) = N(x)) keeps old distances,
# has dist(v, x) = 2, and preserves bipartiteness.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Cover-based vertex extension.
# ----------------------------------------------------------------------------

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
    """Alternate twin growth and cover growth until neither adds a vertex.

    Every step keeps diameter <= D and bipartiteness.
    """
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


# ----------------------------------------------------------------------------
# Driver.
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

    # D = 3 (non-calibration): projective planes and growth.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        t0 = time.monotonic()
        span = 0.25 * tl
        for i, q in enumerate(pg_qs):
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            slice_end = t0 + span * (i + 1) / len(pg_qs)
            n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q) and a saturated variant, grown by the pipeline.
    if D >= 4:
        pipe_end = start + 0.3 * tl
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
            consider(sat[0], sat[1])
            first = True
            while time.monotonic() < pipe_end:
                src = gq if first else rng.choice([gq, sat, best])
                first = False
                pn, pe = _pipeline(src[0], src[1], d, D, pipe_end, rng)
                consider(pn, pe)

    # Main stage: voltage lifts over small non-abelian groups, annealed in C.
    # Target order: the smallest 2*k*G beating the current best.
    lift_end = start + 0.88 * tl - 1.0
    attempt = 0
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = 1 if rng.random() < 0.7 else 2
        G = max(2, best_n // (2 * k) + 1)
        if G > 2048:
            break
        budget = min(8.0, max(2.0, 0.3 * remaining), remaining)
        attempt += 1
        try:
            res = _lift_attempt(d, D, k, G, rng, budget, seed * 7919 + attempt)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
