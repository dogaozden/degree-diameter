import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing for bi-Cayley graphs over the semidirect
# product G = Z_M x|_R Z_K (order N = M*K).
#
# Vertices are (0,x) -> x and (1,y) -> N+y. For a connection set S (|S| = DEG)
# the edges are (0,x)-(1,x*g) for g in S. Left multiplication by h is an
# automorphism that preserves both sides, so diameter <= DIAM holds iff every
# vertex is within DIAM of both (0,e) and (1,e). The cost is the number of
# vertices not reached from those two sources, so one eval is two BFS runs.
# Cost 0 means the graph is valid; the C program prints it and exits.
# ----------------------------------------------------------------------------

C_BICAYLEY = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1600
#define MAXD 32
#define MAXV (2 * MAXG)

static int N, K, M, R, DEG, DIAM;
static int *MT;
static int PW[MAXG + 1];
static int INV[MAXG];
static int S[MAXD], Sinv[MAXD], inS[MAXG];
static int dq[MAXV], qq[MAXV];
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

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    return ((a + PW[b] * c) % M) * K + (b + e) % K;
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    int pa = (int)(((long long)PW[nb] * a) % M);
    return ((M - pa) % M) * K + nb;
}

static int bfs_uncov(int s) {
    int V = 2 * N;
    for (int i = 0; i < V; i++) dq[i] = -1;
    int h = 0, t = 0;
    qq[t++] = s;
    dq[s] = 0;
    while (h < t) {
        int v = qq[h++];
        int dv = dq[v];
        if (dv >= DIAM) continue;
        if (v < N) {
            const int *row = MT + (size_t)v * N;
            for (int i = 0; i < DEG; i++) {
                int w = N + row[S[i]];
                if (dq[w] < 0) {
                    dq[w] = dv + 1;
                    qq[t++] = w;
                }
            }
        } else {
            const int *row = MT + (size_t)(v - N) * N;
            for (int i = 0; i < DEG; i++) {
                int w = row[Sinv[i]];
                if (dq[w] < 0) {
                    dq[w] = dv + 1;
                    qq[t++] = w;
                }
            }
        }
    }
    return V - t;
}

static int cost_of(void) { return bfs_uncov(0) + bfs_uncov(N); }

static void randomize_S(void) {
    for (int i = 0; i < DEG; i++) inS[S[i]] = 0;
    for (int i = 0; i < DEG; i++) {
        int g;
        do { g = rnd(N); } while (inS[g]);
        S[i] = g;
        inS[g] = 1;
        Sinv[i] = INV[g];
    }
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    R = atoi(argv[7]);
    if (K < 1 || M < 2) {
        printf("0 0\n");
        return 0;
    }
    N = K * M;
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || tl <= 0 || N > MAXG || DEG > N) {
        printf("0 0\n");
        return 0;
    }
    PW[0] = 1 % M;
    for (int b = 1; b < K; b++) PW[b] = (int)(((long long)PW[b - 1] * R) % M);
    if ((int)(((long long)PW[K - 1] * R) % M) != 1 % M) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    MT = (int *)malloc(sizeof(int) * (size_t)N * (size_t)N);
    if (!MT) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[(size_t)x * N + y] = gmul(x, y);
    for (int x = 0; x < N; x++) INV[x] = ginv(x);

    memset(inS, 0, sizeof inS);
    randomize_S();

    double tstart = (double)clock() / CLOCKS_PER_SEC;
    double frac = 0.0;
    int cur = cost_of();
    long stall = 0;
    long it = 0;
    const long STALL = 6000;

    while (cur > 0) {
        if ((it & 63) == 0) {
            frac = ((double)clock() / CLOCKS_PER_SEC - tstart) / tl;
            if (frac >= 1.0) break;
        }
        it++;
        int i = rnd(DEG);
        int g = rnd(N);
        if (inS[g]) continue;
        int old = S[i];
        inS[old] = 0;
        inS[g] = 1;
        S[i] = g;
        Sinv[i] = INV[g];
        int c2 = cost_of();
        double dl = (double)(c2 - cur);
        double T = 0.6 * (1.0 - frac) + 0.04;
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else {
            inS[g] = 0;
            inS[old] = 1;
            S[i] = old;
            Sinv[i] = INV[old];
        }
        if (++stall > STALL) {
            randomize_S();
            cur = cost_of();
            stall = 0;
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * N, N * DEG);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", x, N + MT[(size_t)x * N + S[i]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: generalized quadrangle, growth pipeline, glue.
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _twin_grow(n, edges, d, rng, deadline):
    """Add twins (same side, same neighbourhood) while all neighbours have spare degree."""
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
    """Hardest-first weighted set cover: rarely covered vertices weigh more."""
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


def _find_cover(cands, ball, n, full, d, rng, deadline):
    """Try weighted covers, then greedy covers."""
    B = _cand_matrix([ball[s] for s in cands], n)
    nrng = np.random.default_rng(rng.randrange(1 << 30))
    for attempt in range(8):
        if time.monotonic() >= deadline:
            return None
        chosen = _weighted_cover(B, cands, n, d, nrng, attempt > 0)
        if chosen:
            return chosen
    for attempt in range(30):
        if time.monotonic() >= deadline:
            return None
        chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
        if chosen:
            return chosen
    return None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods cover the deficient vertices within D-1."""
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
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
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
    """Extend by cover vertices, then saturate edges with the spare degree."""
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
# Bi-Cayley search over semidirect products Z_M x| Z_K (new main construction).
# ----------------------------------------------------------------------------

def _group_candidates(N, rng):
    """(K, M, R) triples with M*K = N and R^K = 1 mod M. Non-abelian ones come first."""
    if N > 1600 or N < 4:
        return []
    out = []
    for K in range(1, min(N, 48) + 1):
        if N % K:
            continue
        M = N // K
        if M < 2:
            continue
        if K == 1:
            out.append((1, M, 1))
            continue
        rl = [r for r in range(1, M)
              if math.gcd(r, M) == 1 and pow(r, K, M) == 1 % M]
        if not rl:
            continue
        rng.shuffle(rl)
        for r in rl[:6]:
            out.append((K, M, r))
    rng.shuffle(out)
    nonab = [c for c in out if c[0] > 1 and c[2] != 1]
    rest = [c for c in out if not (c[0] > 1 and c[2] != 1)]
    return nonab + rest


def _run_bicayley(d, D, seed, budget, K, M, R):
    """Run the bi-Cayley annealer; return (n, edges), or (0, []) if it found nothing."""
    out = lib.run_c(C_BICAYLEY, [d, D, seed, f"{budget:.2f}", K, M, R],
                    stdin_graph=None, timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def _bicayley_search(d, D, seed, rng, best_n, deadline, consider):
    """Search groups of order N = (best_n // 2) + 1 upward; each hit raises N by one."""
    N = max(best_n // 2 + 1, 2)
    attempt = 0
    while True:
        left = deadline - time.monotonic()
        if left < 1.5:
            break
        cands = _group_candidates(N, rng)[:40]
        if not cands:
            N += 1
            continue
        hit = False
        for K, M, R in cands:
            left = deadline - time.monotonic()
            if left < 1.5:
                break
            budget = min(6.0, max(1.5, left / 8.0), left - 0.6)
            if budget < 0.5:
                break
            attempt += 1
            try:
                n2, e2 = _run_bicayley(d, D, seed * 7919 + attempt, budget, K, M, R)
            except Exception:
                continue
            if n2 > 0 and consider(n2, e2):
                hit = True
                N = n2 // 2 + 1
                break
        if not hit and time.monotonic() >= deadline - 1.5:
            break


# ----------------------------------------------------------------------------
# Top level.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

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
            return True
        return False

    end = start + 0.85 * tl - 1.0

    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        for i, q in enumerate(pg_qs):
            pn, pe = lib.projective_plane_incidence(q)
            consider(pn, pe)
            pipe_end = start + (end - start) * 0.6 * (i + 1) / len(pg_qs)
            consider(*_pipeline(pn, pe, d, D, pipe_end, rng))

    elif D >= 4 and d >= 3:
        pipe_end = start + 0.22 * (end - start)
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
            consider(*sat)
            consider(*_pipeline(gq[0], gq[1], d, D, pipe_end, rng))
        # Main phase: bi-Cayley graphs over non-abelian groups of order just above best_n / 2.
        _bicayley_search(d, D, seed, rng, best_n, end, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
