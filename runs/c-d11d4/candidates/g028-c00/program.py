import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New bold construction for D = 4: abelian Haar graphs found by annealing.
#
# The Haar graph of an abelian group G = Z_a x Z_b with connection set S
# (|S| = d) is bipartite and d-regular on 2|G| vertices. Its diameter is at
# most 4 exactly when
#     S - S + S = G   (odd distances between the two sides), and
#     (S - S) + (S - S) = G   (even distances within a side).
# The C engine below searches for S of this kind for the largest |G| it can,
# ratcheting the group order upward. Groups of order m are tried as Z_a x Z_b
# for every factorisation m = a * b.
# ----------------------------------------------------------------------------

HAAR_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 2048
#define MAXD 16
#define MAXDD (MAXD * MAXD)
#define ITERS 200000

static int d, GA, GB, GM;
static int EI[MAXM], EJ[MAXM];
static int S[MAXD], negS[MAXD];
static int Dl[MAXDD];
static int nD;
static int stamp1[MAXM], stamp2[MAXM], stamp3[MAXM];
static int st1 = 0, st2 = 0, st3 = 0;
static int inS[MAXM];
static uint64_t rs = 1;
static double TL;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(nxt() % (uint64_t)k); }

static double rndd(void) { return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static void setgroup(int a, int b) {
    GA = a;
    GB = b;
    GM = a * b;
    for (int x = 0; x < GM; x++) {
        EI[x] = x / b;
        EJ[x] = x % b;
    }
}

static int gadd(int x, int y) {
    int i = EI[x] + EI[y];
    if (i >= GA) i -= GA;
    int j = EJ[x] + EJ[y];
    if (j >= GB) j -= GB;
    return i * GB + j;
}

static int gneg(int x) {
    int i = EI[x], j = EJ[x];
    return (i ? GA - i : 0) * GB + (j ? GB - j : 0);
}

/* Number of uncovered group elements. Zero iff both diameter conditions hold.
   The cheap condition S-S+S = G is checked first; the D+D condition is only
   counted once the first one is satisfied. */
static int cost_of(void) {
    for (int i = 0; i < d; i++) negS[i] = gneg(S[i]);
    st1++;
    nD = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int x = gadd(S[i], negS[j]);
            if (stamp1[x] != st1) {
                stamp1[x] = st1;
                Dl[nD++] = x;
            }
        }
    st3++;
    int c3 = 0;
    for (int a = 0; a < nD; a++)
        for (int i = 0; i < d; i++) {
            int y = gadd(Dl[a], S[i]);
            if (stamp3[y] != st3) {
                stamp3[y] = st3;
                c3++;
            }
        }
    int u3 = GM - c3;
    if (u3 > 0) return u3;
    st2++;
    int c2 = 0;
    for (int a = 0; a < nD; a++)
        for (int b = 0; b < nD; b++) {
            int y = gadd(Dl[a], Dl[b]);
            if (stamp2[y] != st2) {
                stamp2[y] = st2;
                c2++;
            }
        }
    return GM - c2;
}

/* Simulated annealing from a random S (0 fixed in S, by translation). Returns
   1 on success, 0 if the iteration budget ran out, -1 if the clock ran out. */
static int attempt(int iters) {
    memset(inS, 0, sizeof(int) * (size_t)GM);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int v;
        do {
            v = rndi(GM);
        } while (inS[v]);
        S[i] = v;
        inS[v] = 1;
    }
    int cur = cost_of();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now() > TL) return -1;
        double T = 2.0 * pow(0.05, (double)it / iters);
        int i = 1 + rndi(d - 1);
        int v = rndi(GM);
        if (inS[v]) continue;
        int old = S[i];
        S[i] = v;
        int c = cost_of();
        int delta = c - cur;
        if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[v] = 1;
            cur = c;
        } else {
            S[i] = old;
        }
    }
    return cur == 0 ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    unsigned long long seed = strtoull(argv[2], NULL, 10);
    TL = atof(argv[3]);
    int mlo = atoi(argv[4]), mhi = atoi(argv[5]);
    if (d < 2 || d > MAXD || mlo < 2) {
        printf("0 0 0\n");
        return 0;
    }
    if (mhi > MAXM - 1) mhi = MAXM - 1;
    rs = seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nxt();

    int bestM = 0, bestA = 1, bestB = 0;
    int bestS[MAXD];
    int m = mlo;
    while (m <= mhi && now() < TL) {
        int ca[64], cb[64], na = 0;
        for (int a = 1; a * a <= m && na < 64; a++)
            if (m % a == 0) {
                ca[na] = a;
                cb[na] = m / a;
                na++;
            }
        int found = 0;
        while (!found && now() < TL) {
            int ord[64];
            for (int k = 0; k < na; k++) ord[k] = k;
            for (int k = na - 1; k > 0; k--) {
                int j = rndi(k + 1);
                int t = ord[k];
                ord[k] = ord[j];
                ord[j] = t;
            }
            for (int k = 0; k < na && now() < TL; k++) {
                int idx = ord[k];
                setgroup(ca[idx], cb[idx]);
                int r = attempt(ITERS);
                if (r < 0) break;
                if (r == 1) {
                    found = 1;
                    bestM = m;
                    bestA = ca[idx];
                    bestB = cb[idx];
                    memcpy(bestS, S, sizeof(int) * (size_t)d);
                    break;
                }
            }
        }
        if (!found) break;
        m++;
    }
    if (bestM == 0) {
        printf("0 0 0\n");
        return 0;
    }
    printf("%d %d %d\n", bestM, bestA, bestB);
    for (int i = 0; i < d; i++) printf("%d ", bestS[i]);
    printf("\n");
    return 0;
}
"""


def _haar_abelian(a, b, S):
    """Haar graph of Z_a x Z_b (element x = (x // b, x % b)) with connection set S."""
    m = a * b

    def add(x, y):
        return ((x // b + y // b) % a) * b + (x % b + y % b) % b

    edges = [(x, m + add(x, s)) for x in range(m) for s in S]
    return 2 * m, edges


def _haar_search(d, seed, budget, mlo, mhi):
    """Run the C search; return (n, edges) of the Haar graph it found, or None."""
    out = lib.run_c(HAAR_C_SOURCE, [d, seed, f"{budget:.2f}", mlo, mhi],
                    stdin_graph=None, timeout=budget + 5.0)
    tok = out.split()
    if len(tok) < 3 + d:
        return None
    m, a, b = int(tok[0]), int(tok[1]), int(tok[2])
    if m <= 0 or a * b != m:
        return None
    S = [int(x) for x in tok[3:3 + d]]
    if len(set(S)) != d or any(not 0 <= s < m for s in S):
        return None
    return _haar_abelian(a, b, S)


# ----------------------------------------------------------------------------
# Python constructions: generalized quadrangle and growth pipeline (fallback).
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
    for attempt_i in range(12):
        if time.monotonic() >= deadline:
            return None
        chosen = _weighted_cover(B, cands, n, d, nrng, attempt_i > 0)
        if chosen:
            return chosen
    for attempt_i in range(60):
        if time.monotonic() >= deadline:
            return None
        chosen = _greedy_cover(cands, ball, full, d, rng, attempt_i > 0)
        if chosen:
            return chosen
    if time.monotonic() < deadline:
        return _local_cover(cands, ball, full, d, rng, 400, deadline)
    return None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
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
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
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


# ----------------------------------------------------------------------------
# Entry point.
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

    target = (D == 4 and d >= 5)

    # Stage 1: growth pipeline from projective planes (D = 3) or quadrangles (D >= 4).
    # This gives the safe fallback graph.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        t0 = time.monotonic()
        span = max(0.0, 0.5 * tl - (t0 - start))
        for i, q in enumerate(pg_qs):
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            slice_end = t0 + span * (i + 1) / len(pg_qs)
            n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
            consider(n2, e2)

    if D >= 4:
        pipe_end = start + (0.28 if target else 0.5) * tl
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

    # Stage 2 (target): abelian Haar graphs of diameter 4 via annealing over S.
    # Each found group order m gives a graph of order 2m; the search ratchets m upward
    # from just above the current best.
    if target:
        haar_end = start + 0.85 * tl - 2.0
        budget = haar_end - time.monotonic()
        if budget > 3.0:
            mlo = best_n // 2 + 1
            mhi = min(2047, d ** 3 - d * d + d)
            try:
                res = _haar_search(d, seed, budget, mlo, mhi)
                if res is not None:
                    consider(res[0], res[1])
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
