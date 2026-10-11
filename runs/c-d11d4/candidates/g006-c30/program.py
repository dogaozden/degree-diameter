import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: keeps a valid graph and only ever changes it by moves that were
# checked for diameter <= D. Moves:
#   exchange: delete a random edge, then try to insert a vertex whose
#             neighbourhood covers all vertices within D-1 (randomised greedy
#             covers); accept only if the whole graph is valid again.
#   swap:     move one edge end (a,b) -> (a,c) to shift spare degree; accept
#             only if the graph stays valid (plateau walk).
#   saturate: add edges between deficient opposite-side vertices (never breaks
#             validity).
# Reachability is held in bitsets, one level per distance.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd() % (u64)k); }

static int pc64(u64 x) {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_popcountll(x);
#else
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
#endif
}

static int DM, DIAM, CAP, W, N;
static int *nb, *deg, *col, *cand, *chosen, *gains, *defl, *defr;
static u64 *lev, *unc;

static u64 *LV(int i, int v) {
    return lev + ((size_t)i * (size_t)CAP + (size_t)v) * (size_t)W;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (nb[a * DM + k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    nb[a * DM + deg[a]++] = b;
    nb[b * DM + deg[b]++] = a;
}

static void del_one(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a * DM + k] == b) {
            nb[a * DM + k] = nb[a * DM + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
}

static void compute_levels(void) {
    for (int v = 0; v < N; v++) {
        u64 *p = LV(0, v);
        memset(p, 0, sizeof(u64) * (size_t)W);
        p[v >> 6] |= 1ULL << (v & 63);
    }
    for (int i = 0; i < DIAM; i++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = LV(i + 1, v);
            memcpy(dst, LV(i, v), sizeof(u64) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *s = LV(i, nb[v * DM + k]);
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
    }
}

/* Valid iff every ball of radius DIAM is the whole vertex set. */
static int is_full(void) {
    for (int v = 0; v < N; v++) {
        const u64 *p = LV(DIAM, v);
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(p[w]);
        if (c != N) return 0;
    }
    return 1;
}

/* Greedy cover of all N vertices by balls of radius DIAM-1 of candidates.
   Returns number of chosen vertices (written to out), or -1 on failure. */
static int cover(const int *cd, int ncd, int randomize, int *out) {
    for (int w = 0; w < W; w++) unc[w] = 0;
    for (int v = 0; v < N; v++) unc[v >> 6] |= 1ULL << (v & 63);
    int cnt = 0;
    for (;;) {
        int left = 0;
        for (int w = 0; w < W; w++) {
            if (unc[w]) { left = 1; break; }
        }
        if (!left) return cnt;
        if (cnt >= DM) return -1;
        int best = 0;
        for (int j = 0; j < ncd; j++) {
            const u64 *bl = LV(DIAM - 1, cd[j]);
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(bl[w] & unc[w]);
            gains[j] = g;
            if (g > best) best = g;
        }
        if (best == 0) return -1;
        int thr = best;
        if (randomize && best > 1 && rndi(3) == 0) thr = best - 1;
        int pick = -1, seen = 0;
        for (int j = 0; j < ncd; j++) {
            if (gains[j] >= thr && gains[j] > 0) {
                seen++;
                if (rndi(seen) == 0) pick = j;
            }
        }
        if (pick < 0) return -1;
        out[cnt++] = cd[pick];
        const u64 *bl = LV(DIAM - 1, cd[pick]);
        for (int w = 0; w < W; w++) unc[w] &= ~bl[w];
    }
}

static void saturate(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DM) {
            if (col[v] == 0) defl[nl++] = v;
            else defr[nr++] = v;
        }
    }
    for (int i = 0; i < nl; i++) {
        int a = defl[i];
        for (int j = 0; j < nr && deg[a] < DM; j++) {
            int b = defr[j];
            if (deg[b] < DM && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Exchange augmentation. Returns 1 if a vertex was added (graph stays valid). */
static int try_exchange(int attempts) {
    int a = rndi(N);
    if (deg[a] == 0) return 0;
    int b = nb[a * DM + rndi(deg[a])];
    remove_edge(a, b);
    compute_levels();
    int added = 0;
    int first = rndi(2);
    for (int oi = 0; oi < 2 && !added; oi++) {
        int nc = (oi == 0) ? first : 1 - first;
        int nca = 0;
        for (int v = 0; v < N; v++)
            if (col[v] == nc && deg[v] < DM) cand[nca++] = v;
        if (nca == 0) continue;
        for (int t = 0; t < attempts && !added; t++) {
            int k = cover(cand, nca, t > 0, chosen);
            if (k <= 0 || N >= CAP) continue;
            int v = N;
            N++;
            col[v] = 1 - nc;
            deg[v] = 0;
            for (int i = 0; i < k; i++) add_edge(v, chosen[i]);
            compute_levels();
            if (is_full()) {
                added = 1;
            } else {
                for (int i = 0; i < k; i++) remove_edge(v, chosen[i]);
                N--;
                compute_levels();
            }
        }
    }
    if (!added) add_edge(a, b);
    return added;
}

/* Plateau move: (a,b) -> (a,c) with c on b's side; keep only if still valid. */
static void try_swap(void) {
    int a = rndi(N);
    if (deg[a] == 0) return;
    int b = nb[a * DM + rndi(deg[a])];
    int c = -1;
    for (int tries = 0; tries < 30; tries++) {
        int x = rndi(N);
        if (x != b && col[x] == col[b] && deg[x] < DM && !has_edge(a, x)) {
            c = x;
            break;
        }
    }
    if (c < 0) return;
    remove_edge(a, b);
    add_edge(a, c);
    compute_levels();
    if (!is_full()) {
        remove_edge(a, c);
        add_edge(a, b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DM = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || DM < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    CAP = n0 + 4000;
    W = (CAP + 63) / 64;
    nb = calloc((size_t)CAP * (size_t)DM, sizeof(int));
    deg = calloc((size_t)CAP, sizeof(int));
    col = calloc((size_t)CAP, sizeof(int));
    cand = calloc((size_t)CAP, sizeof(int));
    gains = calloc((size_t)CAP, sizeof(int));
    defl = calloc((size_t)CAP, sizeof(int));
    defr = calloc((size_t)CAP, sizeof(int));
    chosen = calloc((size_t)DM + 1, sizeof(int));
    lev = calloc((size_t)(DIAM + 1) * (size_t)CAP * (size_t)W, sizeof(u64));
    unc = calloc((size_t)W, sizeof(u64));
    if (!nb || !deg || !col || !cand || !gains || !defl || !defr || !chosen || !lev || !unc) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (has_edge(u, v) || deg[u] >= DM || deg[v] >= DM) continue;
        add_edge(u, v);
    }

    /* 2-colour the input (it is bipartite if the caller passed a valid graph). */
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        cand[sp++] = s;
        while (sp) {
            int u = cand[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int x = nb[u * DM + k];
                if (col[x] == -1) {
                    col[x] = 1 - col[u];
                    cand[sp++] = x;
                }
            }
        }
    }

    clock_t t0 = clock();
    saturate();
    compute_levels();
    for (;;) {
        double el = (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
        if (el >= tl) break;
        if (rndi(10) < 7) {
            if (try_exchange(2)) saturate();
        } else {
            try_swap();
        }
    }

    long M = 0;
    for (int v = 0; v < N; v++) M += deg[v];
    M /= 2;
    printf("%d %ld\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v * DM + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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


# ----------------------------------------------------------------------------
# Twin extension. A twin v of x (same side, N(v) = N(x)) keeps all old distances,
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
    """Hardest-first weighted set cover: rare uncovered vertices get larger weight."""
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
    """Try weighted covers (deterministic, then randomised), then greedy, then swaps."""
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


# ----------------------------------------------------------------------------
# Voltage lifts over non-cyclic groups (semidirect products) and Haar graphs.
# ----------------------------------------------------------------------------

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


def _lift_phase(d, D, best, rng, deadline):
    """Lift / Haar / group search for cases without a generalized-quadrangle start."""
    state = [best]

    def consider(n, e):
        if n > state[0][0] and lib.is_valid(n, e, d, D):
            state[0] = (n, e)

    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        best_n = state[0][0]
        r = rng.random()
        if r < 0.3:
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
        elif rng.random() < 0.15 and haar_miss < 4:
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
    return state[0]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.86 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Stage 1: constructions plus the twin / cover pipeline.
    pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3] if D == 3 else []
    gq = _best_gq(d) if D >= 4 else None

    if pg_qs:
        t0 = time.monotonic()
        stage_end = start + 0.4 * time_limit
        span = max(0.0, stage_end - t0)
        for i, q in enumerate(pg_qs):
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            slice_end = t0 + span * (i + 1) / len(pg_qs)
            n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
            consider(n2, e2)
    elif gq is not None:
        consider(gq[0], gq[1])
        stage_end = start + 0.38 * time_limit
        while time.monotonic() < stage_end:
            pn, pe = _pipeline(gq[0], gq[1], d, D, stage_end, rng)
            consider(pn, pe)
    else:
        best = _lift_phase(d, D, best, rng, start + 0.45 * time_limit)

    # Stage 2: C plateau / exchange search from the best graph found so far.
    remaining = end - time.monotonic()
    budget = remaining - 2.0
    if d >= 2 and best[0] >= 2 and budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 15.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
