import itertools
import math
import random
import time

import numpy as np

import lib


# C engine: degree-preserving edge-swap annealing that adds vertices and
# repairs diameter violations. Every returned graph has zero bad pairs.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 4096
#define DMAX 64
#define WMAX 64

static int N, DEG, D;
static int deg_[NMAX];
static int nb[NMAX][DMAX];
static int side[NMAX];
static int L0[NMAX], L1[NMAX], n0cnt, n1cnt;
static uint64_t bufA[NMAX * WMAX], bufB[NMAX * WMAX];
static int bestN = 0, bestM = 0;
static int bside[NMAX];
static int bu[NMAX * DMAX / 2 + 8], bv[NMAX * DMAX / 2 + 8];
static int qbuf[NMAX];
static clock_t T0C;

static uint64_t rs = 0x2545F4914F6CDD1DULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0C) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D. */
static long cost(void) {
    int Wn = (N + 63) >> 6;
    uint64_t *A = bufA, *B = bufB;
    for (int v = 0; v < N; v++) {
        uint64_t *r = A + (size_t)v * WMAX;
        for (int w = 0; w < Wn; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < D; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *r = B + (size_t)v * WMAX;
            const uint64_t *s = A + (size_t)v * WMAX;
            for (int w = 0; w < Wn; w++) r[w] = s[w];
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *t = A + (size_t)nb[v][k] * WMAX;
                for (int w = 0; w < Wn; w++) r[w] |= t[w];
            }
        }
        uint64_t *tmp = A; A = B; B = tmp;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = A + (size_t)v * WMAX;
        int c = 0;
        for (int w = 0; w < Wn; w++) c += pc64(r[w]);
        unr += N - c;
    }
    return unr / 2;
}

static int isadj(int a, int b) {
    for (int k = 0; k < deg_[a]; k++) if (nb[a][k] == b) return 1;
    return 0;
}

static void add_e(int a, int b) {
    nb[a][deg_[a]++] = b;
    nb[b][deg_[b]++] = a;
}

static void del_from(int a, int b) {
    for (int k = 0; k < deg_[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][deg_[a] - 1];
            deg_[a]--;
            return;
        }
    }
}

static void rem_e(int a, int b) {
    del_from(a, b);
    del_from(b, a);
}

typedef struct { int op, a, b; } Op;
static Op logv[16];
static int nlog = 0;

static void LADD(int a, int b) {
    add_e(a, b);
    logv[nlog].op = 1; logv[nlog].a = a; logv[nlog].b = b; nlog++;
}

static void LREM(int a, int b) {
    rem_e(a, b);
    logv[nlog].op = 0; logv[nlog].a = a; logv[nlog].b = b; nlog++;
}

static void undo(void) {
    while (nlog > 0) {
        nlog--;
        if (logv[nlog].op == 1) rem_e(logv[nlog].a, logv[nlog].b);
        else add_e(logv[nlog].a, logv[nlog].b);
    }
}

static void rebuild_lists(void) {
    n0cnt = 0; n1cnt = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] == 0) L0[n0cnt++] = v;
        else L1[n1cnt++] = v;
    }
}

static int pick_edge(int *a, int *b) {
    if (n0cnt == 0) return 0;
    for (int t = 0; t < 50; t++) {
        int x = L0[rndi(n0cnt)];
        if (deg_[x] == 0) continue;
        *a = x;
        *b = nb[x][rndi(deg_[x])];
        return 1;
    }
    return 0;
}

/* One annealing move: degree-preserving swap, endpoint move, or edge addition. */
static void step(double T, long *cur, int *hit) {
    if (n0cnt == 0 || n1cnt == 0) return;
    nlog = 0;
    int mt = rndi(4), a1 = 0, b1 = 0, a2 = 0, b2 = 0;
    if (mt == 0) {
        if (!pick_edge(&a1, &b1) || !pick_edge(&a2, &b2)) return;
        if (a1 == a2 || b1 == b2) return;
        if (isadj(a1, b2) || isadj(a2, b1)) return;
        LREM(a1, b1); LREM(a2, b2); LADD(a1, b2); LADD(a2, b1);
    } else if (mt == 1) {
        if (!pick_edge(&a1, &b1)) return;
        int x = -1;
        for (int t = 0; t < 30; t++) {
            int c = L0[rndi(n0cnt)];
            if (c != a1 && deg_[c] < DEG && !isadj(c, b1)) { x = c; break; }
        }
        if (x < 0) return;
        LREM(a1, b1); LADD(x, b1);
    } else if (mt == 2) {
        if (!pick_edge(&a1, &b1)) return;
        int y = -1;
        for (int t = 0; t < 30; t++) {
            int c = L1[rndi(n1cnt)];
            if (c != b1 && deg_[c] < DEG && !isadj(a1, c)) { y = c; break; }
        }
        if (y < 0) return;
        LREM(a1, b1); LADD(a1, y);
    } else {
        int x = -1, y = -1;
        for (int t = 0; t < 30; t++) {
            int c = L0[rndi(n0cnt)];
            if (deg_[c] < DEG) { x = c; break; }
        }
        for (int t = 0; t < 30; t++) {
            int c = L1[rndi(n1cnt)];
            if (deg_[c] < DEG) { y = c; break; }
        }
        if (x < 0 || y < 0 || isadj(x, y)) return;
        LADD(x, y);
    }
    long nc = cost();
    long delta = nc - *cur;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        *cur = nc;
        if (nc == 0) *hit = 1;
    } else {
        undo();
    }
}

/* Append one vertex on a random side, joined to up to DEG spare opposite-side vertices. */
static void grow(void) {
    int c = rndi(2);
    int v = N;
    N++;
    side[v] = c;
    deg_[v] = 0;
    static int cand[NMAX];
    int nc = 0;
    for (int u = 0; u < v; u++) if (side[u] != c && deg_[u] < DEG) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int take = nc < DEG ? nc : DEG;
    for (int i = 0; i < take; i++) add_e(v, cand[i]);
    rebuild_lists();
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int v = 0; v < N; v++) {
        bside[v] = side[v];
        for (int k = 0; k < deg_[v]; k++) {
            int u = nb[v][k];
            if (v < u) { bu[bestM] = v; bv[bestM] = u; bestM++; }
        }
    }
}

static void restore_best(void) {
    N = bestN;
    for (int v = 0; v < N; v++) { deg_[v] = 0; side[v] = bside[v]; }
    for (int i = 0; i < bestM; i++) add_e(bu[i], bv[i]);
    rebuild_lists();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    T0C = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > NMAX - 800 ||
        DEG < 1 || DEG > DMAX || D < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) deg_[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (isadj(u, v) || deg_[u] >= DEG || deg_[v] >= DEG) continue;
        add_e(u, v);
    }

    /* Bipartition by BFS; fail safe if the input is not bipartite. */
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int k = 0; k < deg_[u]; k++) {
                int w = nb[u][k];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    qbuf[qt++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    rebuild_lists();

    long cur = cost();
    int phaseL = 1500;
    while (elapsed() < tl) {
        if (cur == 0) {
            if (N > bestN) save_best();
            grow();
            cur = cost();
        }
        int hit = 0;
        for (int it = 0; it < phaseL && !hit && elapsed() < tl; it++) {
            double fr = (double)it / phaseL;
            double T = 1.0 * (1.0 - fr) + 0.15 * fr;
            step(T, &cur, &hit);
        }
        if (!hit && bestN > 0) {
            restore_best();
            cur = 0;
        }
    }
    if (cur == 0 && N > bestN) save_best();
    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q), order 2(q+1)(q^2+1)."""
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


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Growth helpers (valid-by-construction additions using spare degree)
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
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
    nb = (n + 7) // 8
    buf = b"".join(x.to_bytes(nb, "little") for x in cand_balls)
    arr = np.frombuffer(buf, dtype=np.uint8).reshape(len(cand_balls), nb)
    return np.unpackbits(arr, axis=1, bitorder="little")[:, :n].astype(bool)


def _weighted_cover(B, cand_ids, n, d, nrng, randomize):
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Append whole vertices whose neighbourhoods cover all vertices, using spare degree only."""
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


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth, cover growth and edge saturation until nothing changes."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage-lift families (used when no generalized quadrangle applies)
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
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


def _lift_loop(d, D, best_n, deadline, rng, consider):
    group_p = 0.3
    haar_p = 0.2 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0
    cur_best = best_n
    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = cur_best // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                cur_best = max(cur_best, res[0])
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
                cur_best = max(cur_best, n)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], cur_best // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                cur_best = max(cur_best, res[0])
                ladder[k] = m + 1
            else:
                ladder[k] = m


# ----------------------------------------------------------------------------
# C annealing stage: grow the best graph and repair diameter violations.
# ----------------------------------------------------------------------------

def _c_anneal(n, edges, d, D, start, time_limit, seed):
    end_c = start + 0.85 * time_limit
    now = time.monotonic()
    budget = end_c - now - 2.0
    if budget < 1.0 or n < 2:
        return None
    timeout = max(budget + 2.0, start + 0.95 * time_limit - now)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed % 100000 + 1, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=timeout)
        return lib.parse_graph_text(out)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Seeds: projective plane for D = 3, generalized quadrangle for D >= 4.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    gq = _best_gq(d) if D >= 4 else None
    if gq is not None:
        consider(gq[0], gq[1])
        grow_end = start + 0.22 * time_limit
        while time.monotonic() < grow_end:
            pn, pe = _pipeline(gq[0], gq[1], d, D, grow_end, rng)
            consider(pn, pe)
            if pn == gq[0]:
                break
    else:
        _lift_loop(d, D, best_n, start + 0.22 * time_limit, rng, consider)

    # Calibration: already at the Moore bound, so nothing can improve.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Bold stage: C annealing from the best graph found so far.
    res = _c_anneal(best_n, best[1], d, D, start, time_limit, seed)
    if res is not None:
        consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
